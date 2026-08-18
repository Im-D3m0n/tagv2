/* ==========================================================
   TAGGED — a side-view platformer tag game
   - Local 2-player (same keyboard): P1 = WASD, P2 = Arrow keys
   - Online multiplayer across devices via Supabase Realtime
     (Broadcast + Presence channels). Host is authoritative:
     simulates physics, buffs, portals, and tagging; broadcasts
     state. Clients send input. Needs a free Supabase project's
     URL + anon key in config.js.
   - Buffs (speed / jump / shield) and linked teleport portals.
   - Platform layout is generated tier-by-tier so every platform
     is guaranteed reachable from the one below it by a normal jump.
   ========================================================== */

const COLORS = ["#5de4c7", "#ffd166", "#c792ea", "#82aaff", "#ff8fa3", "#a3f7bf"];
const PLAYER_W = 18;
const PLAYER_H = 26;
const TAG_DISTANCE = 22;
const TAG_COOLDOWN_MS = 1500;
const GAME_DURATION_MS = 2 * 60 * 1000;
const MOVE_SPEED = 230;       // px/sec horizontal
const GRAVITY = 1400;         // px/sec^2
const JUMP_VELOCITY = -560;   // px/sec (negative = up)
const MAX_FALL_SPEED = 900;
const NETWORK_TICK_MS = 50;   // 20Hz state broadcast

// derived jump reach, used to keep the generated map fully climbable
const JUMP_TIME_TO_APEX = -JUMP_VELOCITY / GRAVITY;             // s
const JUMP_MAX_HEIGHT = 0.5 * -JUMP_VELOCITY * JUMP_TIME_TO_APEX; // px
const JUMP_MAX_HORIZONTAL = MOVE_SPEED * JUMP_TIME_TO_APEX * 2;  // px (up+down)
const SAFE_VERTICAL_REACH = JUMP_MAX_HEIGHT * 0.8;   // margin below max
const SAFE_HORIZONTAL_REACH = JUMP_MAX_HORIZONTAL * 0.75;

const BUFF_TYPES = ["speed", "jump", "shield"];
const BUFF_RADIUS = 15;
const BUFF_COUNT = 4;
const BUFF_RESPAWN_MS = 9000;
const BUFF_DURATION_MS = 6000;
const BUFF_SPEED_MULT = 1.6;
const BUFF_JUMP_MULT = 1.3;

const PORTAL_RADIUS = 18;
const PORTAL_COOLDOWN_MS = 700;

const $ = (id) => document.getElementById(id);

const screens = {
  menu: $("screen-menu"),
  host: $("screen-host"),
  join: $("screen-join"),
  game: $("screen-game"),
  gameover: $("screen-gameover"),
};

function showScreen(name) {
  Object.values(screens).forEach((s) => s.classList.add("hidden"));
  screens[name].classList.remove("hidden");
}

document.querySelectorAll("[data-back]").forEach((btn) => {
  btn.addEventListener("click", () => {
    teardownNetwork();
    showScreen("menu");
  });
});

/* ----------------------- Supabase setup ----------------------- */

let supabaseClient = null;
function getSupabaseClient() {
  if (supabaseClient) return supabaseClient;
  if (!window.SUPABASE_URL || !window.SUPABASE_ANON_KEY || window.SUPABASE_URL.includes("YOUR-PROJECT")) {
    return null;
  }
  supabaseClient = window.supabase.createClient(window.SUPABASE_URL, window.SUPABASE_ANON_KEY);
  return supabaseClient;
}

function uuid() {
  if (window.crypto?.randomUUID) return crypto.randomUUID();
  return "id-" + Math.random().toString(36).slice(2) + Date.now().toString(36);
}

/* ----------------------- shared game state ----------------------- */

let mode = null; // "host" | "client" | "local"
let channel = null;

let players = {};
let platforms = [];
let climbableSpots = []; // {x,y,w} — every reachable platform (incl. ground), used to place buffs/portals
let buffs = []; // {id,type,x,y,active,respawnAt}
let portals = []; // {id,x,y,linkId,color}
let localPlayerId = null;
let roomCode = null;
let gameRunning = false;
let gameEndsAt = 0;
let lastTagAt = 0;

const keys = {};
const jumpQueue = { p1: false, p2: false, solo: false };

const canvas = $("game-canvas");
const ctx = canvas.getContext("2d");

function resizeCanvas() {
  canvas.width = window.innerWidth * devicePixelRatio;
  canvas.height = window.innerHeight * devicePixelRatio;
  canvas.style.width = window.innerWidth + "px";
  canvas.style.height = window.innerHeight + "px";
  ctx.setTransform(devicePixelRatio, 0, 0, devicePixelRatio, 0, 0);
}
window.addEventListener("resize", resizeCanvas);

function arenaSize() {
  return { w: window.innerWidth, h: window.innerHeight };
}

/* ----------------------- map generation ----------------------- */
/* Platforms are built tier by tier: every platform in a tier is anchored
   to (placed within safe jump reach of) a specific platform in the tier
   below, so there's always a legal jump path from the ground to every
   platform on the map — nothing is ever stranded/unreachable. */

function generatePlatforms(size) {
  const list = [];
  const groundY = size.h - 36;
  const ground = { x: 0, y: groundY, w: size.w, h: 36, isGround: true };
  list.push(ground);

  const topMargin = 110;
  const usableH = size.h - 120 - topMargin;
  const tierGap = Math.max(50, Math.min(SAFE_VERTICAL_REACH, 80));
  const tierCount = Math.max(7, Math.floor(usableH / tierGap));

  let prevTier = [ground];
  const climbable = [];

  for (let t = 1; t <= tierCount; t++) {
    const y = groundY - t * tierGap - (Math.random() * 16 - 8);
    const count = 3 + Math.floor(Math.random() * 3); // 3-5 platforms per tier
    const tierPlats = [];
    for (let i = 0; i < count; i++) {
      const anchor = prevTier[Math.floor(Math.random() * prevTier.length)];
      const w = 55 + Math.random() * 45;
      let x;
      if (anchor.isGround) {
        // ground is walkable along its whole width, so any x works
        x = 20 + Math.random() * (size.w - 40 - w);
      } else {
        const anchorCenter = anchor.x + anchor.w / 2;
        const offset = (Math.random() - 0.5) * SAFE_HORIZONTAL_REACH * 1.3;
        x = anchorCenter + offset - w / 2;
        x = Math.max(10, Math.min(size.w - w - 10, x));
      }
      const plat = { x, y, w, h: 16 };
      tierPlats.push(plat);
      list.push(plat);
      climbable.push(plat);
    }
    prevTier = tierPlats;
  }

  // decorative dodge obstacles — narrow ground pillars, NOT part of the
  // climb path, so they add clutter without ever blocking access
  const pillarCount = Math.max(3, Math.round(size.w / 340));
  for (let i = 0; i < pillarCount; i++) {
    const pw = 16 + Math.random() * 10;
    const ph = 40 + Math.random() * 70;
    const px = 80 + Math.random() * (size.w - 160 - pw);
    list.push({ x: px, y: groundY - ph, w: pw, h: ph });
  }

  return { platforms: list, climbable: [ground, ...climbable] };
}

function pickSpot(spots, size, avoid = [], minDist = 90) {
  for (let attempt = 0; attempt < 20; attempt++) {
    const spot = spots[Math.floor(Math.random() * spots.length)];
    const x = spot.x + 10 + Math.random() * Math.max(1, spot.w - 20);
    const y = spot.y - 26;
    const tooClose = avoid.some((a) => Math.hypot(a.x - x, a.y - y) < minDist);
    if (!tooClose) return { x, y };
  }
  const spot = spots[Math.floor(Math.random() * spots.length)];
  return { x: spot.x + spot.w / 2, y: spot.y - 26 };
}

function generateBuffs(spots, size) {
  const list = [];
  const placed = [];
  for (let i = 0; i < BUFF_COUNT; i++) {
    const pos = pickSpot(spots, size, placed, 110);
    placed.push(pos);
    list.push({
      id: "buff-" + i,
      type: BUFF_TYPES[i % BUFF_TYPES.length],
      x: pos.x, y: pos.y,
      active: true,
      respawnAt: 0,
    });
  }
  return list;
}

function generatePortals(spots, size) {
  const list = [];
  const pairColors = ["#c792ea", "#ffd166"];
  const pairCount = size.w > 900 ? 2 : 1;
  const usedSpots = [];
  for (let p = 0; p < pairCount; p++) {
    // pick two spots that are far apart horizontally so portals are useful shortcuts
    let a = null, b = null;
    for (let attempt = 0; attempt < 30; attempt++) {
      const s1 = spots[Math.floor(Math.random() * spots.length)];
      const s2 = spots[Math.floor(Math.random() * spots.length)];
      if (Math.abs(s1.x - s2.x) > size.w * 0.35) { a = s1; b = s2; break; }
    }
    if (!a || !b) { a = spots[0]; b = spots[spots.length - 1]; }
    const idA = "portal-" + p + "a", idB = "portal-" + p + "b";
    list.push({ id: idA, x: a.x + a.w / 2, y: a.y - 24, linkId: idB, color: pairColors[p % pairColors.length] });
    list.push({ id: idB, x: b.x + b.w / 2, y: b.y - 24, linkId: idA, color: pairColors[p % pairColors.length] });
  }
  return list;
}

function generateMap(size) {
  const { platforms: plats, climbable } = generatePlatforms(size);
  platforms = plats;
  climbableSpots = climbable;
  buffs = generateBuffs(climbableSpots, size);
  portals = generatePortals(climbableSpots, size);
}

/* ----------------------- input handling ----------------------- */

window.addEventListener("keydown", (e) => {
  const k = e.key.toLowerCase();
  if (!keys[k]) {
    if (k === "w") jumpQueue.p1 = true;
    if (k === "arrowup") jumpQueue.p2 = true;
    if (k === "w" || k === "arrowup") jumpQueue.solo = true;
  }
  keys[k] = true;
  if (["arrowup", "arrowdown", "arrowleft", "arrowright", " "].includes(k)) e.preventDefault();
});
window.addEventListener("keyup", (e) => { keys[e.key.toLowerCase()] = false; });

const touchState = { left: false, right: false, jump: false };

function readWASDInput() {
  let x = 0;
  if (keys["a"]) x -= 1;
  if (keys["d"]) x += 1;
  if (touchState.left) x -= 1;
  if (touchState.right) x += 1;
  const jump = jumpQueue.p1;
  jumpQueue.p1 = false;
  return { x: Math.max(-1, Math.min(1, x)), jump };
}

function readArrowInput() {
  let x = 0;
  if (keys["arrowleft"]) x -= 1;
  if (keys["arrowright"]) x += 1;
  const jump = jumpQueue.p2;
  jumpQueue.p2 = false;
  return { x: Math.max(-1, Math.min(1, x)), jump };
}

function readSoloInput() {
  let x = 0;
  if (keys["a"] || keys["arrowleft"]) x -= 1;
  if (keys["d"] || keys["arrowright"]) x += 1;
  if (touchState.left) x -= 1;
  if (touchState.right) x += 1;
  const jump = jumpQueue.solo || touchState.jump;
  jumpQueue.solo = false;
  touchState.jump = false;
  return { x: Math.max(-1, Math.min(1, x)), jump };
}

(function setupTouchButtons() {
  const zone = $("touch-controls");
  zone.innerHTML = `
    <div id="btn-touch-left" class="touch-btn touch-btn-left">◀</div>
    <div id="btn-touch-right" class="touch-btn touch-btn-right">▶</div>
    <div id="btn-touch-jump" class="touch-btn touch-btn-jump">⤴</div>
  `;
  const left = $("btn-touch-left"), right = $("btn-touch-right"), jump = $("btn-touch-jump");

  function bind(el, key) {
    const start = (e) => { e.preventDefault(); touchState[key] = true; };
    const end = (e) => { e.preventDefault(); touchState[key] = false; };
    el.addEventListener("touchstart", start, { passive: false });
    el.addEventListener("touchend", end, { passive: false });
    el.addEventListener("touchcancel", end, { passive: false });
  }
  bind(left, "left");
  bind(right, "right");
  jump.addEventListener("touchstart", (e) => {
    e.preventDefault();
    touchState.jump = true;
    jumpQueue.p1 = true;
    jumpQueue.p2 = true;
    jumpQueue.solo = true;
  }, { passive: false });
})();

function isTouchDevice() {
  return "ontouchstart" in window || navigator.maxTouchPoints > 0;
}

/* ----------------------- menu wiring ----------------------- */

$("btn-host").addEventListener("click", startHostFlow);
$("btn-join").addEventListener("click", () => showScreen("join"));
$("btn-local").addEventListener("click", startLocalGame);
$("btn-connect").addEventListener("click", connectToHost);
$("btn-copy-code").addEventListener("click", () => {
  navigator.clipboard?.writeText(roomCode || "");
  $("btn-copy-code").textContent = "Copied!";
  setTimeout(() => ($("btn-copy-code").textContent = "Copy Code"), 1200);
});
$("btn-play-again").addEventListener("click", () => {
  teardownNetwork();
  showScreen("menu");
});

function randomRoomCode() {
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let s = "";
  for (let i = 0; i < 6; i++) s += chars[Math.floor(Math.random() * chars.length)];
  return s;
}

function channelNameFor(code) {
  return "tagged-room-" + code;
}

/* ----------------------- hosting ----------------------- */

function startHostFlow() {
  showScreen("host");
  const sb = getSupabaseClient();
  if (!sb) {
    $("room-code").textContent = "Not configured";
    $("btn-start-hosted").textContent = "Add Supabase keys to config.js first";
    return;
  }

  mode = "host";
  players = {};
  roomCode = randomRoomCode();
  localPlayerId = uuid();
  $("room-code").textContent = "Connecting…";

  channel = sb.channel(channelNameFor(roomCode), {
    config: { broadcast: { self: false, ack: false }, presence: { key: localPlayerId } },
  });

  channel.on("broadcast", { event: "input" }, ({ payload }) => {
    const p = players[payload.id];
    if (p) p.input = payload.vec;
  });

  channel.on("presence", { event: "sync" }, () => {
    if (gameRunning) return;
    const state = channel.presenceState();
    const seenIds = new Set();
    Object.keys(state).forEach((key) => {
      seenIds.add(key);
      const meta = state[key][0] || {};
      if (!players[key]) addPlayer(key, meta.name || "Player");
      else if (meta.name) players[key].name = meta.name;
    });
    Object.keys(players).forEach((id) => { if (!seenIds.has(id)) delete players[id]; });
    renderLobby();
  });

  channel.on("presence", { event: "leave" }, ({ key }) => {
    if (!gameRunning && players[key]) { delete players[key]; renderLobby(); }
  });

  channel.subscribe(async (status) => {
    if (status === "SUBSCRIBED") {
      $("room-code").textContent = roomCode;
      const hostName = $("host-name").value.trim() || "Host";
      await channel.track({ name: hostName });
      addPlayer(localPlayerId, hostName);
      renderLobby();
      $("btn-start-hosted").disabled = false;
      $("btn-start-hosted").textContent = "Start Game";
    } else if (status === "CHANNEL_ERROR" || status === "TIMED_OUT") {
      $("room-code").textContent = "Connection error";
      $("btn-start-hosted").textContent = "Can't host — check your network / Supabase keys";
    }
  });

  $("host-name").oninput = () => {
    if (players[localPlayerId]) {
      players[localPlayerId].name = $("host-name").value.trim() || "Host";
      renderLobby();
      channel?.track({ name: players[localPlayerId].name });
    }
  };

  $("btn-start-hosted").onclick = () => {
    if (Object.keys(players).length < 1) return;
    generateMap(arenaSize());
    beginGame();
    channel.send({ type: "broadcast", event: "start", payload: { platforms, portals } });
  };
}

function addPlayer(id, name) {
  const colorIdx = Object.keys(players).length % COLORS.length;
  const size = arenaSize();
  players[id] = {
    id, name,
    color: COLORS[colorIdx],
    x: 60 + Math.random() * (size.w - 120),
    y: 40,
    vx: 0, vy: 0,
    grounded: false,
    facing: 1,
    isIt: false,
    immuneUntil: 0,
    itTimeMs: 0,
    speedUntil: 0,
    jumpUntil: 0,
    shieldUntil: 0,
    portalCooldownUntil: 0,
  };
}

function renderLobby() {
  const wrap = $("lobby-players");
  wrap.innerHTML = "";
  Object.values(players).forEach((p) => {
    const row = document.createElement("div");
    row.className = "lobby-player";
    row.innerHTML = `<span class="swatch" style="background:${p.color}"></span>${p.name}`;
    wrap.appendChild(row);
  });
}

/* ----------------------- joining ----------------------- */

function connectToHost() {
  const sb = getSupabaseClient();
  if (!sb) {
    $("join-status").textContent = "Game isn't configured with Supabase keys yet.";
    return;
  }
  const nameVal = $("join-name").value.trim() || "Player";
  const code = $("join-code").value.trim().toUpperCase();
  if (!code) { $("join-status").textContent = "Enter a room code."; return; }

  $("join-status").textContent = "Connecting…";
  mode = "client";
  localPlayerId = uuid();

  channel = sb.channel(channelNameFor(code), {
    config: { broadcast: { self: false, ack: false }, presence: { key: localPlayerId } },
  });

  let gotState = false;
  const timeout = setTimeout(() => {
    if (!gotState) $("join-status").textContent = "Connected — waiting for the host to start…";
  }, 1500);

  channel.on("broadcast", { event: "start" }, ({ payload }) => {
    platforms = payload.platforms;
    portals = payload.portals;
    beginGame();
  });

  channel.on("broadcast", { event: "state" }, ({ payload }) => {
    gotState = true;
    players = payload.players;
    buffs = payload.buffs;
    gameEndsAt = payload.gameEndsAt;
  });

  channel.on("broadcast", { event: "gameover" }, ({ payload }) => {
    showGameOver(payload.results);
  });

  channel.subscribe(async (status) => {
    if (status === "SUBSCRIBED") {
      clearTimeout(timeout);
      await channel.track({ name: nameVal });
      $("join-status").textContent = "Connected! Waiting for host to start…";
    } else if (status === "CHANNEL_ERROR" || status === "TIMED_OUT") {
      clearTimeout(timeout);
      $("join-status").textContent = "Couldn't connect. Check the code and try again.";
    }
  });
}

/* ----------------------- local 2-player ----------------------- */

function startLocalGame() {
  mode = "local";
  players = {};
  const size = arenaSize();
  generateMap(size);
  players["p1"] = {
    id: "p1", name: "P1 (WASD)", color: COLORS[0],
    x: size.w * 0.3, y: 40, vx: 0, vy: 0,
    grounded: false, facing: 1,
    isIt: true, immuneUntil: 0, itTimeMs: 0,
    speedUntil: 0, jumpUntil: 0, shieldUntil: 0, portalCooldownUntil: 0,
  };
  players["p2"] = {
    id: "p2", name: "P2 (Arrows)", color: COLORS[1],
    x: size.w * 0.7, y: 40, vx: 0, vy: 0,
    grounded: false, facing: -1,
    isIt: false, immuneUntil: 0, itTimeMs: 0,
    speedUntil: 0, jumpUntil: 0, shieldUntil: 0, portalCooldownUntil: 0,
  };
  beginGame();
}

/* ----------------------- game loop ----------------------- */

let lastFrameTime = 0;
let lastNetworkSend = 0;

function beginGame() {
  showScreen("game");
  resizeCanvas();
  $("touch-controls").classList.toggle("hidden", !isTouchDevice());

  if (mode === "host" || mode === "local") {
    const ids = Object.keys(players);
    if (!ids.some((id) => players[id].isIt) && ids.length) {
      players[ids[Math.floor(Math.random() * ids.length)]].isIt = true;
    }
    gameEndsAt = performance.now() + GAME_DURATION_MS;
  }

  gameRunning = true;
  lastFrameTime = performance.now();
  requestAnimationFrame(loop);
}

function loop(now) {
  if (!gameRunning) return;
  const dt = Math.min((now - lastFrameTime) / 1000, 0.05);
  lastFrameTime = now;

  if (mode === "host" || mode === "local") {
    hostSimulate(dt, now);
  } else if (mode === "client") {
    sendClientInput(now);
  }

  render(now);
  requestAnimationFrame(loop);
}

/* AABB platform collision for a rectangular player body */
function resolvePlatformCollisions(p, dt) {
  const halfW = PLAYER_W / 2, halfH = PLAYER_H / 2;
  const size = arenaSize();

  let newX = p.x + p.vx * dt;
  newX = Math.max(halfW, Math.min(size.w - halfW, newX));
  const bx1 = newX - halfW, bx2 = newX + halfW;
  const by1 = p.y - halfH, by2 = p.y + halfH;
  for (const plat of platforms) {
    const overlapY = by1 < plat.y + plat.h && by2 > plat.y;
    const overlapX = bx2 > plat.x && bx1 < plat.x + plat.w;
    if (overlapY && overlapX) {
      if (p.vx > 0) newX = plat.x - halfW;
      else if (p.vx < 0) newX = plat.x + plat.w + halfW;
      p.vx = 0;
      break;
    }
  }
  p.x = newX;

  let newY = p.y + p.vy * dt;
  p.grounded = false;
  const bx1b = p.x - halfW, bx2b = p.x + halfW;
  let by1b = newY - halfH, by2b = newY + halfH;
  for (const plat of platforms) {
    const overlapX = bx2b > plat.x && bx1b < plat.x + plat.w;
    const overlapY = by1b < plat.y + plat.h && by2b > plat.y;
    if (overlapX && overlapY) {
      if (p.vy > 0) { newY = plat.y - halfH; p.grounded = true; }
      else if (p.vy < 0) { newY = plat.y + plat.h + halfH; }
      p.vy = 0;
      by1b = newY - halfH; by2b = newY + halfH;
    }
  }
  if (newY + halfH > size.h) { newY = size.h - halfH; p.vy = 0; p.grounded = true; }
  p.y = newY;
}

function stepPlayerPhysics(p, dt, now) {
  const inp = p.input || { x: 0, jump: false };
  const speedMult = now < (p.speedUntil || 0) ? BUFF_SPEED_MULT : 1;
  const jumpMult = now < (p.jumpUntil || 0) ? BUFF_JUMP_MULT : 1;

  p.vx = inp.x * MOVE_SPEED * speedMult;
  if (inp.x !== 0) p.facing = inp.x > 0 ? 1 : -1;

  p.vy += GRAVITY * dt;
  if (p.vy > MAX_FALL_SPEED) p.vy = MAX_FALL_SPEED;

  if (inp.jump && p.grounded) {
    p.vy = JUMP_VELOCITY * jumpMult;
    p.grounded = false;
  }

  resolvePlatformCollisions(p, dt);
  if (p.isIt) p.itTimeMs += dt * 1000;
}

function checkBuffPickups(list, now) {
  buffs.forEach((buff) => {
    if (!buff.active) {
      if (now >= buff.respawnAt) {
        const spot = pickSpot(climbableSpots, arenaSize(), [], 60);
        buff.x = spot.x; buff.y = spot.y;
        buff.active = true;
      }
      return;
    }
    for (const p of list) {
      const dist = Math.hypot(p.x - buff.x, p.y - buff.y);
      if (dist < BUFF_RADIUS + PLAYER_W / 2) {
        if (buff.type === "speed") p.speedUntil = now + BUFF_DURATION_MS;
        else if (buff.type === "jump") p.jumpUntil = now + BUFF_DURATION_MS;
        else if (buff.type === "shield") p.shieldUntil = now + BUFF_DURATION_MS;
        buff.active = false;
        buff.respawnAt = now + BUFF_RESPAWN_MS;
        break;
      }
    }
  });
}

function checkPortals(list, now) {
  for (const p of list) {
    if (now < (p.portalCooldownUntil || 0)) continue;
    for (const portal of portals) {
      const dist = Math.hypot(p.x - portal.x, p.y - portal.y);
      if (dist < PORTAL_RADIUS + PLAYER_W / 2) {
        const dest = portals.find((pt) => pt.id === portal.linkId);
        if (dest) {
          p.x = dest.x;
          p.y = dest.y;
          p.portalCooldownUntil = now + PORTAL_COOLDOWN_MS;
        }
        break;
      }
    }
  }
}

function hostSimulate(dt, now) {
  if (mode === "host" && players[localPlayerId]) {
    players[localPlayerId].input = readSoloInput();
  }
  if (mode === "local") {
    players["p1"].input = readWASDInput();
    players["p2"].input = readArrowInput();
  }

  const list = Object.values(players);
  list.forEach((p) => stepPlayerPhysics(p, dt, now));
  checkBuffPickups(list, now);
  checkPortals(list, now);

  const itPlayer = list.find((p) => p.isIt);
  if (itPlayer && now > lastTagAt + 50) {
    for (const other of list) {
      if (other.id === itPlayer.id) continue;
      if (now < other.immuneUntil) continue;
      if (now < (other.shieldUntil || 0)) continue; // shield buff blocks being tagged
      const dist = Math.hypot(other.x - itPlayer.x, other.y - itPlayer.y);
      if (dist < TAG_DISTANCE) {
        itPlayer.isIt = false;
        other.isIt = true;
        other.immuneUntil = 0;
        itPlayer.immuneUntil = now + TAG_COOLDOWN_MS;
        lastTagAt = now;
        break;
      }
    }
  }

  const msLeft = gameEndsAt - now;
  $("hud-timer").textContent = formatTime(Math.max(0, msLeft));
  $("hud-status").textContent = itPlayer ? `${itPlayer.name} is IT` : "";
  $("hud-scores").textContent = list.map((p) => p.name.split(" ")[0]).join(" · ");

  if (msLeft <= 0) { endGame(); return; }

  if (mode === "host" && now - lastNetworkSend > NETWORK_TICK_MS) {
    lastNetworkSend = now;
    channel?.send({ type: "broadcast", event: "state", payload: { players: sanitizedPlayers(), buffs, gameEndsAt } });
  }
}

function sanitizedPlayers() {
  const out = {};
  Object.values(players).forEach((p) => {
    const { input, ...rest } = p;
    out[p.id] = rest;
  });
  return out;
}

function sendClientInput(now) {
  if (!channel) return;
  if (now - lastNetworkSend > NETWORK_TICK_MS) {
    lastNetworkSend = now;
    channel.send({ type: "broadcast", event: "input", payload: { id: localPlayerId, vec: readSoloInput() } });
  }
  const msLeft = gameEndsAt - now;
  $("hud-timer").textContent = formatTime(Math.max(0, msLeft));
  const itPlayer = Object.values(players).find((p) => p.isIt);
  $("hud-status").textContent = itPlayer ? `${itPlayer.name} is IT` : "";
  $("hud-scores").textContent = Object.values(players).map((p) => p.name.split(" ")[0]).join(" · ");
}

function formatTime(ms) {
  const total = Math.ceil(ms / 1000);
  const m = Math.floor(total / 60);
  const s = total % 60;
  return `${m}:${s.toString().padStart(2, "0")}`;
}

function endGame() {
  gameRunning = false;
  const results = Object.values(players)
    .map((p) => ({ name: p.name, itTimeMs: p.itTimeMs }))
    .sort((a, b) => a.itTimeMs - b.itTimeMs);
  if (mode === "host") channel?.send({ type: "broadcast", event: "gameover", payload: { results } });
  showGameOver(results);
}

function showGameOver(results) {
  gameRunning = false;
  showScreen("gameover");
  const wrap = $("gameover-results");
  wrap.innerHTML = "";
  results.forEach((r, i) => {
    const row = document.createElement("div");
    row.className = "result-row";
    const secs = (r.itTimeMs / 1000).toFixed(1);
    row.innerHTML = `<span>#${i + 1} ${r.name}</span><span>${secs}s as IT</span>`;
    wrap.appendChild(row);
  });
}

/* ----------------------- rendering ----------------------- */

const BUFF_GLYPH = { speed: "⚡", jump: "⬆", shield: "🛡" };
const BUFF_COLOR = { speed: "#ffd166", jump: "#82aaff", shield: "#5de4c7" };

function render(now) {
  const size = arenaSize();
  ctx.clearRect(0, 0, size.w, size.h);

  const grad = ctx.createLinearGradient(0, 0, 0, size.h);
  grad.addColorStop(0, "#201c33");
  grad.addColorStop(1, "#2a2444");
  ctx.fillStyle = grad;
  ctx.fillRect(0, 0, size.w, size.h);

  platforms.forEach((plat) => {
    ctx.fillStyle = "#3a3458";
    ctx.fillRect(plat.x, plat.y, plat.w, plat.h);
    ctx.fillStyle = "#5de4c7";
    ctx.fillRect(plat.x, plat.y, plat.w, 3);
  });

  // portals
  (portals || []).forEach((portal) => {
    ctx.save();
    ctx.shadowColor = portal.color;
    ctx.shadowBlur = 18;
    ctx.strokeStyle = portal.color;
    ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.ellipse(portal.x, portal.y, PORTAL_RADIUS * 0.55, PORTAL_RADIUS, (now / 400) % Math.PI, 0, Math.PI * 2);
    ctx.stroke();
    ctx.restore();
  });

  // buffs
  (buffs || []).forEach((buff) => {
    if (!buff.active) return;
    const bob = Math.sin(now / 300 + buff.x) * 4;
    ctx.save();
    ctx.shadowColor = BUFF_COLOR[buff.type];
    ctx.shadowBlur = 14;
    ctx.beginPath();
    ctx.arc(buff.x, buff.y + bob, BUFF_RADIUS, 0, Math.PI * 2);
    ctx.fillStyle = "rgba(255,255,255,0.08)";
    ctx.fill();
    ctx.strokeStyle = BUFF_COLOR[buff.type];
    ctx.lineWidth = 2;
    ctx.stroke();
    ctx.restore();
    ctx.font = "14px sans-serif";
    ctx.textAlign = "center";
    ctx.fillStyle = BUFF_COLOR[buff.type];
    ctx.fillText(BUFF_GLYPH[buff.type], buff.x, buff.y + bob + 5);
  });

  Object.values(players).forEach((p) => {
    const halfW = PLAYER_W / 2, halfH = PLAYER_H / 2;
    ctx.save();
    if (p.isIt) { ctx.shadowColor = "#ff5d6c"; ctx.shadowBlur = 16; }
    else if (now < (p.shieldUntil || 0)) { ctx.shadowColor = "#5de4c7"; ctx.shadowBlur = 14; }
    ctx.fillStyle = p.isIt ? "#ff5d6c" : p.color;
    roundRect(ctx, p.x - halfW, p.y - halfH, PLAYER_W, PLAYER_H, 6);
    ctx.fill();
    if (now < (p.immuneUntil || 0) || now < (p.shieldUntil || 0)) {
      ctx.lineWidth = 2;
      ctx.strokeStyle = "rgba(255,255,255,0.6)";
      ctx.stroke();
    }
    ctx.restore();

    ctx.fillStyle = "#14121f";
    const eyeX = p.x + (p.facing || 1) * 4;
    ctx.beginPath();
    ctx.arc(eyeX, p.y - halfH * 0.3, 2, 0, Math.PI * 2);
    ctx.fill();

    // tiny buff icons above the player's head while active
    let iconOffset = 0;
    ["speed", "jump", "shield"].forEach((type) => {
      const untilKey = type + "Until";
      if (now < (p[untilKey] || 0)) {
        ctx.font = "10px sans-serif";
        ctx.fillStyle = BUFF_COLOR[type];
        ctx.fillText(BUFF_GLYPH[type], p.x - 10 + iconOffset, p.y - halfH - 22);
        iconOffset += 12;
      }
    });

    ctx.fillStyle = "#f4f2ff";
    ctx.font = "12px sans-serif";
    ctx.textAlign = "center";
    ctx.fillText(p.name, p.x, p.y - halfH - 8);
    if (p.isIt) {
      ctx.fillStyle = "#ff5d6c";
      ctx.font = "bold 10px sans-serif";
      ctx.fillText("IT", p.x, p.y - halfH - 34);
    }
  });
}

function roundRect(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

function teardownNetwork() {
  gameRunning = false;
  Object.keys(keys).forEach((k) => (keys[k] = false));
  jumpQueue.p1 = jumpQueue.p2 = jumpQueue.solo = false;
  if (channel) {
    try { supabaseClient?.removeChannel(channel); } catch (e) {}
    channel = null;
  }
  players = {};
  mode = null;
}
