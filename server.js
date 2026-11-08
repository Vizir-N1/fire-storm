'use strict';
/* FIRE STORM server v0.1 — accounts, rooms by code, authoritative 1v1 duel. */
const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto');
const { WebSocketServer } = require('ws'), Database = require('better-sqlite3');
const PORT = +process.env.PORT || 3000, PUB = path.join(__dirname, 'public');
const db = new Database(process.env.DB_PATH || path.join(__dirname, 'firestorm.db'));
db.pragma('journal_mode = WAL');
db.exec(`CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY AUTOINCREMENT,nick TEXT UNIQUE COLLATE NOCASE,hash TEXT,salt TEXT,rec TEXT,
coins INT DEFAULT 600,xp INT DEFAULT 0,inv TEXT DEFAULT '[]',eq TEXT DEFAULT '{}',stats TEXT DEFAULT '{}',created INT);
CREATE TABLE IF NOT EXISTS sessions(h TEXT PRIMARY KEY,uid INT,ts INT);
CREATE TABLE IF NOT EXISTS friends(a INT,b INT,st TEXT,PRIMARY KEY(a,b));`);

/* ---------- helpers ---------- */
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const scr = (pw, salt) => crypto.scryptSync(pw, salt, 64).toString('hex');
const same = (a, b) => { const x = Buffer.from(a), y = Buffer.from(b); return x.length === y.length && crypto.timingSafeEqual(x, y); };
const num = v => Number.isFinite(+v) ? +v : 0, clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const lvl = xp => Math.floor(Math.sqrt(xp / 50)) + 1;
const getU = id => db.prepare('SELECT * FROM users WHERE id=?').get(id);
const meOf = u => ({ id: u.id, nick: u.nick, coins: u.coins, xp: u.xp, inv: JSON.parse(u.inv), eq: JSON.parse(u.eq), stats: JSON.parse(u.stats) });
const send = (c, o) => { if (c && c.ws.readyState === 1) c.ws.send(JSON.stringify(o)); };
const err = (c, m) => send(c, { t: 'err', m });
const NICK = /^[A-Za-z0-9А-Яа-яЁё_]{3,16}$/;

/* ---------- game data (server is the source of truth) ---------- */
const RR = [50, 25, 14, 7, 3.5, 0.5];
const IT = [['Ржавчина', 'w', 0, '#6b4a2f'], ['Тканевые перчатки', 'g', 0, '#888'], ['Полевой нож', 'k', 0, '#aaa'], ['Синий лёд', 'w', 1, '#4fc3f7'], ['Frost Knife', 'k', 1, '#80d8ff'], ['Кровавый закат', 'w', 2, '#c62828'], ['Shadow Gloves', 'g', 2, '#444'], ['Драконье пламя', 'w', 3, '#ff6d00'], ['Fire Gloves', 'g', 3, '#ff3d00'], ['Neon Blade', 'k', 4, '#00e5ff'], ['Neon Gloves', 'g', 4, '#d500f9'], ['Dragon Fang', 'k', 5, '#ffd740']];
const CS = { s: { p: 500, cap: 3 }, f: { p: 1500, cap: 5 } };
const WEAP = {
  ak47: { d: 27, r: .10, mag: 30, rl: 2.2, sp: .020, p: 1 }, m4a1: { d: 24, r: .09, mag: 30, rl: 2.0, sp: .015, p: 1 },
  deagle: { d: 50, r: .35, mag: 7, rl: 1.8, sp: .006, p: 1 }, awp: { d: 110, r: 1.4, mag: 5, rl: 3.0, sp: .0015, p: 1 },
  mp5: { d: 17, r: .075, mag: 30, rl: 1.8, sp: .030, p: 1 }, shotgun: { d: 12, r: .9, mag: 6, rl: 2.4, sp: .06, p: 8 },
  fsar: { d: 26, r: .085, mag: 30, rl: 2.0, sp: .012, p: 1 }, shadow: { d: 24, r: .20, mag: 15, rl: 1.5, sp: .012, p: 1 },
  knife: { d: 55, r: .55, mag: 999, rl: 0, sp: 0, p: 1, range: 2.2 }
};
const ALL = Object.keys(WEAP).filter(k => k !== 'knife');
const RULES = { all: Object.keys(WEAP), pistols: ['deagle', 'shadow'], snipers: ['awp'], knives: ['knife'], random: [] };
const ARENA = 28, R = .45, SPEED = 6;
const EYE = 1.6, HEIGHT = 1.8, HEAD_Y = 1.4; // высота глаз, рост игрока, граница головы (клиент берёт значения из hello)
const OB = [[0, 0, 6, 2], [-12, 8, 3, 3], [12, -8, 3, 3], [-10, -12, 2, 6], [10, 12, 2, 6], [0, 14, 4, 1.5], [0, -14, 4, 1.5]];
const SPAWN = [[0, -24, Math.PI], [0, 24, 0]];
const TARGET = { 3: 2, 5: 3, 10: 6 };

function col(p) {
  p.x = clamp(p.x, -ARENA + .5, ARENA - .5); p.z = clamp(p.z, -ARENA + .5, ARENA - .5);
  for (const [cx, cz, w, d] of OB) {
    const nx = clamp(p.x, cx - w / 2, cx + w / 2), nz = clamp(p.z, cz - d / 2, cz + d / 2), dx = p.x - nx, dz = p.z - nz, l = Math.hypot(dx, dz);
    if (l < R) { if (l < 1e-6) p.x = cx - w / 2 - R; else { p.x = nx + dx / l * R; p.z = nz + dz / l * R; } }
  }
}
function blocked(ax, az, bx, bz) { // segment vs obstacle boxes (xz plane)
  for (const [cx, cz, w, d] of OB) {
    let t0 = 0, t1 = 1, ok = true; const dx = bx - ax, dz = bz - az;
    for (const [o, dd, mn, mx] of [[ax, dx, cx - w / 2, cx + w / 2], [az, dz, cz - d / 2, cz + d / 2]]) {
      if (Math.abs(dd) < 1e-9) { if (o < mn || o > mx) { ok = false; break; } }
      else { let a = (mn - o) / dd, b = (mx - o) / dd; if (a > b) [a, b] = [b, a]; t0 = Math.max(t0, a); t1 = Math.min(t1, b); if (t0 > t1) { ok = false; break; } }
    }
    if (ok) return true;
  }
  return false;
}

/* ---------- state ---------- */
const users = new Map(), userRoom = new Map(), rooms = new Map(), ipHits = new Map(), lastZr = new Map();
let queue = [];
const tooMany = ip => { const n = Date.now(), h = ipHits.get(ip) || { n: 0, t: n }; if (n - h.t > 60000) { h.n = 0; h.t = n; } h.n++; ipHits.set(ip, h); return h.n > 12; };
const newTok = uid => { const t = crypto.randomBytes(24).toString('hex'); db.prepare('INSERT INTO sessions VALUES(?,?,?)').run(sha(t), uid, Date.now()); return t; };
const pushMe = uid => send(users.get(uid), { t: 'me', me: meOf(getU(uid)) });

function authOk(c, u, tok, rec) {
  const old = users.get(u.id); if (old && old !== c) { old.uid = null; old.ws.close(4001); }
  c.uid = u.id; c.nick = u.nick; users.set(u.id, c);
  send(c, { t: 'auth', me: meOf(u), tok, rec });
  const r = rooms.get(userRoom.get(u.id));
  if (r) { const p = r.p.find(q => q.uid === u.id); if (p) { p.conn = c; p.dc = 0; sendRoom(r); } }
}

const fStatus = id => { if (!users.has(id)) return 'offline'; const r = rooms.get(userRoom.get(id)); return r ? (r.state === 'lobby' ? 'lobby' : 'match') : 'online'; };
function sendFriends(uid) {
  const nm = id => (db.prepare('SELECT nick FROM users WHERE id=?').get(id) || {}).nick, f = [], inc = [], out = [];
  for (const x of db.prepare('SELECT a,b,st FROM friends WHERE a=? OR b=?').all(uid, uid)) {
    const o = x.a === uid ? x.b : x.a;
    if (x.st === 'ok') f.push({ id: o, nick: nm(o), st: fStatus(o) }); else if (x.b === uid) inc.push({ id: o, nick: nm(o) }); else out.push({ id: o, nick: nm(o) });
  }
  send(users.get(uid), { t: 'flist', f, inc, out });
}
/* ---------- rooms ---------- */
const allowedList = r => r.rule === 'random' ? [] : RULES[r.rule];
const rinfo = r => ({ code: r.code, host: r.host, bo: r.bo, time: r.time, rule: r.rule, state: r.state, round: r.round, sc: r.sc, allowed: allowedList(r), players: r.p.map(p => ({ id: p.uid, nick: p.nick, lvl: lvl(p.xp), ready: p.ready, w: p.pw, online: !!p.conn || !!p.bot, skin: p.skin })) });
const sendRoom = r => r.p.forEach(p => send(p.conn, { t: 'room', room: rinfo(r) }));
const bcast = (r, o) => r.p.forEach(p => send(p.conn, o));
function mkRoom(c, bo, time, rule) {
  let code; do code = 'DUEL-' + (1000 + Math.floor(Math.random() * 9000)); while (rooms.has(code));
  const r = { code, host: c.uid, bo, time, rule, state: 'lobby', round: 0, sc: {}, p: [], until: 0, t0: 0 };
  rooms.set(code, r); joinRoom(r, c); return r;
}
function joinRoom(r, c) {
  queue = queue.filter(q => q.uid !== c.uid); // вошёл в комнату любым способом — больше не ищет быструю дуэль
  const u = getU(c.uid), eq = JSON.parse(u.eq), sk = IT.find(i => i[0] === eq.w);
  r.p.push({ uid: c.uid, nick: c.nick, conn: c, xp: u.xp, skin: sk ? sk[3] : '#c62828', ready: false, w: '', pw: allowedList(r)[0] || 'ak47', x: 0, z: 0, yaw: 0, pitch: 0, hp: 100, mag: 0, nextFire: 0, rlEnd: 0, kx: 0, kz: 0, li: 0, dc: 0, rm: false });
  userRoom.set(c.uid, r.code); sendRoom(r);
}
function leaveRoom(uid) {
  const r = rooms.get(userRoom.get(uid)); if (!r) return;
  const o = r.p.find(p => p.uid !== uid);
  if (o && ['countdown', 'live', 'between'].includes(r.state)) finish(r, o.uid, 'forfeit');
  r.p = r.p.filter(p => p.uid !== uid); userRoom.delete(uid);
  if (!r.p.length || r.p.every(p => p.bot)) { rooms.delete(r.code); return; }
  r.host = r.p[0].uid;
  // после окончания матча остаёмся в состоянии 'over', чтобы оставшийся игрок увидел результаты; комната удалится, когда он выйдет
  if (r.state !== 'over') { r.state = 'lobby'; r.p.forEach(p => { p.ready = !!p.bot; p.rm = false; }); }
  sendRoom(r);
}
function startMatch(r) { r.sc = {}; r.p.forEach(p => { r.sc[p.uid] = 0; p.rm = false; }); r.round = 0; startRound(r); }
function startRound(r) {
  r.round++; const yaws = {};
  r.p.forEach((p, i) => {
    if (p.bot && r.rule !== 'random') { const a = allowedList(r); p.pw = a[Math.floor(Math.random() * a.length)]; } p.seen = 0;
    p.w = r.rule === 'random' ? ALL[Math.floor(Math.random() * ALL.length)] : (allowedList(r).includes(p.pw) ? p.pw : allowedList(r)[0]);
    const s = SPAWN[i]; p.x = s[0]; p.z = s[1]; p.yaw = s[2]; p.pitch = 0; p.hp = 100; p.mag = WEAP[p.w].mag; p.rlEnd = 0; p.nextFire = 0; p.kx = p.kz = 0; yaws[p.uid] = s[2];
  });
  r.state = 'countdown'; r.until = Date.now() + 3000; sendRoom(r); bcast(r, { t: 'ev', k: 'spawn', yaw: yaws });
}
function roundEnd(r, winUid) {
  if (r.state !== 'live') return;
  if (winUid) r.sc[winUid]++;
  bcast(r, { t: 'ev', k: 'round', w: winUid, sc: r.sc });
  const tg = TARGET[r.bo];
  if (winUid && r.sc[winUid] >= tg) return finish(r, winUid, 'score');
  if (r.round >= tg * 2 + 3) { const [a, b] = r.p; return finish(r, r.sc[a.uid] > r.sc[b.uid] ? a.uid : r.sc[b.uid] > r.sc[a.uid] ? b.uid : null, 'score'); }
  r.state = 'between'; r.until = Date.now() + 4500; sendRoom(r);
}
function finish(r, w, why) {
  if (r.state === 'over') return;
  r.state = 'over';
  const botM = r.p.find(q => q.bot);
  for (const p of r.p) {
    if (p.bot) continue;
    const u = getU(p.uid), st = JSON.parse(u.stats || '{}'), d = st.duel = st.duel || { w: 0, l: 0, d: 0, streak: 0, best: 0, rank: 0 };
    const win = w === p.uid, dr = w == null;
    if (botM) { // vs bot: small reward, no rank change
      const bd = st.bot = st.bot || { w: 0, l: 0 }; if (win) bd.w++; else if (!dr) bd.l++;
      const coins = win ? 30 + 20 * botM.df : 10, xp = win ? 40 + 20 * botM.df : 20;
      db.prepare('UPDATE users SET coins=coins+?,xp=xp+?,stats=? WHERE id=?').run(coins, xp, JSON.stringify(st), p.uid); p.rw = { coins, xp, rank: d.rank }; continue;
    }
    if (dr) d.d++; else if (win) { d.w++; d.streak++; d.best = Math.max(d.best, d.streak); d.rank += 25; } else { d.l++; d.streak = 0; d.rank = Math.max(0, d.rank - 15); }
    const coins = dr ? 60 : win ? 120 + 10 * Math.min(d.streak, 10) : 40, xp = dr ? 80 : win ? 150 : 50;
    db.prepare('UPDATE users SET coins=coins+?,xp=xp+?,stats=? WHERE id=?').run(coins, xp, JSON.stringify(st), p.uid);
    p.rw = { coins, xp, rank: d.rank };
  }
  const scs = r.p.map(q => ({ n: q.nick, s: r.sc[q.uid] || 0 }));
  for (const p of r.p) { if (p.bot) continue; send(p.conn, { t: 'over', w, why, sc: scs, rw: p.rw }); pushMe(p.uid); }
  sendRoom(r);
}

/* ---------- combat (all checks are server-side) ---------- */
function shoot(r, p, m) {
  const now = Date.now(), W = WEAP[p.w];
  if (r.state !== 'live' || p.hp <= 0 || now < p.nextFire || p.rlEnd) return;
  if (p.mag <= 0) { p.rlEnd = now + W.rl * 1000; return; }
  p.mag--; p.nextFire = now + W.r * 1000;
  const yaw = num(m.yaw), pit = clamp(num(m.pitch), -1.4, 1.4); p.yaw = yaw; p.pitch = pit;
  const o = r.p.find(q => q !== p); let dmg = 0, head = false, ex, ey, ez;
  for (let i = 0; i < W.p; i++) {
    const yy = yaw + (Math.random() - .5) * 2 * W.sp, pp = pit + (Math.random() - .5) * 2 * W.sp;
    const dx = -Math.sin(yy) * Math.cos(pp), dy = Math.sin(pp), dz = -Math.cos(yy) * Math.cos(pp), range = W.range || 200;
    let tEnd = Math.min(range, 60);
    const fx = o.x - p.x, fz = o.z - p.z, a = dx * dx + dz * dz;
    if (a > 1e-9 && o.hp > 0) {
      const b = fx * dx + fz * dz, c = fx * fx + fz * fz - .25, disc = b * b - a * c;
      if (disc >= 0) {
        const t = (b - Math.sqrt(disc)) / a, y = EYE + dy * t;
        if (t > 0 && t <= range && y >= 0 && y <= HEIGHT && !blocked(p.x, p.z, p.x + dx * t, p.z + dz * t)) { const h = y > HEAD_Y; dmg += W.d * (h ? 2 : 1); head = head || h; tEnd = t; }
      }
    }
    if (i === 0) { ex = p.x + dx * tEnd; ey = EYE + dy * tEnd; ez = p.z + dz * tEnd; }
  }
  bcast(r, { t: 'ev', k: 'shot', id: p.uid, ex, ey, ez });
  if (dmg > 0) {
    o.hp = Math.max(0, o.hp - dmg); bcast(r, { t: 'ev', k: 'hit', id: o.uid, by: p.uid, dmg: Math.round(dmg), head });
    if (o.hp <= 0) roundEnd(r, p.uid);
  }
}

const MELEE_STOP = 1.2; // ножевой бот останавливается на таком расстоянии от цели (м)
const BOT_AIM_Y = 1.2; // уровень груди (ниже границы головы HEAD_Y)
const BDF = [{ err: .15, turn: 2.5, react: 600, gap: [700, 1300] }, { err: .08, turn: 4, react: 400, gap: [450, 800] }, { err: .035, turn: 8, react: 250, gap: [250, 500] }, { err: .012, turn: 14, react: 120, gap: [120, 300] }];
function botAI(r, p, now) { // simple server-side bot: turns at limited speed, strafes, reacts with delay, aims with error
  const o = r.p.find(q => q !== p), D = BDF[p.df]; p.li = now;
  if (!o || o.hp <= 0) { p.kx = p.kz = 0; return; }
  const dx = o.x - p.x, dz = o.z - p.z, dist = Math.hypot(dx, dz), W = WEAP[p.w], melee = !!W.range;
  const diff = Math.atan2(Math.sin(Math.atan2(-dx, -dz) - p.yaw), Math.cos(Math.atan2(-dx, -dz) - p.yaw)), step = D.turn * .05;
  p.yaw += clamp(diff, -step, step); p.pitch = Math.atan2(BOT_AIM_Y - EYE, Math.max(.3, dist - .5)); // целится в грудь: высота BOT_AIM_Y на поверхности хитбокса (dist - радиус)
  const pref = melee ? 0 : p.style === 'rusher' ? 7 : 20;
  p.kz = melee ? (dist > MELEE_STOP ? 1 : 0) : dist > pref + 4 ? 1 : dist < pref - 4 ? -.7 : 0; // нож: подходит и останавливается за MELEE_STOP
  if (now > (p.flip || 0)) { p.flip = now + 500 + Math.random() * 900; p.dir = Math.random() < .5 ? -1 : 1; }
  p.kx = melee ? (blocked(p.x, p.z, o.x, o.z) ? (p.dir || 1) : 0) : (p.dir || 1) * (.4 + p.df * .2);
  const los = !blocked(p.x, p.z, o.x, o.z);
  if (!los) p.seen = 0; else if (!p.seen) p.seen = now + D.react;
  if (los && now >= p.seen && Math.abs(diff) < .12 && (!melee || dist < W.range) && now >= (p.bnext || 0)) {
    shoot(r, p, { yaw: p.yaw + (Math.random() - .5) * 2 * D.err, pitch: p.pitch });
    p.bnext = now + Math.max(W.r * 1000, (D.gap[0] + Math.random() * (D.gap[1] - D.gap[0])) * (W.r < .2 ? .25 : 1));
  }
}
function tick(r, now) {
  for (const p of r.p) if (!p.conn && p.dc && now - p.dc > 20000) { leaveRoom(p.uid); return; }
  if (r.state === 'countdown' && now >= r.until) { r.state = 'live'; r.t0 = now; sendRoom(r); }
  else if (r.state === 'between' && now >= r.until) startRound(r);
  if (r.state === 'live') {
    const dt = .05;
    for (const p of r.p) {
      if (p.hp <= 0) continue;
      if (p.bot) botAI(r, p, now);
      let kx = now - p.li > 500 ? 0 : clamp(p.kx, -1, 1), kz = now - p.li > 500 ? 0 : clamp(p.kz, -1, 1); const m = Math.hypot(kx, kz); if (m > 1) { kx /= m; kz /= m; }
      p.x += (Math.cos(p.yaw) * kx - Math.sin(p.yaw) * kz) * SPEED * dt; p.z += (-Math.sin(p.yaw) * kx - Math.cos(p.yaw) * kz) * SPEED * dt; col(p);
      if (p.rlEnd && now >= p.rlEnd) { p.mag = WEAP[p.w].mag; p.rlEnd = 0; }
    }
    if (now - r.t0 >= r.time * 1000) { const [a, b] = r.p; roundEnd(r, a.hp > b.hp ? a.uid : b.hp > a.hp ? b.uid : null); }
  }
  if (r.state !== 'lobby') bcast(r, { t: 'snap', s: r.state, tl: r.state === 'live' ? Math.max(0, r.t0 + r.time * 1000 - now) : 0, p: r.p.map(p => ({ id: p.uid, x: +p.x.toFixed(2), z: +p.z.toFixed(2), yaw: +p.yaw.toFixed(2), pitch: +p.pitch.toFixed(2), hp: p.hp, w: p.w, mag: p.mag, rl: p.rlEnd ? 1 : 0 })) });
}
setInterval(() => { const now = Date.now(); for (const r of rooms.values()) { try { tick(r, now); } catch (e) { console.error(e); } } }, 50);

/* ---------- messages ---------- */
function onMessage(c, m) {
  if (!m || typeof m.t !== 'string') return;
  const now = Date.now(); if (now - c.rt > 1000) { c.rt = now; c.rate = 0; } if (++c.rate > 150) return;
  switch (m.t) {
    case 'ping': return send(c, { t: 'pong', ts: num(m.ts) });
    case 'reg': {
      if (tooMany(c.ip)) return err(c, 'Слишком много попыток, подождите минуту');
      const nick = String(m.nick || ''), pw = String(m.pw || '');
      if (!NICK.test(nick)) return err(c, 'Ник: 3–16 символов, буквы, цифры, _');
      if (pw.length < 6 || pw.length > 72) return err(c, 'Пароль: от 6 символов');
      const salt = crypto.randomBytes(16).toString('hex'), code = crypto.randomBytes(5).toString('hex').toUpperCase();
      let id; try { id = Number(db.prepare('INSERT INTO users(nick,hash,salt,rec,created) VALUES(?,?,?,?,?)').run(nick, scr(pw, salt), salt, sha(code + salt), Date.now()).lastInsertRowid); } catch (e) { return err(c, 'Ник занят'); }
      return authOk(c, getU(id), newTok(id), code);
    }
    case 'login': {
      if (tooMany(c.ip)) return err(c, 'Слишком много попыток, подождите минуту');
      const u = db.prepare('SELECT * FROM users WHERE nick=?').get(String(m.nick || ''));
      if (!u || !same(scr(String(m.pw || ''), u.salt), u.hash)) return err(c, 'Неверный ник или пароль');
      return authOk(c, u, newTok(u.id));
    }
    case 'tok': {
      const s = db.prepare('SELECT uid FROM sessions WHERE h=?').get(sha(String(m.tok || '')));
      const u = s && getU(s.uid); if (!u) return send(c, { t: 'tokbad' });
      return authOk(c, u, String(m.tok));
    }
    case 'rec': {
      if (tooMany(c.ip)) return err(c, 'Слишком много попыток, подождите минуту');
      const u = db.prepare('SELECT * FROM users WHERE nick=?').get(String(m.nick || '')), pw = String(m.pw || '');
      if (!u || !same(sha(String(m.code || '').trim().toUpperCase() + u.salt), u.rec)) return err(c, 'Неверный ник или код восстановления');
      if (pw.length < 6 || pw.length > 72) return err(c, 'Новый пароль: от 6 символов');
      const salt = crypto.randomBytes(16).toString('hex'), code = crypto.randomBytes(5).toString('hex').toUpperCase();
      db.prepare('UPDATE users SET hash=?,salt=?,rec=? WHERE id=?').run(scr(pw, salt), salt, sha(code + salt), u.id);
      db.prepare('DELETE FROM sessions WHERE uid=?').run(u.id);
      return authOk(c, getU(u.id), newTok(u.id), code);
    }
  }
  if (!c.uid) return;
  const uid = c.uid, r = rooms.get(userRoom.get(uid)), p = r && r.p.find(q => q.uid === uid);
  switch (m.t) {
    case 'out': db.prepare('DELETE FROM sessions WHERE h=?').run(sha(String(m.tok || ''))); leaveRoom(uid); queue = queue.filter(q => q !== c); users.delete(uid); c.uid = null; return;
    case 'case': {
      const k = CS[m.id]; if (!k) return; const u = getU(uid); if (u.coins < k.p) return err(c, 'Не хватает монет');
      let x = Math.random() * 100, a = 0, ri = 0; for (let i = 0; i < 6; i++) { a += RR[i]; if (x < a) { ri = i; break; } } ri = Math.min(ri, k.cap);
      const pool = IT.filter(i => i[2] === ri), it = pool[Math.floor(Math.random() * pool.length)], inv = JSON.parse(u.inv); inv.push(it[0]);
      db.prepare('UPDATE users SET coins=coins-?,inv=? WHERE id=?').run(k.p, JSON.stringify(inv), uid); pushMe(uid);
      return send(c, { t: 'cres', n: it[0], ty: it[1], ri, col: it[3] });
    }
    case 'equip': {
      const u = getU(uid), inv = JSON.parse(u.inv), eq = JSON.parse(u.eq), it = IT.find(i => i[0] === m.name);
      if (!it || !inv.includes(it[0])) return; eq[it[1]] = eq[it[1]] === it[0] ? null : it[0];
      db.prepare('UPDATE users SET eq=? WHERE id=?').run(JSON.stringify(eq), uid); return pushMe(uid);
    }
    case 'zr': { // offline zombie result: capped, NOT fully verifiable (no server simulation yet)
      if (now - (lastZr.get(uid) || 0) < 120000) return; lastZr.set(uid, now);
      const kills = clamp(Math.floor(num(m.kills)), 0, 222), df = clamp(Math.floor(num(m.df)), 0, 3), win = m.win && kills >= 200 ? 1 : 0, cm = [.7, 1, 1.4, 2][df];
      db.prepare('UPDATE users SET coins=coins+?,xp=xp+? WHERE id=?').run(Math.round(kills * 2 * cm + win * 500 * cm), kills * 3 + win * 300, uid); return pushMe(uid);
    }
    case 'create': {
      if (r) return err(c, 'Вы уже в комнате'); const bo = +m.bo, time = +m.time;
      if (!TARGET[bo] || ![60, 90, 120].includes(time) || !RULES[m.rule]) return err(c, 'Неверные настройки');
      mkRoom(c, bo, time, m.rule); return;
    }
    case 'join': {
      if (r) return err(c, 'Вы уже в комнате'); const t = rooms.get(String(m.code || '').trim().toUpperCase());
      if (!t) return err(c, 'Комната не найдена'); if (t.p.length >= 2 || t.state !== 'lobby') return err(c, 'Комната занята');
      joinRoom(t, c); return;
    }
    case 'quick': {
      if (r || queue.includes(c)) return; const o = queue.find(q => q.uid && q.uid !== uid && q.ws.readyState === 1 && !userRoom.has(q.uid));
      if (o) { queue = queue.filter(q => q !== o); const nr = mkRoom(o, 3, 60, 'all'); joinRoom(nr, c); nr.p.forEach(q => q.ready = true); startMatch(nr); }
      else { queue.push(c); send(c, { t: 'qs', on: 1 }); } return;
    }
    case 'flist': return sendFriends(uid);
    case 'fadd': {
      const t = db.prepare('SELECT id,nick FROM users WHERE nick=?').get(String(m.nick || '')); if (!t || t.id === uid) return err(c, 'Игрок не найден');
      const ex = db.prepare('SELECT * FROM friends WHERE (a=? AND b=?) OR (a=? AND b=?)').get(uid, t.id, t.id, uid);
      if (ex) { if (ex.st === 'req' && ex.a === t.id) db.prepare("UPDATE friends SET st='ok' WHERE a=? AND b=?").run(t.id, uid); else return err(c, ex.st === 'ok' ? 'Вы уже друзья' : 'Заявка уже отправлена'); }
      else db.prepare("INSERT INTO friends VALUES(?,?,'req')").run(uid, t.id);
      sendFriends(uid); if (users.has(t.id)) { sendFriends(t.id); send(users.get(t.id), { t: 'fnote', m: c.nick + ': заявка в друзья' }); } return;
    }
    case 'faccept': { const o = num(m.id); db.prepare("UPDATE friends SET st='ok' WHERE a=? AND b=? AND st='req'").run(o, uid); sendFriends(uid); if (users.has(o)) sendFriends(o); return; }
    case 'fdel': { const o = num(m.id); db.prepare('DELETE FROM friends WHERE (a=? AND b=?) OR (a=? AND b=?)').run(uid, o, o, uid); sendFriends(uid); if (users.has(o)) sendFriends(o); return; }
    case 'invite': {
      const o = num(m.id); if (!r || r.state !== 'lobby' || r.p.length >= 2) return err(c, 'Сначала создайте комнату со свободным местом');
      if (!db.prepare("SELECT 1 FROM friends WHERE st='ok' AND ((a=? AND b=?) OR (a=? AND b=?))").get(uid, o, o, uid)) return err(c, 'Это не ваш друг');
      const oc = users.get(o); if (!oc) return err(c, 'Друг не в сети'); if (userRoom.has(o)) return err(c, 'Друг уже в комнате');
      send(oc, { t: 'inv', from: c.nick, code: r.code }); return send(c, { t: 'fnote', m: 'Приглашение отправлено' });
    }
    case 'bot': {
      if (r) return err(c, 'Вы уже в комнате'); const bo = +m.bo, time = +m.time, df = clamp(Math.floor(num(m.df)), 0, 3);
      if (!TARGET[bo] || ![60, 90, 120].includes(time) || !RULES[m.rule]) return err(c, 'Неверные настройки');
      const nr = mkRoom(c, bo, time, m.rule), names = ['Vector', 'Ghost', 'Rex', 'Nova', 'Blaze', 'Ivan', 'Storm', 'Cobra'], cols = IT.filter(i => i[1] === 'w').map(i => i[3]);
      nr.p.push({ uid: -1, bot: true, df, style: Math.random() < .5 ? 'rusher' : 'anchor', nick: names[Math.floor(Math.random() * names.length)] + (df + 1), conn: null, xp: [0, 200, 800, 2000][df], skin: cols[Math.floor(Math.random() * cols.length)], ready: true, w: '', pw: allowedList(nr)[0] || 'ak47', x: 0, z: 0, yaw: 0, pitch: 0, hp: 100, mag: 0, nextFire: 0, rlEnd: 0, kx: 0, kz: 0, li: 0, dc: 0, rm: false });
      sendRoom(nr); return;
    }
    case 'qcancel': queue = queue.filter(q => q !== c); return;
  }
  if (!r || !p) return;
  switch (m.t) {
    case 'leave': return leaveRoom(uid);
    case 'ready': if (r.state !== 'lobby') return; p.ready = !!m.v; sendRoom(r); if (r.p.length === 2 && r.p.every(q => q.ready)) startMatch(r); return;
    case 'weapon': if (['lobby', 'between'].includes(r.state) && allowedList(r).includes(m.w)) { p.pw = m.w; sendRoom(r); } return;
    case 'cfgroom': {
      if (r.host !== uid || r.state !== 'lobby') return; const bo = +m.bo, time = +m.time;
      if (!TARGET[bo] || ![60, 90, 120].includes(time) || !RULES[m.rule]) return;
      Object.assign(r, { bo, time, rule: m.rule }); r.p.forEach(q => { q.ready = !!q.bot; if (!allowedList(r).includes(q.pw)) q.pw = allowedList(r)[0] || 'ak47'; }); sendRoom(r); return;
    }
    case 'kick': { if (r.host !== uid || r.state !== 'lobby') return; const o = r.p.find(q => q.uid !== uid); if (!o) return; send(o.conn, { t: 'kicked' }); leaveRoom(o.uid); return; }
    case 'chat': { const x = String(m.x || '').slice(0, 200).trim(); if (!x || now - (c.lc || 0) < 1000) return; c.lc = now; return bcast(r, { t: 'chat', n: c.nick, x }); }
    case 'in': if (r.state === 'live') { p.kx = num(m.kx); p.kz = num(m.kz); p.yaw = num(m.yaw); p.pitch = clamp(num(m.pitch), -1.4, 1.4); p.li = now; } return;
    case 'shoot': return shoot(r, p, m);
    case 'reload': { const W = WEAP[p.w]; if (r.state === 'live' && W && !p.rlEnd && p.mag < W.mag) p.rlEnd = now + W.rl * 1000; return; }
    case 'rematch': if (r.state !== 'over') return; if (r.p.length < 2) return err(c, 'Соперник покинул комнату'); p.rm = true; if (r.p.every(q => q.rm || q.bot)) startMatch(r); return;
  }
}
function onClose(c) {
  queue = queue.filter(q => q !== c);
  if (!c.uid || users.get(c.uid) !== c) return;
  users.delete(c.uid); const r = rooms.get(userRoom.get(c.uid)); if (!r) return;
  if (r.state === 'lobby') return leaveRoom(c.uid);
  const p = r.p.find(q => q.uid === c.uid); if (p) { p.conn = null; p.dc = Date.now(); bcast(r, { t: 'ev', k: 'dc', id: c.uid }); }
}

/* ---------- http + websocket ---------- */
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.css': 'text/css', '.png': 'image/png', '.svg': 'image/svg+xml' };
const server = http.createServer((req, res) => {
  if (req.url === '/health') { res.end('ok'); return; }
  let p = decodeURIComponent(req.url.split('?')[0]); if (p === '/') p = '/index.html';
  const f = path.join(PUB, path.normalize(p)); if (!f.startsWith(PUB + path.sep)) { res.writeHead(403); res.end(); return; }
  fs.readFile(f, (e, d) => { if (e) { res.writeHead(404); res.end('Not found'); return; } res.writeHead(200, { 'Content-Type': MIME[path.extname(f)] || 'application/octet-stream', 'X-Content-Type-Options': 'nosniff' }); res.end(d); });
});
const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 4096 });
wss.on('connection', (ws, req) => {
  const c = { ws, ip: String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim(), rt: Date.now(), rate: 0 };
  send(c, { t: 'hello', cfg: { A: ARENA, EYE, H: HEIGHT, OB, weap: Object.fromEntries(Object.entries(WEAP).map(([k, v]) => [k, { mag: v.mag }])) } });
  ws.on('message', d => { let m; try { m = JSON.parse(d); } catch { return; } try { onMessage(c, m); } catch (e) { console.error(e); } });
  ws.on('close', () => onClose(c)); ws.on('error', () => { });
});
server.listen(PORT, () => console.log('FIRE STORM server on :' + PORT));
