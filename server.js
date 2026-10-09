// Fusion Arena v3 - منظور جانبي + غرف بكود (بدون مكتبات خارجية)
const http = require('http'), fs = require('fs'), path = require('path');
const crypto = require('crypto'), os = require('os');

const PORT = process.env.PORT || 3000;
const W = 1280, H = 720, TICK = 30, DT = 1 / TICK, BLOCK = 40;
const GRAV = 2200, MAXFALL = 1100, JUMP = 820;

// ============ العالم (ماريو) ============
const LEVEL = {
  W, H,
  solids: [
    { x: 0, y: 640, w: 1280, h: 80 },     // الأرض
    { x: 300, y: 540, w: 60, h: 100 },    // أنبوب 1
    { x: 920, y: 540, w: 60, h: 100 }     // أنبوب 2
  ],
  plats: [                                 // منصات يمكن القفز من تحتها
    { x: 60, y: 500, w: 200 }, { x: 1020, y: 500, w: 200 },
    { x: 500, y: 400, w: 280 },
    { x: 400, y: 520, w: 120 }, { x: 760, y: 520, w: 120 }
  ]
};

// ============ إعدادات سهلة التعديل ============
const CFG = {
  xpMax: 80, xpPerDamage: 0.5,
  healCost: 20, healAmount: 25, healCooldown: 1,
  respawn: 5, killsToWin: 10,
  maxDuration: 5, tankDuration: 8, skillDuration: 25,
  cardDamage: 15, maxPlayers: 4
};

const CHARS = {
  cj: { name: 'CJ', hp: 110, speed: 210, w: 36, h: 58, color: '#2e8b3e', weapons: ['Pistol', 'Bat', 'Shotgun'],
    desc: 'قوي من بعيد، ضعيف من قريب. 3 أسلحة (مسدس / مضرب / شوتجن). عند 80 XP: دبابة 8 ثواني' },
  steve: { name: 'Steve', hp: 130, speed: 5 * BLOCK, w: 34, h: 58, color: '#2bb5c4', weapons: ['Sword', 'Bow'],
    desc: 'ملك القتال القريب: سيف، ترايدنت برق، رمح داش. عند 80 XP: Creative 25 ثانية (طيران + TNT + Potion + Finisher)' },
  ghost: { name: 'Ghost', hp: 120, speed: 150, w: 36, h: 60, color: '#8a6bf0', weapons: [],
    desc: 'ضرر عالي لكن بطيء. فازات مع XP. ثلاث قدرات أرواح بشحن طويل. عند 80 XP: Phase 3 لمدة 5 ثواني بدون شحن' },
  cuphead: { name: 'Cuphead', hp: 100, speed: 235, w: 32, h: 56, color: '#d42a2a', weapons: [],
    desc: 'سريع ومراوغ. رصاص سريع، ضربة مشحونة، داش، وسوبر بالكروت. عند 80 XP: MAX 5 ثواني' },
  dummy: { name: 'Dummy', hp: 300, speed: 0, w: 40, h: 60, color: '#777', weapons: [], desc: '' }
};

const CJ_W = [
  { kind: 'proj', dmg: 8, cd: .3, windup: 0, speed: 800, r: 5, life: .9, color: '#ffe08a' },
  { kind: 'melee', dmg: 18, cd: .8, windup: .1, range: 85, kb: 520 },
  { kind: 'spread', dmg: 4, pellets: 6, spread: .6, cd: 1.0, windup: 0, speed: 700, r: 4, life: .4, color: '#ffb84d' }
];
const CJ_SHELL = { kind: 'proj', dmg: 30, cd: 1.5, windup: 0, speed: 520, r: 10, life: 1.2, aoe: 90, color: '#cfd8dc' };
const ST_SWORD = { kind: 'melee', dmg: 6, cd: .3, windup: 0, range: 80 };
const ST_NETH = { kind: 'melee', dmg: 7.5, cd: .3, windup: 0, range: 85 };
const ST_BOW = { kind: 'proj', dmg: 7, cd: 1.3, windup: .6, speed: 520, r: 5, life: 1.2, color: '#d8c9a0' };
const GH_SW = [{ dmg: 9, cd: .8 }, { dmg: 12, cd: .6 }, { dmg: 14, cd: .4 }, { dmg: 17, cd: .1 }];
const GH_RV = [18, 20, 23, 25], GH_HG = [12, 14, 16, 19], GH_DV = [15, 17, 20, 22];
const GH_NEED = [20, 11, 15];

// ============ الحالة ============
let nextId = 0, R = null;                 // R = الغرفة الحالية أثناء المعالجة
const rooms = new Map();

const phaseOf = p => p.maxT > 0 ? 3 : p.xp >= 40 ? 2 : p.xp >= 20 ? 1 : 0;
const angd = (a, b) => { const d = a - b; return Math.atan2(Math.sin(d), Math.cos(d)); };
const cy = t => t.y - t.h / 2;                         // مركز الجسم
const dist = (a, b) => Math.hypot(a.x - b.x, cy(a) - cy(b));
const enemy = (p, t) => t.alive && t.team !== p.team;
const rdy = (p, k) => !(p.cdm[k] > 0);
const inRect = (x, y, s) => x > s.x && x < s.x + s.w && y > s.y && y < s.y + s.h;
const ov = (l, r, t, b, s) => l < s.x + s.w && r > s.x && t < s.y + s.h && b > s.y;

function newRoom(code) { return { code, clients: new Map(), phase: 'lobby', ents: [], projs: [], zones: [], score: { A: 0, B: 0 }, fx: [] }; }
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ';
function genCode() {
  for (;;) {
    let c = ''; for (let i = 0; i < 4; i++) c += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
    if (!rooms.has(c)) return c;
  }
}

function makeEnt(id, name, team, char) {
  const c = CHARS[char];
  return {
    id, name, team, char, hp: c.hp, maxHp: c.hp, x: 0, y: 0, w: c.w, h: c.h, vx: 0, vy: 0, dir: 1, face: 0,
    onGround: false, onPlat: false, drop: 0, fly: false,
    xp: 0, maxT: 0, ultT: 0, alive: true, resp: 0, cd: 0, hcd: 0, swing: 0, swingR: 0, wind: null,
    weapon: 0, inv: 0, kx: 0, forced: null, lt: null, cdm: {}, gch: [0, 0, 0],
    cards: 0, cardProg: 0, ch: 0, sup: null, fmode: 0, prev: {},
    inp: { up: 0, dn: 0, lf: 0, rt: 0, jump: 0, fire: 0, alt: 0, skr: 0, skf: 0, skg: 0, ult: 0, heal: 0, dash: 0, fin: 0, fm: 0, wp: 0 }
  };
}
function spawn(p) {
  const mates = R.ents.filter(e => e.team === p.team), idx = mates.indexOf(p), c = CHARS[p.char];
  p.hp = p.maxHp; p.alive = true; p.xp = 0; p.maxT = 0; p.ultT = 0; p.wind = null; p.cd = 0;
  p.kx = 0; p.vx = 0; p.vy = 0; p.forced = null; p.lt = null; p.cdm = {}; p.gch = [0, 0, 0];
  p.cards = 0; p.cardProg = 0; p.ch = 0; p.sup = null; p.w = c.w; p.h = c.h; p.fly = false;
  p.x = p.team === 'A' ? 140 + idx * 70 : W - 140 - idx * 70;
  p.y = 640; p.dir = p.team === 'A' ? 1 : -1; p.face = p.dir > 0 ? 0 : Math.PI; p.inv = 1.5;
}
function startMatch(room) {
  R = room;
  R.phase = 'playing'; R.score = { A: 0, B: 0 }; R.projs = []; R.zones = []; R.fx = []; R.ents = [];
  for (const c of R.clients.values()) R.ents.push(makeEnt(c.id, c.name, c.team, c.char));
  for (const t of ['A', 'B']) if (!R.ents.some(e => e.team === t)) R.ents.push(makeEnt(-(t === 'A' ? 1 : 2), 'Dummy', t, 'dummy'));
  R.ents.forEach(spawn);
}
function endMatch(winner) {
  broadcast(R, { t: 'end', winner });
  R.phase = 'lobby'; R.ents = []; R.projs = []; R.zones = []; R.fx = [];
  broadcastLobby(R);
}

// ============ الضرر والـXP ============
function addXP(p, n) {
  if (!p || p.maxT > 0 || p.ultT > 0) return;
  p.xp = Math.min(CFG.xpMax, p.xp + n);
  if (p.xp >= CFG.xpMax && (p.char === 'ghost' || p.char === 'cuphead')) {
    p.maxT = CFG.maxDuration; p.xp = 0; p.wind = null; p.ch = 0;
  }
}
function hurt(t, amount, src, o) {
  o = o || {};
  if (!t.alive || t.inv > 0) return;
  if (!o.pure) {
    if (t.char === 'cj' && t.ultT > 0) amount *= 0.4;    // Tank: 60% حماية
    if (t.char === 'steve' && t.ultT > 0) amount *= 0.9; // Skill: 10% حماية فقط
  }
  t.hp -= amount;
  R.fx.push({ k: 'd', x: Math.round(t.x), y: Math.round(t.y - t.h), v: Math.round(amount * 10) / 10 });
  if (src && src !== t) {
    addXP(src, amount * CFG.xpPerDamage);
    if (src.char === 'cuphead') {
      src.cardProg += amount;
      while (src.cardProg >= CFG.cardDamage && src.cards < 5) { src.cards++; src.cardProg -= CFG.cardDamage; }
      if (src.cards >= 5) src.cardProg = 0;
    }
  }
  if (t.hp <= 0) {
    t.alive = false; t.resp = t.char === 'dummy' ? 3 : CFG.respawn;
    t.wind = null; t.maxT = 0; t.ultT = 0; t.forced = null; t.sup = null; t.lt = null; t.fly = false;
    if (src && src.team !== t.team) {
      R.score[src.team]++;
      if (R.score[src.team] >= CFG.killsToWin) endMatch(src.team);
    }
  }
}
function knock(t, a, v) { t.kx += Math.cos(a) * v; if (t.onGround) { t.vy = -260; t.onGround = false; } }

// ============ الهجمات ============
function shoot(p, a, s) {
  R.projs.push({ o: p, team: p.team, x: p.x + Math.cos(a) * p.w / 2, y: cy(p) + Math.sin(a) * 8,
    vx: Math.cos(a) * s.speed, vy: Math.sin(a) * s.speed, dmg: s.dmg, r: s.r, life: s.life,
    pierce: !!s.pierce, aoe: s.aoe || 0, color: s.color, hit: [], lt: !!s.lt, kb: s.kb || 0, lob: null });
}
function lob(p, kind, color) {
  const a = p.face;
  R.projs.push({ o: p, team: p.team, x: p.x, y: cy(p), vx: Math.cos(a) * 430, vy: Math.sin(a) * 430 - 260,
    r: 8, life: 2, color, hit: [], dmg: 0, aoe: 0, lob: { kind } });
}
function execute(p, s) {
  if (s.kind === 'melee') {
    p.swing = .15; p.swingR = s.range;
    for (const t of R.ents) {
      if (!enemy(p, t)) continue;
      const a = Math.atan2(cy(t) - cy(p), t.x - p.x);
      if (dist(p, t) < s.range + t.w / 2 && Math.abs(angd(a, p.face)) < 1.0) {
        hurt(t, s.dmg, p);
        if (s.kb && t.alive) knock(t, a, s.kb);
        if (R.phase !== 'playing') return;
      }
    }
  } else {
    const n = s.pellets || 1;
    for (let k = 0; k < n; k++) shoot(p, p.face + (n > 1 ? (Math.random() - .5) * s.spread : 0), s);
  }
}
function primary(p) {
  switch (p.char) {
    case 'cj': return p.ultT > 0 ? CJ_SHELL : CJ_W[p.weapon];
    case 'steve': return p.weapon === 1 ? ST_BOW : (p.ultT > 0 ? ST_NETH : ST_SWORD);
    case 'ghost': { const g = GH_SW[phaseOf(p)]; return { kind: 'melee', dmg: g.dmg, cd: g.cd, windup: 0, range: 95 }; }
    case 'cuphead':
      return p.maxT > 0 ? { kind: 'proj', dmg: 6, cd: .09, windup: 0, speed: 900, r: 5, life: .8, color: '#ffe066' }
                        : { kind: 'proj', dmg: 4, cd: .18, windup: 0, speed: 760, r: 5, life: .8, color: '#ffffff' };
  }
  return null;
}
function primaryAttack(p) {
  const s = primary(p); if (!s || p.cd > 0) return;
  p.cd = s.cd;
  if (s.windup > 0 && p.maxT <= 0) p.wind = { t: s.windup, total: s.windup, spec: s };
  else execute(p, s);
}
function explodeShell(pr) {
  R.fx.push({ k: 'b', x: Math.round(pr.x), y: Math.round(pr.y), r: pr.aoe });
  for (const t of R.ents) {
    if (!t.alive || t.team === pr.team || t.fly) continue;
    const d = Math.hypot(t.x - pr.x, cy(t) - pr.y);
    if (d < pr.aoe + t.w / 2) hurt(t, pr.dmg * (1 - 0.5 * Math.min(1, d / pr.aoe)), pr.o);
    if (R.phase !== 'playing') return;
  }
}
function explodeTNT(x, y, o) {
  R.fx.push({ k: 'b', x: Math.round(x), y: Math.round(y), r: 120 });
  for (const t of R.ents) {
    if (!t.alive || t.team === o.team) continue;
    const d = Math.hypot(t.x - x, cy(t) - y);
    const dmg = d < 50 ? 35 : d < 85 ? 20 : d < 120 ? 10 : 0;   // قريب 35 / متوسط 20 / بعيد 10
    if (dmg) hurt(t, dmg, o);
    if (R.phase !== 'playing') return;
  }
}
function hitCircleBox(px, py, r, t) {
  const nx = Math.max(t.x - t.w / 2, Math.min(px, t.x + t.w / 2));
  const ny = Math.max(t.y - t.h, Math.min(py, t.y));
  return Math.hypot(px - nx, py - ny) < r;
}
function stepProjs() {
  const keep = [];
  for (const pr of R.projs) {
    if (pr.lob) {
      const py = pr.y;
      pr.vy += 1200 * DT; pr.x += pr.vx * DT; pr.y += pr.vy * DT; pr.life -= DT;
      let land = pr.life <= 0 || pr.x < 0 || pr.x > W || pr.y > H;
      for (const s of LEVEL.solids) if (inRect(pr.x, pr.y, s)) { land = true; pr.y = Math.min(pr.y, s.y - 2); }
      if (pr.vy > 0) for (const pl of LEVEL.plats) if (py <= pl.y && pr.y >= pl.y && pr.x > pl.x && pr.x < pl.x + pl.w) { land = true; pr.y = pl.y - 2; }
      if (pr.lob.kind === 'tnt') for (const t of R.ents) if (t.alive && t.team !== pr.team && hitCircleBox(pr.x, pr.y, 18, t)) land = true;
      if (land) {
        if (pr.lob.kind === 'tnt') { explodeTNT(pr.x, pr.y, pr.o); if (R.phase !== 'playing') return; }
        else R.zones.push({ x: pr.x, y: pr.y, r: 75, t: 5, tick: 0, team: pr.team, o: pr.o, color: '#c46bff' });
      } else keep.push(pr);
      continue;
    }
    pr.x += pr.vx * DT; pr.y += pr.vy * DT; pr.life -= DT;
    let dead = pr.life <= 0 || pr.x < 0 || pr.x > W || pr.y < -50 || pr.y > H;
    if (!dead) for (const s of LEVEL.solids) if (inRect(pr.x, pr.y, s)) { dead = true; if (pr.aoe) explodeShell(pr); break; }
    if (!dead) {
      for (const t of R.ents) {
        if (!t.alive || t.team === pr.team || pr.hit.includes(t.id)) continue;
        if (hitCircleBox(pr.x, pr.y, pr.r, t)) {
          pr.hit.push(t.id);
          if (pr.aoe) explodeShell(pr);
          else {
            hurt(t, pr.dmg, pr.o);
            if (t.alive && pr.lt) { t.lt = { t: 2, n: .5, dmg: 3, src: pr.o }; R.fx.push({ k: 'l', x: Math.round(t.x), y: Math.round(t.y) }); }
            if (t.alive && pr.kb) knock(t, Math.atan2(pr.vy, pr.vx), pr.kb);
          }
          if (R.phase !== 'playing') return;
          if (!pr.pierce) { dead = true; break; }
        }
      }
    } else if (pr.aoe && pr.life <= 0) { explodeShell(pr); if (R.phase !== 'playing') return; }
    if (!dead) keep.push(pr);
  }
  R.projs = keep;
}
function stepZones() {
  const keep = [];
  for (const z of R.zones) {
    z.tick -= DT; z.t -= DT;
    if (z.tick <= 0) {
      z.tick += 1;
      for (const t of R.ents) {
        if (t.alive && t.team !== z.team && Math.hypot(t.x - z.x, cy(t) - z.y) < z.r + t.w / 2) {
          hurt(t, 5, z.o); if (R.phase !== 'playing') return;
        }
      }
    }
    if (z.t > 0) keep.push(z);
  }
  R.zones = keep;
}

// ============ القدرات ============
function heal(p) {
  if (p.maxT > 0 || p.ultT > 0 || p.hcd > 0 || p.xp < CFG.healCost || p.hp >= p.maxHp) return;
  p.xp -= CFG.healCost; p.hp = Math.min(p.maxHp, p.hp + CFG.healAmount); p.hcd = CFG.healCooldown;
  R.fx.push({ k: 'h', x: Math.round(p.x), y: Math.round(cy(p)) });
}
function ult(p) {
  if (p.char === 'cj' && p.ultT <= 0 && p.xp >= CFG.xpMax) { p.xp = 0; p.ultT = CFG.tankDuration; p.wind = null; }
  else if (p.char === 'steve' && p.ultT <= 0 && p.xp >= CFG.xpMax) { p.xp = 0; p.ultT = CFG.skillDuration; p.wind = null; }
  else if (p.char === 'cuphead' && p.cards >= 5 && !p.sup) { p.cards = 0; p.cardProg = 0; p.sup = { n: 0, t: 0, base: p.face }; }
}
function stepSuper(p) {  // السوبر: 20 ضربة × 2 ضرر = 40 كحد أقصى
  const s = p.sup; s.t -= DT;
  while (s.t <= 0 && s.n < 20) {
    s.t += 0.1;
    shoot(p, s.base - 0.7 + s.n * (1.4 / 19), { dmg: 2, speed: 650, r: 6, life: 1.5, color: '#ffe066' });
    s.n++;
  }
  if (s.n >= 20) p.sup = null;
}
function dashCuphead(p, ix) {
  if (p.char !== 'cuphead' || !rdy(p, 'dash') || p.forced) return;
  const m = p.maxT > 0, d = ix || p.dir, sp = m ? 1000 : 720;
  p.forced = { kind: 'dash', t: m ? .12 : .15, vx: d * sp, vy: 0, hit: [] };
  p.cdm.dash = m ? 2 : 4; p.inv = Math.max(p.inv, .2);
}
function cupheadCharge(p, i) {
  const full = 1.5;
  if (p.maxT > 0) {                       // MAX: بدون شحن
    if (i.alt && rdy(p, 'cs')) { shoot(p, p.face, { dmg: 25, speed: 800, r: 13, life: 1, color: '#ffcf4a' }); p.cdm.cs = .6; }
    p.ch = 0; return;
  }
  if (i.alt && !i.fire) p.ch = Math.min(full, p.ch + DT);
  else if (!i.alt && p.ch > 0) {
    if (rdy(p, 'cs')) {
      const dmg = p.ch >= full ? 25 : p.ch >= 0.75 ? 15 : 8;
      shoot(p, p.face, { dmg, speed: 700, r: dmg >= 25 ? 13 : dmg >= 15 ? 9 : 6, life: 1, color: dmg >= 25 ? '#ffcf4a' : '#fff6c9' });
      p.cdm.cs = .4;
    }
    p.ch = 0;
  } else if (i.alt && i.fire) p.ch = 0;
}
function ghostAb(p, idx) {
  const mx = p.maxT > 0;
  if (p.cd > 0 || (!mx && p.gch[idx] < GH_NEED[idx])) return;
  if (!mx) p.gch[idx] = 0;
  p.cd = mx ? .35 : .6;
  const ph = phaseOf(p);
  if (idx === 0) shoot(p, p.face, { dmg: GH_RV[ph], speed: 380, r: 15, life: 1.7, pierce: true, color: '#c8b3ff' });   // الروح الانتقامية
  else if (idx === 1) {                                                                                         // أشباح العواء
    R.fx.push({ k: 'c', x: Math.round(p.x), y: Math.round(cy(p)), f: +p.face.toFixed(2), r: 220, h: .9 });
    for (const t of R.ents) {
      if (!enemy(p, t)) continue;
      if (dist(p, t) < 220 + t.w / 2 && Math.abs(angd(Math.atan2(cy(t) - cy(p), t.x - p.x), p.face)) < .9) {
        hurt(t, GH_HG[ph], p); if (R.phase !== 'playing') return;
      }
    }
  } else {                                                                                                       // الغطسة المهجورة
    const up = p.inp.up;
    p.forced = up ? { kind: 'dive', up: true, t: .3, vx: 0, vy: -900, dmg: GH_DV[ph], hit: [] }
                  : { kind: 'dive', up: false, t: .8, vx: 0, vy: 1400, dmg: GH_DV[ph], hit: [] };
  }
}
function finisher(p) {
  if (p.char !== 'steve' || p.ultT <= 0 || !rdy(p, 'fin')) return;
  let tgt = null, bd = 1e9;
  for (const t of R.ents) {
    if (!enemy(p, t) || t.hp > t.maxHp * .25) continue;
    const d = dist(p, t);
    if (d < 120 && d < bd) { bd = d; tgt = t; }
  }
  if (!tgt) return;
  p.cdm.fin = 6;
  const tx = tgt.x, ty = cy(tgt);
  hurt(tgt, tgt.hp + 1, p, { pure: true });
  if (R.phase !== 'playing') return;
  if (p.fmode === 0) {                                  // الطور 1: Mace Smash + موجة صدمة
    R.fx.push({ k: 'b', x: Math.round(tx), y: Math.round(ty), r: 90 });
    for (const t of R.ents) if (enemy(p, t) && Math.hypot(t.x - tx, cy(t) - ty) < 90) { hurt(t, 12, p); if (R.phase !== 'playing') return; }
  } else {                                              // الطور 2: صاعقة تقفز للأعداء القريبين
    R.fx.push({ k: 'l', x: Math.round(tx), y: Math.round(ty) });
    for (const t of R.ents) if (enemy(p, t) && Math.hypot(t.x - tx, cy(t) - ty) < 160) {
      hurt(t, 15, p); if (t.alive) t.lt = { t: 2, n: .5, dmg: 3, src: p };
      if (R.phase !== 'playing') return;
    }
  }
}

// ============ الفيزياء ============
function physics(p, vx, vy) {
  const hw = p.w / 2;
  p.x += vx * DT;
  for (const s of LEVEL.solids) {
    if (ov(p.x - hw, p.x + hw, p.y - p.h, p.y, s)) p.x = p.x < s.x + s.w / 2 ? s.x - hw : s.x + s.w + hw;
  }
  const prev = p.y;
  p.y += vy * DT; p.onGround = false; p.onPlat = false;
  for (const s of LEVEL.solids) {
    if (ov(p.x - hw, p.x + hw, p.y - p.h, p.y, s)) {
      if (vy >= 0) { p.y = s.y; p.vy = 0; p.onGround = true; }
      else { p.y = s.y + s.h + p.h; p.vy = 0; }
    }
  }
  if (vy >= 0 && p.drop <= 0) {
    for (const pl of LEVEL.plats) {
      if (prev <= pl.y + 0.5 && p.y >= pl.y && p.x + hw > pl.x && p.x - hw < pl.x + pl.w) { p.y = pl.y; p.vy = 0; p.onGround = true; p.onPlat = true; }
    }
  }
  p.x = Math.max(hw, Math.min(W - hw, p.x));
  if (p.y - p.h < 0) { p.y = p.h; if (p.vy < 0) p.vy = 0; }
  if (p.y > H) { p.y = 640; p.vy = 0; }
}
function aimOf(p) {
  const i = p.inp, d = p.dir, h = i.lf || i.rt;
  if (p.fly) return d > 0 ? 0 : Math.PI;
  if (i.up) return h ? (d > 0 ? -0.785 : -2.356) : -Math.PI / 2;
  if (i.dn && !p.onGround) return h ? (d > 0 ? 0.785 : 2.356) : Math.PI / 2;
  return d > 0 ? 0 : Math.PI;
}

function stepPlayer(p) {
  p.inv = Math.max(0, p.inv - DT);
  if (!p.alive) { p.resp -= DT; if (p.resp <= 0) spawn(p); return; }
  const i = p.inp;
  p.drop = Math.max(0, p.drop - DT);

  if (p.lt) {
    p.lt.t -= DT; p.lt.n -= DT;
    if (p.lt.n <= 0) { p.lt.n += .5; hurt(p, p.lt.dmg, p.lt.src); if (R.phase !== 'playing') return; }
    if (p.lt.t <= 0) p.lt = null;
  }
  if (!p.alive) return;
  const kx = p.kx; p.kx *= .85; if (Math.abs(p.kx) < 10) p.kx = 0;

  if (p.char === 'dummy') {
    p.vy = Math.min(MAXFALL, p.vy + GRAV * DT); physics(p, kx, p.vy); return;
  }

  // مؤقتات
  p.cd = Math.max(0, p.cd - DT); p.hcd = Math.max(0, p.hcd - DT); p.swing = Math.max(0, p.swing - DT);
  for (const k of Object.keys(p.cdm)) p.cdm[k] = Math.max(0, p.cdm[k] - DT);
  if (p.maxT > 0) { p.maxT -= DT; if (p.maxT <= 0) { p.maxT = 0; p.xp = 0; } }
  if (p.ultT > 0) { p.ultT -= DT; if (p.ultT <= 0) p.ultT = 0; }
  if (p.char === 'ghost' && p.maxT <= 0) for (let k = 0; k < 3; k++) p.gch[k] = Math.min(GH_NEED[k], p.gch[k] + DT);
  const tank = p.char === 'cj' && p.ultT > 0;
  p.w = tank ? 84 : CHARS[p.char].w; p.h = tank ? 50 : CHARS[p.char].h;
  p.fly = p.char === 'steve' && p.ultT > 0;

  const ix = (i.rt ? 1 : 0) - (i.lf ? 1 : 0);
  if (ix && !p.forced) p.dir = ix;
  p.face = aimOf(p);

  const edge = k => { const v = !!i[k], r = v && !p.prev[k]; p.prev[k] = v; return r; };
  if (edge('heal')) heal(p);
  if (edge('ult')) ult(p);
  if (edge('dash')) dashCuphead(p, ix);
  if (edge('fm') && p.char === 'steve') p.fmode = 1 - p.fmode;
  if (edge('fin')) { finisher(p); if (R.phase !== 'playing') return; }
  if (p.char === 'cj' && p.ultT <= 0 && i.wp >= 0 && i.wp < 3) p.weapon = i.wp;
  if (p.char === 'steve' && i.wp >= 0 && i.wp < 2) p.weapon = i.wp;

  // الحركة
  let sp = CHARS[p.char].speed;
  if (tank) sp *= .75;
  if (p.fly) sp = 8 * BLOCK;                                      // 5 → 8 Blocks/s
  if (p.maxT > 0) sp *= 1.1;
  if (p.sup) sp *= .5;
  const jumpEdge = edge('jump');
  let vx, vy;
  if (p.forced) {
    vx = p.forced.vx; vy = p.forced.vy; p.vy = vy;
  } else if (p.fly) {
    vx = ix * sp; vy = ((i.dn ? 1 : 0) - (i.up ? 1 : 0)) * sp; p.vy = 0;
  } else {
    vx = ix * sp;
    if (jumpEdge) {
      if (i.dn && p.onPlat) p.drop = .25;
      else if (p.onGround) { p.vy = -JUMP * (tank ? .7 : 1); p.onGround = false; }
    }
    p.vy = Math.min(MAXFALL, p.vy + GRAV * DT); vy = p.vy;
  }
  p.vx = vx;
  physics(p, vx + kx, vy);

  if (p.forced) {
    const f = p.forced; f.t -= DT;
    if (f.kind === 'spear') {
      for (const t of R.ents) {
        if (enemy(p, t) && !f.hit.includes(t.id) && Math.abs(t.x - p.x) < (p.w + t.w) / 2 + 16 && Math.abs(cy(t) - cy(p)) < (p.h + t.h) / 2) {
          f.hit.push(t.id); hurt(t, 25, p); if (R.phase !== 'playing') return;
          if (t.alive) knock(t, p.dir > 0 ? 0 : Math.PI, 300);
        }
      }
    }
    if (f.t <= 0 || (f.kind === 'dive' && !f.up && p.onGround)) {
      if (f.kind === 'dive') {
        R.fx.push({ k: 'b', x: Math.round(p.x), y: Math.round(cy(p)), r: 110 });
        for (const t of R.ents) if (enemy(p, t) && !t.fly && dist(p, t) < 110 + t.w / 2) { hurt(t, f.dmg, p); if (R.phase !== 'playing') return; }
      }
      p.forced = null; p.vy = 0;
    }
  }

  // الهجمات
  if (p.wind) { p.wind.t -= DT; if (p.wind.t <= 0) { const s = p.wind.spec; p.wind = null; execute(p, s); if (R.phase !== 'playing') return; } }
  if (p.sup) stepSuper(p);
  if (p.char === 'cuphead' && !p.sup) cupheadCharge(p, i);
  if (!p.wind && !p.forced && !p.sup) {
    if (i.fire) { primaryAttack(p); if (R.phase !== 'playing') return; }
    switch (p.char) {
      case 'steve':
        if (i.alt && rdy(p, 'tri')) { shoot(p, p.face, { dmg: 15, speed: 600, r: 8, life: 1, lt: true, color: '#7dffea' }); p.cdm.tri = 5; }
        if (i.skr && rdy(p, 'spr')) { p.forced = { kind: 'spear', t: .2, vx: p.dir * 900, vy: 0, hit: [] }; p.cdm.spr = 7; }
        if (p.ultT > 0) {
          if (i.skf && rdy(p, 'tnt')) { lob(p, 'tnt', '#e0463c'); p.cdm.tnt = 3; }
          if (i.skg && rdy(p, 'pot')) { lob(p, 'pot', '#c46bff'); p.cdm.pot = 4; }
        }
        break;
      case 'ghost':
        if (i.alt) ghostAb(p, 0); else if (i.skr) ghostAb(p, 1); else if (i.skf) ghostAb(p, 2);
        break;
    }
  }
}

function abilities(p) {
  const r = (k, m) => +(1 - Math.min(1, (p.cdm[k] || 0) / m)).toFixed(2);
  const q = n => +Math.min(1, p.xp / CFG.xpMax).toFixed(2);
  switch (p.char) {
    case 'steve': {
      const a = [['Skill', 'Q', p.ultT > 0 ? 0 : q()], ['Trident', 'E', r('tri', 5)], ['Spear', 'R', r('spr', 7)]];
      if (p.ultT > 0) a.push(['TNT', 'F', r('tnt', 3)], ['Potion', 'G', r('pot', 4)], [p.fmode ? 'Fin:Bolt' : 'Fin:Mace', 'V', r('fin', 6)]);
      return a;
    }
    case 'ghost': { const mx = p.maxT > 0; return [['Vengeful', 'E', mx ? 1 : +(p.gch[0] / 20).toFixed(2)], ['Howling', 'R', mx ? 1 : +(p.gch[1] / 11).toFixed(2)], ['Dive', 'F', mx ? 1 : +(p.gch[2] / 15).toFixed(2)]]; }
    case 'cuphead': return [['Charge', 'E', +(p.ch / 1.5).toFixed(2)], ['Dash', 'Shift', r('dash', p.maxT > 0 ? 2 : 4)], ['Super', 'Q', +(p.cards / 5).toFixed(2)]];
    case 'cj': return [['Tank', 'Q', p.ultT > 0 ? 0 : q()]];
  }
  return [];
}

// ============ الحلقة الرئيسية ============
function snapshot() {
  return {
    t: 's', score: R.score, fx: R.fx,
    p: R.ents.map(e => ({
      id: e.id, n: e.name, tm: e.team, c: e.char, x: Math.round(e.x), y: Math.round(e.y), w: e.w, h: e.h, d: e.dir, f: +e.face.toFixed(2),
      hp: Math.ceil(e.hp), mh: e.maxHp, xp: Math.floor(e.xp), mx: +e.maxT.toFixed(1), ul: +e.ultT.toFixed(1),
      al: e.alive, rs: Math.ceil(e.resp), wp: e.weapon, wd: e.wind ? +(1 - e.wind.t / e.wind.total).toFixed(2) : 0,
      sw: e.swing > 0 ? 1 : 0, sr: e.swingR, inv: e.inv > 0 ? 1 : 0, og: e.onGround ? 1 : 0, vx: Math.round(e.vx),
      fl: e.fly ? 1 : 0, ph: e.char === 'ghost' ? phaseOf(e) : 0, cr: e.cards, ch: +(e.ch / 1.5).toFixed(2),
      lt: e.lt ? 1 : 0, sp: e.sup ? 1 : 0, ab: abilities(e)
    })),
    b: R.projs.map(p => [Math.round(p.x), Math.round(p.y), p.r, p.color]),
    z: R.zones.map(z => [Math.round(z.x), Math.round(z.y), z.r, z.color])
  };
}
setInterval(() => {
  for (const room of rooms.values()) {
    if (room.phase !== 'playing') continue;
    R = room;
    for (const p of R.ents.slice()) { stepPlayer(p); if (R.phase !== 'playing') break; }
    if (R.phase !== 'playing') continue;
    stepProjs(); if (R.phase !== 'playing') continue;
    stepZones(); if (R.phase !== 'playing') continue;
    broadcast(R, snapshot()); R.fx = [];
  }
}, 1000 / TICK);
setInterval(() => { for (const c of clients.values()) try { c.socket.write(Buffer.from([0x89, 0])); } catch (e) {} }, 25000); // ping

// ============ الشبكة (WebSocket مكتوب يدويًا) ============
const clients = new Map();
function frame(obj) {
  const data = Buffer.from(JSON.stringify(obj)); let h;
  if (data.length < 126) h = Buffer.from([0x81, data.length]);
  else if (data.length < 65536) { h = Buffer.alloc(4); h[0] = 0x81; h[1] = 126; h.writeUInt16BE(data.length, 2); }
  else { h = Buffer.alloc(10); h[0] = 0x81; h[1] = 127; h.writeBigUInt64BE(BigInt(data.length), 2); }
  return Buffer.concat([h, data]);
}
function send(c, obj) { try { c.socket.write(frame(obj)); } catch (e) {} }
function broadcast(room, obj) { const f = frame(obj); for (const c of room.clients.values()) try { c.socket.write(f); } catch (e) {} }
function broadcastLobby(room) {
  broadcast(room, { t: 'lobby', code: room.code, phase: room.phase,
    players: [...room.clients.values()].map(c => ({ id: c.id, name: c.name, team: c.team, char: c.char })) });
}
function parseFrames(c) {
  for (;;) {
    const b = c.buf; if (b.length < 2) return;
    const op = b[0] & 15, masked = b[1] & 128; let len = b[1] & 127, off = 2;
    if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
    else if (len === 127) { if (b.length < 10) return; len = Number(b.readBigUInt64BE(2)); off = 10; }
    const ml = masked ? 4 : 0;
    if (len > 100000) { c.socket.destroy(); return; }
    if (b.length < off + ml + len) return;
    let payload = Buffer.from(b.slice(off + ml, off + ml + len));
    if (masked) { const m = b.slice(off, off + 4); for (let k = 0; k < payload.length; k++) payload[k] ^= m[k % 4]; }
    c.buf = b.slice(off + ml + len);
    if (op === 8) { c.socket.end(); return; }
    if (op === 1) { try { onMessage(c, JSON.parse(payload.toString())); } catch (e) { console.error(e); } }
  }
}
const cleanName = (n, d) => String(n || '').replace(/[<>&]/g, '').slice(0, 12) || d;
function joinRoom(c, room) {
  c.room = room;
  const a = [...room.clients.values()].filter(x => x.team === 'A').length, b = room.clients.size - a;
  c.team = a <= b ? 'A' : 'B';
  room.clients.set(c.id, c);
  send(c, { t: 'room', code: room.code });
  broadcastLobby(room);
}
function onMessage(c, m) {
  if (m.t === 'ping') return;
  if (m.t === 'create') {
    if (c.room) return;
    if (rooms.size >= 100) return send(c, { t: 'err', msg: 'السيرفر مليان، جرّب بعد شوي' });
    c.name = cleanName(m.name, c.name);
    const room = newRoom(genCode()); rooms.set(room.code, room); joinRoom(c, room); return;
  }
  if (m.t === 'join') {
    if (c.room) return;
    c.name = cleanName(m.name, c.name);
    const room = rooms.get(String(m.code || '').toUpperCase().trim());
    if (!room) return send(c, { t: 'err', msg: 'الكود غلط أو الغرفة انتهت' });
    if (room.phase !== 'lobby') return send(c, { t: 'err', msg: 'المباراة بدأت بالفعل' });
    if (room.clients.size >= CFG.maxPlayers) return send(c, { t: 'err', msg: 'الغرفة ممتلئة (4 لاعبين)' });
    joinRoom(c, room); return;
  }
  const room = c.room; if (!room) return;
  R = room;
  if (m.t === 'pick' && room.phase === 'lobby') {
    if (CHARS[m.char] && m.char !== 'dummy') c.char = m.char;
    if (m.team === 'A' || m.team === 'B') c.team = m.team;
  } else if (m.t === 'start' && room.phase === 'lobby') startMatch(room);
  else if (m.t === 'in') {
    const e = room.ents.find(x => x.id === c.id); if (!e) return;
    const b = k => !!m[k];
    e.inp = { up: b('up'), dn: b('dn'), lf: b('lf'), rt: b('rt'), jump: b('jump'), fire: b('fire'), alt: b('alt'),
      skr: b('skr'), skf: b('skf'), skg: b('skg'), ult: b('ult'), heal: b('heal'), dash: b('dash'),
      fin: b('fin'), fm: b('fm'), wp: m.wp | 0 };
    return;
  }
  broadcastLobby(room);
}
function drop(c) {
  if (!clients.has(c.id)) return;
  clients.delete(c.id);
  const room = c.room; if (!room) return;
  room.clients.delete(c.id); room.ents = room.ents.filter(e => e.id !== c.id);
  if (room.clients.size === 0) rooms.delete(room.code); else broadcastLobby(room);
}

const server = http.createServer((req, res) => {
  if (req.url === '/health') { res.writeHead(200); return res.end('ok'); }
  fs.readFile(path.join(__dirname, 'index.html'), (err, data) => {
    if (err) { res.writeHead(500); return res.end('index.html not found'); }
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' }); res.end(data);
  });
});
server.on('upgrade', (req, socket) => {
  const key = req.headers['sec-websocket-key'];
  if (!key) return socket.destroy();
  const acc = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + acc + '\r\n\r\n');
  const c = { id: ++nextId, socket, buf: Buffer.alloc(0), name: 'Player' + nextId, team: 'A', char: 'cj', room: null };
  clients.set(c.id, c);
  socket.on('data', d => { c.buf = Buffer.concat([c.buf, d]); parseFrames(c); });
  socket.on('close', () => drop(c));
  socket.on('error', () => drop(c));
  send(c, { t: 'hello', id: c.id, chars: CHARS, level: LEVEL });
});
server.listen(PORT, () => {
  console.log('\nاللعبة شغالة!  http://localhost:' + PORT);
  for (const list of Object.values(os.networkInterfaces()))
    for (const i of list) if (i.family === 'IPv4' && !i.internal) console.log('  نفس الواي فاي: http://' + i.address + ':' + PORT);
});
