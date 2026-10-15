'use strict';
const $ = s => document.querySelector(s);
const KEY = 'nemologic.v1';
const MAX_HINTS = 3;
const DIFFS = ['쉬움', '보통', '어려움'];
const LEVELS = [];
const STAGES = 20; // 별 하나(칸 수·난이도 조합)마다 들어 있는 문제 수
const GROUPS = [];
for (let s = 10; s <= 25; s++) for (let d = 0; d < 3; d++) {
  const g = { key: s + '-' + d, size: s, diff: d, levels: [] };
  for (let t = 0; t < STAGES; t++) { const L = { id: s + '-' + d + '-' + t, size: s, diff: d, stage: t }; LEVELS.push(L); g.levels.push(L); }
  GROUPS.push(g);
}

/* ---------------- 저장소 (localStorage) ---------------- */
let memoryOnly = null; // localStorage 불가 시 임시 보관
function defaults() { return { ver: 2, salt: Math.random().toString(36).slice(2), games: {}, last: null, settings: { free: { size: 15, diff: 1 } } }; }
function loadStore() {
  try {
    const o = JSON.parse(localStorage.getItem(KEY));
    if (o && o.games) { if (!o.salt) o.salt = Math.random().toString(36).slice(2);
    // 난이도 조정 이전에 시작한 퍼즐은 새 난이도로 다시 만들어지도록 진행 상황을 비움
    if ((o.ver || 0) < 2) { for (const g of Object.values(o.games)) if (!g.done) { delete g.grid; g.board = ''; g.lock = []; g.hints = 0; g.time = 0; } o.ver = 2; } o.settings = Object.assign(defaults().settings, o.settings); return o; }
  } catch (e) { memoryOnly = true; }
  return defaults();
}
let store = loadStore();
function save() { try { localStorage.setItem(KEY, JSON.stringify(store)); } catch (e) { memoryOnly = true; } }
try { navigator.storage && navigator.storage.persist && navigator.storage.persist(); } catch (e) {}

/* ---------------- 유틸 ---------------- */
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function hash(str) { let h = 2166136261; for (const ch of str) { h ^= ch.charCodeAt(0); h = Math.imul(h, 16777619); } return h >>> 0; }
function fmtTime(s) { return String(Math.floor(s / 60)).padStart(2, '0') + ':' + String(s % 60).padStart(2, '0'); }
const sameArr = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);

/* ---------------- 퍼즐 생성 / 풀이 검증 ---------------- */
function lineClue(a) {
  const c = []; let run = 0;
  for (const v of a) { if (v === 1) run++; else if (run) { c.push(run); run = 0; } }
  if (run) c.push(run);
  return c.length ? c : [0];
}
function cluesOf(grid, n) {
  const rows = [], cols = [];
  for (let i = 0; i < n; i++) {
    rows.push(lineClue(grid.slice(i * n, i * n + n)));
    cols.push(lineClue(Array.from({ length: n }, (_, y) => grid[y * n + i])));
  }
  return { rows, cols };
}
// known: -1 모름 / 0 빈칸 / 1 채움. 확정되는 칸을 반영해 돌려줌(모순이면 null)
function solveLine(blocks, known) {
  const n = known.length, k = blocks.length, memo = new Map();
  function go(i, j) {
    if (i >= n) return j === k ? { ok: true, fill: 0, empty: 0 } : { ok: false };
    const key = i * (k + 1) + j;
    let m = memo.get(key);
    if (m) return m;
    let ok = false, fill = 0, empty = 0;
    if (known[i] !== 1) {
      const s = go(i + 1, j);
      if (s.ok) { ok = true; fill |= s.fill; empty |= s.empty | (1 << i); }
    }
    if (j < k && known[i] !== 0) {
      const L = blocks[j], end = i + L;
      if (end <= n) {
        let good = true;
        for (let t = i; t < end; t++) if (known[t] === 0) { good = false; break; }
        if (good && (end === n || known[end] !== 1)) {
          const s = go(Math.min(end + 1, n), j + 1);
          if (s.ok) {
            ok = true;
            fill |= s.fill | (((1 << L) - 1) << i);
            empty |= s.empty;
            if (end < n) empty |= 1 << end;
          }
        }
      }
    }
    m = ok ? { ok, fill, empty } : { ok: false };
    memo.set(key, m);
    return m;
  }
  const r = go(0, 0);
  if (!r.ok) return null;
  const out = known.slice();
  for (let i = 0; i < n; i++) {
    const f = (r.fill >> i) & 1, e = (r.empty >> i) & 1;
    if (f && !e) out[i] = 1; else if (e && !f) out[i] = 0;
  }
  return out;
}
// 줄 단위 논리만으로 풀어 보고, 풀렸는지와 사람이 거쳐야 하는 "줄 추론 횟수(steps)"를 돌려줌
function solveStats(rows, cols, n) {
  const rb = rows.map(c => c.filter(x => x > 0)), cb = cols.map(c => c.filter(x => x > 0));
  const g = new Array(n * n).fill(-1);
  let changed = true, steps = 0, rounds = 0;
  while (changed) {
    changed = false; rounds++;
    for (let y = 0; y < n; y++) {
      const line = g.slice(y * n, y * n + n), res = solveLine(rb[y], line);
      if (!res) return { solved: false, steps, rounds };
      let c = false;
      for (let x = 0; x < n; x++) if (res[x] !== line[x]) { g[y * n + x] = res[x]; c = true; }
      if (c) { steps++; changed = true; }
    }
    for (let x = 0; x < n; x++) {
      const line = Array.from({ length: n }, (_, y) => g[y * n + x]), res = solveLine(cb[x], line);
      if (!res) return { solved: false, steps, rounds };
      let c = false;
      for (let y = 0; y < n; y++) if (res[y] !== line[y]) { g[y * n + x] = res[y]; c = true; }
      if (c) { steps++; changed = true; }
    }
  }
  return { solved: g.every(v => v !== -1), steps, rounds };
}
const lineSolvable = (rows, cols, n) => solveStats(rows, cols, n).solved;

/* ---------------- 그림 (벡터로 그려서 N×N으로 변환) ---------------- */
const RED = '#e63946', YEL = '#ffd43b', GRN = '#3bb273', BRN = '#8d5a2b', DK = '#2b2d42', PNK = '#ff8fab', ORG = '#ff9f1c', BLU = '#4d96ff', CRM = '#f6e7c8';
function starPts(cx, cy, R, r) {
  const pts = [];
  for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + i * Math.PI / 5, rr = i % 2 ? r : R; pts.push([cx + rr * Math.cos(a), cy + rr * Math.sin(a)]); }
  return pts;
}
// 색을 null로 주면 그 부분이 구멍(빈칸)이 돼서 눈·창문 같은 디테일이 생겨요
const PICS = {
  heart: { name: '하트', emoji: '❤️', draw: d => { d.c(32, 36, 21, RED); d.c(68, 36, 21, RED); d.p([[12, 46], [88, 46], [50, 90]], RED); d.c(26, 30, 6, PNK); } },
  star: { name: '별', emoji: '⭐', draw: d => { d.p(starPts(50, 54, 46, 20), YEL); d.c(40, 52, 3.5, null); d.c(60, 52, 3.5, null); d.a(50, 56, 9, 0.2, Math.PI - 0.2, 3, null); } },
  smile: { name: '웃는 얼굴', emoji: '😊', draw: d => { d.c(50, 50, 44, YEL); d.c(36, 40, 6, null); d.c(64, 40, 6, null); d.a(50, 52, 24, 0.2, Math.PI - 0.2, 6, null); } },
  house: { name: '집', emoji: '🏠', draw: d => { d.r(66, 18, 10, 24, BRN); d.r(18, 46, 64, 44, '#e9c46a'); d.p([[8, 48], [50, 12], [92, 48]], RED); d.r(42, 62, 16, 28, null); d.r(24, 56, 12, 12, null); d.r(64, 56, 12, 12, null); } },
  apple: { name: '사과', emoji: '🍎', draw: d => { d.c(36, 58, 28, RED); d.c(64, 58, 28, RED); d.r(47, 14, 6, 22, BRN); d.p([[54, 26], [78, 12], [72, 32]], GRN); d.c(30, 52, 5, PNK); } },
  moon: { name: '달', emoji: '🌙', draw: d => { d.c(48, 50, 42, YEL); d.c(66, 40, 34, null); d.c(80, 78, 5, YEL); d.c(88, 62, 3, YEL); } },
  mushroom: { name: '버섯', emoji: '🍄', draw: d => { d.e(50, 48, 44, 36, RED); d.r(0, 52, 100, 60, null); d.r(36, 50, 28, 42, CRM, 8); d.c(34, 36, 7, null); d.c(60, 28, 6, null); d.c(70, 44, 5, null); } },

  rabbit: { name: '토끼', emoji: '🐰', draw: d => { d.e(37, 24, 10, 24, '#c9a27e'); d.e(63, 24, 10, 24, '#c9a27e'); d.e(37, 26, 4, 15, PNK); d.e(63, 26, 4, 15, PNK); d.c(50, 64, 30, '#c9a27e'); d.c(40, 58, 4, null); d.c(60, 58, 4, null); d.c(50, 68, 4, PNK); d.l(50, 72, 50, 78, 2, null); } },
  duck: { name: '오리', emoji: '🦆', draw: d => { d.p([[16, 56], [6, 38], [28, 52]], YEL); d.e(46, 66, 34, 24, YEL); d.c(66, 36, 18, YEL); d.p([[80, 36], [97, 40], [80, 46]], ORG); d.c(70, 31, 3, null); d.a(42, 66, 15, 0.3, 2.8, 3, null); } },
  turtle: { name: '거북이', emoji: '🐢', draw: d => { d.p([[14, 66], [2, 74], [16, 74]], '#7bc67e'); d.e(50, 62, 36, 30, '#2d9a5a'); d.r(0, 62, 100, 60, null); d.r(14, 62, 72, 10, '#7bc67e', 4); d.r(24, 70, 13, 18, '#7bc67e', 3); d.r(62, 70, 13, 18, '#7bc67e', 3); d.c(88, 60, 10, '#7bc67e'); d.c(91, 57, 2.5, null); d.c(50, 46, 7, null); d.c(32, 56, 5, null); d.c(68, 56, 5, null); } },
  bee: { name: '꿀벌', emoji: '🐝', draw: d => { d.e(38, 30, 12, 18, '#9ad0f5', -0.4); d.e(60, 28, 12, 18, '#9ad0f5', 0.4); d.p([[24, 58], [6, 58], [24, 64]], DK); d.e(50, 58, 30, 22, YEL); d.c(82, 54, 11, DK); d.r(38, 40, 6, 36, null); d.r(54, 40, 6, 36, null); d.c(85, 51, 2, YEL); d.l(84, 44, 90, 34, 2, DK); } },
  bus: { name: '버스', emoji: '🚌', draw: d => { d.r(6, 26, 88, 54, YEL, 8); d.r(6, 60, 88, 7, ORG); d.r(12, 34, 16, 18, null); d.r(32, 34, 16, 18, null); d.r(52, 34, 16, 18, null); d.r(72, 34, 16, 18, null); d.c(26, 82, 11, DK); d.c(74, 82, 11, DK); d.c(26, 82, 4, null); d.c(74, 82, 4, null); } },
  cat: { name: '고양이', emoji: '🐱', cat: true, draw: d => { d.c(50, 58, 36, ORG); d.p([[16, 44], [20, 8], [46, 26]], ORG); d.p([[84, 44], [80, 8], [54, 26]], ORG); d.c(37, 54, 5, null); d.c(63, 54, 5, null); d.p([[46, 64], [54, 64], [50, 70]], PNK); d.l(8, 64, 32, 67, 2.5, null); d.l(8, 76, 32, 72, 2.5, null); d.l(92, 64, 68, 67, 2.5, null); d.l(92, 76, 68, 72, 2.5, null); } },
  fish: { name: '물고기', emoji: '🐟', draw: d => { d.e(42, 52, 36, 24, ORG); d.p([[70, 52], [96, 28], [96, 76]], ORG); d.p([[36, 32], [58, 32], [46, 14]], '#f77f00'); d.c(26, 46, 4, null); d.a(44, 52, 18, -0.8, 0.8, 3, null); d.p([[40, 70], [56, 70], [48, 86]], '#f77f00'); } },
  flower: { name: '꽃', emoji: '🌸', draw: d => { d.r(47, 60, 6, 40, GRN); d.e(32, 86, 14, 6, GRN, -0.5); d.e(68, 78, 14, 6, GRN, 0.5); for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + i * 2 * Math.PI / 5; d.c(50 + 24 * Math.cos(a), 38 + 24 * Math.sin(a), 16, PNK); } d.c(50, 38, 12, YEL); } },
  tree: { name: '나무', emoji: '🌳', draw: d => { d.r(43, 58, 14, 38, BRN); d.c(50, 34, 28, GRN); d.c(28, 52, 20, GRN); d.c(72, 52, 20, GRN); d.c(40, 28, 4, null); d.c(60, 40, 4, null); } },
  butterfly: { name: '나비', emoji: '🦋', draw: d => { d.e(28, 36, 24, 26, '#7b5cf0', -0.3); d.e(72, 36, 24, 26, '#7b5cf0', 0.3); d.e(34, 68, 17, 20, '#b99bff'); d.e(66, 68, 17, 20, '#b99bff'); d.c(26, 34, 6, null); d.c(74, 34, 6, null); d.r(46, 24, 8, 62, DK, 4); d.l(50, 26, 38, 8, 3, DK); d.l(50, 26, 62, 8, 3, DK); } },
  car: { name: '자동차', emoji: '🚗', draw: d => { d.r(6, 48, 88, 30, RED, 8); d.p([[24, 50], [36, 24], [68, 24], [80, 50]], RED); d.p([[31, 46], [39, 29], [48, 29], [48, 46]], null); d.p([[53, 46], [53, 29], [65, 29], [73, 46]], null); d.c(28, 78, 13, DK); d.c(72, 78, 13, DK); d.c(28, 78, 5, null); d.c(72, 78, 5, null); } },

  sun: { name: '해', emoji: '☀️', draw: d => { for (let i = 0; i < 8; i++) { const a = i * Math.PI / 4; d.l(50 + 32 * Math.cos(a), 50 + 32 * Math.sin(a), 50 + 46 * Math.cos(a), 50 + 46 * Math.sin(a), 7, ORG); } d.c(50, 50, 25, YEL); d.c(42, 46, 3, null); d.c(58, 46, 3, null); d.a(50, 52, 10, 0.2, Math.PI - 0.2, 3, null); } },
  cloud: { name: '비구름', emoji: '🌧️', draw: d => { d.c(34, 52, 20, '#9ab4d0'); d.c(58, 40, 26, '#9ab4d0'); d.c(78, 56, 16, '#9ab4d0'); d.r(18, 54, 70, 22, '#9ab4d0', 11); d.l(30, 86, 26, 96, 4, BLU); d.l(52, 84, 48, 94, 4, BLU); d.l(74, 86, 70, 96, 4, BLU); } },
  umbrella: { name: '우산', emoji: '☂️', draw: d => { d.c(50, 46, 44, RED); d.p([[50, 4], [34, 46], [66, 46]], '#ffd6a5'); d.r(0, 46, 100, 60, null); d.c(25, 46, 10, null); d.c(50, 46, 10, null); d.c(75, 46, 10, null); d.r(48, 44, 4, 44, DK); d.a(42, 88, 8, 0, Math.PI, 4, DK); } },
  gem: { name: '보석', emoji: '💎', draw: d => { d.p([[24, 28], [76, 28], [94, 44], [50, 94], [6, 44]], BLU); d.l(6, 44, 94, 44, 2, null); d.l(38, 44, 50, 94, 2, null); d.l(62, 44, 50, 94, 2, null); d.l(30, 28, 38, 44, 2, null); d.l(70, 28, 62, 44, 2, null); } },
  mug: { name: '머그컵', emoji: '☕', draw: d => { d.l(36, 6, 32, 18, 4, '#9aa3b2'); d.l(54, 6, 50, 18, 4, '#9aa3b2'); d.r(14, 26, 54, 62, BLU, 8); d.a(70, 54, 16, -1.57, 1.57, 9, BLU); d.e(41, 31, 20, 4, null); } },
  // ---- 고양이 (자세 다양) ----
  catSleep: { name: '잠자는 고양이', emoji: '😴', cat: true, draw: d => { d.e(54, 62, 38, 26, ORG); d.p([[14, 48], [16, 32], [28, 42]], ORG); d.p([[34, 42], [44, 34], [42, 50]], ORG); d.c(28, 58, 17, ORG); d.a(54, 66, 32, 0.1, Math.PI * 0.9, 9, '#f08a00'); d.a(22, 56, 4, 0.1, Math.PI - 0.1, 2.5, null); d.a(36, 56, 4, 0.1, Math.PI - 0.1, 2.5, null); d.l(52, 40, 55, 52, 3, null); d.l(64, 40, 66, 52, 3, null); d.l(76, 46, 77, 56, 3, null); } },
  catLoaf: { name: '식빵 굽는 고양이', emoji: '🍞', cat: true, draw: d => { d.r(12, 50, 76, 40, '#e0a458', 18); d.c(50, 40, 25, '#e0a458'); d.p([[28, 28], [30, 6], [44, 20]], '#e0a458'); d.p([[72, 28], [70, 6], [56, 20]], '#e0a458'); d.a(41, 40, 5, 0.1, Math.PI - 0.1, 2.5, null); d.a(59, 40, 5, 0.1, Math.PI - 0.1, 2.5, null); d.c(50, 48, 3, PNK); d.l(40, 78, 40, 90, 2.5, null); d.l(60, 78, 60, 90, 2.5, null); } },
  catSit: { name: '앉은 고양이', emoji: '🐈', cat: true, draw: d => { d.a(76, 76, 15, -0.3, 2.2, 7, '#8e8e9b'); d.e(50, 70, 26, 28, '#8e8e9b'); d.e(50, 76, 14, 18, '#d7d7e0'); d.c(50, 34, 20, '#8e8e9b'); d.p([[32, 26], [34, 4], [46, 18]], '#8e8e9b'); d.p([[68, 26], [66, 4], [54, 18]], '#8e8e9b'); d.c(43, 32, 3.5, null); d.c(57, 32, 3.5, null); d.c(50, 40, 2.5, PNK); d.l(50, 78, 50, 97, 2, null); d.e(40, 97, 10, 3, '#8e8e9b'); d.e(60, 97, 10, 3, '#8e8e9b'); } },
  catWalk: { name: '산책하는 고양이', emoji: '🐾', cat: true, draw: d => { d.l(20, 46, 8, 30, 7, ORG); d.l(8, 30, 12, 14, 7, ORG); d.r(18, 38, 56, 28, ORG, 13); d.l(26, 62, 20, 92, 8, ORG); d.l(42, 62, 46, 92, 8, ORG); d.l(58, 62, 54, 92, 8, ORG); d.l(70, 62, 78, 92, 8, ORG); d.c(80, 38, 14, ORG); d.p([[72, 30], [74, 14], [82, 26]], ORG); d.p([[84, 26], [92, 16], [93, 32]], ORG); d.c(85, 36, 2.5, null); d.l(34, 42, 34, 54, 2.5, null); d.l(46, 42, 46, 54, 2.5, null); d.l(58, 42, 58, 54, 2.5, null); } },
  catYarn: { name: '털실 갖고 노는 고양이', emoji: '🧶', cat: true, draw: d => { d.e(38, 82, 26, 17, ORG); d.l(52, 84, 66, 84, 8, ORG); d.c(40, 38, 26, ORG); d.p([[18, 28], [20, 4], [36, 18]], ORG); d.p([[62, 28], [58, 4], [44, 18]], ORG); d.c(30, 36, 5.5, null); d.c(50, 36, 5.5, null); d.c(31, 37, 2.2, DK); d.c(51, 37, 2.2, DK); d.p([[36, 46], [44, 46], [40, 52]], PNK); d.l(8, 46, 24, 48, 2, null); d.l(56, 48, 72, 46, 2, null); d.c(78, 76, 16, RED); d.l(66, 70, 90, 64, 2.5, null); d.l(64, 78, 92, 74, 2.5, null); d.l(68, 86, 86, 86, 2.5, null); d.l(64, 90, 54, 96, 2.5, RED); } },
  catMoon: { name: '달밤의 고양이', emoji: '🌕', cat: true, draw: d => { d.c(50, 50, 46, YEL); d.e(50, 80, 16, 20, null); d.c(50, 52, 12, null); d.p([[39, 46], [40, 30], [48, 40]], null); d.p([[61, 46], [60, 30], [52, 40]], null); d.a(70, 78, 13, -1.4, 1.7, 5, null); d.c(46, 52, 2, YEL); d.c(54, 52, 2, YEL); } },
  catStretch: { name: '기지개 켜는 고양이', emoji: '🙀', cat: true, draw: d => { d.l(14, 46, 6, 26, 6, ORG); d.l(6, 26, 10, 10, 6, ORG); d.e(46, 56, 32, 14, ORG, 0.35); d.l(24, 46, 18, 90, 8, ORG); d.l(36, 52, 34, 92, 8, ORG); d.l(64, 66, 76, 94, 7, ORG); d.l(74, 68, 90, 92, 7, ORG); d.c(80, 76, 12, ORG); d.p([[72, 68], [74, 54], [83, 65]], ORG); d.p([[85, 66], [94, 58], [94, 72]], ORG); d.c(84, 74, 2.5, null); d.l(40, 46, 44, 56, 2.5, null); d.l(52, 50, 56, 60, 2.5, null); } },
  // ---- 동물 ----
  pig: { name: '돼지', emoji: '🐷', draw: d => { d.p([[18, 34], [20, 8], [40, 24]], '#ff6f91'); d.p([[82, 34], [80, 8], [60, 24]], '#ff6f91'); d.c(50, 54, 38, PNK); d.e(50, 64, 17, 12, '#ff6f91'); d.c(44, 64, 3, null); d.c(56, 64, 3, null); d.c(36, 46, 4, null); d.c(64, 46, 4, null); } },
  frog: { name: '개구리', emoji: '🐸', draw: d => { d.e(50, 64, 42, 30, GRN); d.c(28, 32, 14, GRN); d.c(72, 32, 14, GRN); d.c(28, 32, 7, null); d.c(72, 32, 7, null); d.c(28, 33, 3, DK); d.c(72, 33, 3, DK); d.a(50, 60, 27, 0.2, Math.PI - 0.2, 3, null); d.c(45, 48, 2, null); d.c(55, 48, 2, null); } },
  bird: { name: '작은 새', emoji: '🐦', draw: d => { d.p([[16, 52], [0, 40], [2, 64], [18, 64]], '#2f6fd8'); d.l(42, 84, 42, 97, 3, ORG); d.l(58, 84, 58, 97, 3, ORG); d.e(46, 60, 34, 26, BLU); d.c(76, 38, 16, BLU); d.p([[88, 36], [100, 42], [88, 46]], ORG); d.c(80, 34, 3, null); d.e(40, 62, 18, 10, '#2f6fd8', -0.3); d.l(30, 64, 50, 56, 2, null); } },
  dog: { name: '강아지', emoji: '🐶', draw: d => { d.e(21, 52, 12, 27, BRN, 0.2); d.e(79, 52, 12, 27, BRN, -0.2); d.c(50, 52, 30, '#c9a27e'); d.c(40, 46, 4, null); d.c(60, 46, 4, null); d.e(50, 64, 14, 10, CRM); d.c(50, 58, 5, DK); d.e(50, 78, 6, 9, PNK); d.l(50, 62, 50, 70, 2, null); } },
  panda: { name: '판다', emoji: '🐼', draw: d => { d.c(24, 22, 13, DK); d.c(76, 22, 13, DK); d.c(50, 54, 36, '#ececec'); d.e(35, 48, 9, 12, null, 0.4); d.e(65, 48, 9, 12, null, -0.4); d.c(36, 49, 3, DK); d.c(64, 49, 3, DK); d.c(50, 62, 5, DK); d.a(50, 66, 7, 0.2, Math.PI - 0.2, 2.5, null); } },
  snail: { name: '달팽이', emoji: '🐌', draw: d => { d.r(4, 68, 92, 18, '#b5d97c', 9); d.r(78, 42, 13, 38, '#b5d97c', 6); d.l(82, 46, 76, 24, 3, '#b5d97c'); d.l(88, 46, 94, 24, 3, '#b5d97c'); d.c(76, 22, 3.5, '#b5d97c'); d.c(94, 22, 3.5, '#b5d97c'); d.c(40, 50, 28, '#c9884a'); d.a(40, 50, 17, 0, 5, 3.5, null); d.a(40, 50, 8, 0.6, 5.6, 3, null); } },
  elephant: { name: '코끼리', emoji: '🐘', draw: d => { d.e(58, 54, 34, 28, '#9aa3b2'); d.r(32, 74, 11, 24, '#9aa3b2', 3); d.r(46, 76, 11, 22, '#9aa3b2', 3); d.r(66, 74, 11, 24, '#9aa3b2', 3); d.r(79, 76, 11, 22, '#9aa3b2', 3); d.l(92, 48, 96, 70, 3, '#7a8394'); d.c(28, 46, 21, '#9aa3b2'); d.l(16, 56, 10, 82, 11, '#9aa3b2'); d.l(10, 82, 20, 92, 9, '#9aa3b2'); d.e(40, 44, 13, 19, '#7a8394'); d.c(21, 40, 2.5, null); d.p([[24, 60], [12, 68], [18, 60]], '#f4f1de'); } },
  giraffe: { name: '기린', emoji: '🦒', draw: d => { d.l(26, 66, 16, 82, 3, YEL); d.r(30, 82, 6, 16, YEL); d.r(40, 84, 6, 14, YEL); d.r(56, 84, 6, 14, YEL); d.r(66, 82, 6, 16, YEL); d.e(50, 72, 25, 16, YEL); d.p([[56, 72], [70, 72], [74, 26], [62, 26]], YEL); d.e(72, 20, 14, 9, YEL, -0.2); d.l(66, 12, 64, 3, 2.5, BRN); d.l(77, 12, 79, 3, 2.5, BRN); d.p([[60, 20], [52, 14], [60, 12]], YEL); d.c(77, 18, 2, null); d.c(44, 68, 3.5, null); d.c(58, 76, 3.5, null); d.c(36, 74, 3, null); d.c(67, 42, 2.8, null); d.c(69, 56, 2.8, null); d.c(66, 66, 2.5, null); } },
  lion: { name: '사자', emoji: '🦁', draw: d => { d.c(50, 52, 46, '#c0752b'); d.c(26, 18, 9, '#c0752b'); d.c(74, 18, 9, '#c0752b'); d.c(50, 55, 28, '#f3b65a'); d.c(40, 48, 4, null); d.c(60, 48, 4, null); d.p([[44, 58], [56, 58], [50, 65]], DK); d.l(50, 65, 50, 71, 2.5, null); d.a(44, 71, 6, 0, Math.PI, 2.5, null); d.a(56, 71, 6, 0, Math.PI, 2.5, null); d.l(10, 52, 20, 52, 2.5, null); d.l(80, 52, 90, 52, 2.5, null); } },
  bicycle: { name: '자전거', emoji: '🚲', draw: d => { d.a(22, 68, 19, 0, 7, 6, DK); d.a(78, 68, 19, 0, 7, 6, DK); d.l(22, 68, 42, 40, 5, RED); d.l(42, 40, 66, 40, 5, RED); d.l(66, 40, 78, 68, 5, RED); d.l(42, 40, 50, 68, 5, RED); d.l(22, 68, 50, 68, 5, RED); d.l(66, 40, 50, 68, 5, RED); d.l(36, 34, 50, 34, 6, DK); d.l(66, 40, 60, 24, 5, DK); d.l(60, 24, 74, 22, 5, DK); d.c(50, 68, 5, DK); } },
  balloon: { name: '열기구', emoji: '🎈', draw: d => { d.c(50, 36, 34, RED); d.p([[20, 50], [80, 50], [60, 74], [40, 74]], RED); d.e(50, 36, 23, 34, null); d.e(50, 36, 13, 34, YEL); d.l(40, 74, 42, 82, 3, DK); d.l(60, 74, 58, 82, 3, DK); d.r(38, 80, 24, 16, BRN, 3); d.l(42, 88, 58, 88, 2.5, null); } },
  ferris: { name: '관람차', emoji: '🎡', draw: d => { d.l(50, 44, 26, 96, 6, DK); d.l(50, 44, 74, 96, 6, DK); d.r(8, 94, 84, 6, GRN); d.a(50, 44, 34, 0, 7, 6, BLU); d.a(50, 44, 15, 0, 7, 4, BLU); for (let k = 0; k < 4; k++) { const a = k * Math.PI / 4; d.l(50 + 34 * Math.cos(a), 44 + 34 * Math.sin(a), 50 - 34 * Math.cos(a), 44 - 34 * Math.sin(a), 4, BLU); } for (let k = 0; k < 8; k++) { const a = k * Math.PI / 4 + 0.4; d.c(50 + 34 * Math.cos(a), 44 + 34 * Math.sin(a), 6, k % 2 ? YEL : PNK); } d.c(50, 44, 6, RED); } },
  octopus: { name: '문어', emoji: '🐙', draw: d => { const P = '#b565d9'; for (let i = 0; i < 6; i++) { const x = 24 + i * 10.4, e = x + (i % 2 ? 5 : -5); d.l(x, 54, e, 84, 8, P); d.c(e, 87, 4.5, P); } d.c(50, 36, 29, P); d.c(40, 32, 6, null); d.c(60, 32, 6, null); d.c(41, 33, 2.5, DK); d.c(61, 33, 2.5, DK); d.c(50, 14, 2.5, null); d.c(34, 20, 2, null); d.c(66, 20, 2, null); } },
  crab: { name: '게', emoji: '🦀', draw: d => { d.l(24, 62, 8, 76, 5, RED); d.l(26, 68, 12, 90, 5, RED); d.l(76, 62, 92, 76, 5, RED); d.l(74, 68, 88, 90, 5, RED); d.e(50, 58, 32, 20, RED); d.l(40, 42, 40, 30, 5, RED); d.l(60, 42, 60, 30, 5, RED); d.c(40, 27, 6, RED); d.c(60, 27, 6, RED); d.c(40, 27, 3, null); d.c(60, 27, 3, null); d.l(22, 50, 10, 34, 6, RED); d.l(78, 50, 90, 34, 6, RED); d.c(10, 26, 13, RED); d.c(90, 26, 13, RED); d.p([[10, 28], [2, 12], [18, 14]], null); d.p([[90, 28], [82, 14], [98, 12]], null); d.a(50, 56, 12, 0.3, Math.PI - 0.3, 2.5, null); } },
  palm: { name: '야자수 섬', emoji: '🏝️', draw: d => { d.c(18, 20, 11, YEL); d.r(0, 80, 100, 20, BLU); d.e(50, 82, 34, 10, '#e9c46a'); d.l(48, 82, 52, 50, 7, BRN); d.l(52, 50, 58, 30, 7, BRN); d.l(58, 30, 30, 22, 6, GRN); d.l(58, 30, 34, 42, 6, GRN); d.l(58, 30, 88, 22, 6, GRN); d.l(58, 30, 84, 44, 6, GRN); d.l(58, 30, 58, 8, 6, GRN); d.c(53, 37, 4, BRN); d.c(63, 37, 4, BRN); d.a(22, 90, 9, Math.PI, 2 * Math.PI, 2.5, null); d.a(78, 90, 9, Math.PI, 2 * Math.PI, 2.5, null); } },
  train: { name: '기차', emoji: '🚂', draw: d => { d.c(24, 10, 6, '#cbd5e1'); d.c(34, 4, 5, '#cbd5e1'); d.r(14, 20, 14, 8, DK); d.r(18, 26, 8, 16, DK); d.r(8, 40, 52, 34, '#3b4a6b', 6); d.r(58, 28, 34, 46, RED, 3); d.r(54, 22, 42, 8, DK); d.r(66, 36, 18, 14, null); d.c(14, 52, 4, null); d.p([[8, 74], [0, 92], [16, 92]], DK); d.c(24, 82, 12, DK); d.c(50, 82, 10, DK); d.c(78, 82, 12, DK); d.c(24, 82, 4, null); d.c(50, 82, 3.5, null); d.c(78, 82, 4, null); d.r(0, 95, 100, 5, DK); } },
  fox: { name: '여우', emoji: '🦊', draw: d => { d.p([[8, 14], [32, 34], [68, 34], [92, 14], [86, 60], [50, 94], [14, 60]], ORG); d.p([[16, 60], [50, 94], [84, 60], [70, 54], [50, 70], [30, 54]], '#f4f1de'); d.p([[16, 22], [26, 34], [18, 46]], DK); d.p([[84, 22], [74, 34], [82, 46]], DK); d.p([[19, 30], [25, 38], [20, 42]], null); d.p([[81, 30], [75, 38], [80, 42]], null); d.e(34, 50, 5, 3, null, 0.3); d.e(66, 50, 5, 3, null, -0.3); d.c(50, 90, 5, DK); } },  owl: { name: '부엉이', emoji: '🦉', draw: d => { d.e(50, 56, 36, 40, BRN); d.p([[18, 36], [20, 6], [42, 22]], BRN); d.p([[82, 36], [80, 6], [58, 22]], BRN); d.e(16, 62, 8, 22, '#6b4423', 0.2); d.e(84, 62, 8, 22, '#6b4423', -0.2); d.c(36, 44, 14, null); d.c(64, 44, 14, null); d.c(36, 44, 6, DK); d.c(64, 44, 6, DK); d.p([[44, 56], [56, 56], [50, 68]], ORG); for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) d.c(38 + j * 12, 74 + i * 7 - (j === 1 ? 2 : 0), 2.2, null); } },
  boat: { name: '돛단배', emoji: '⛵', draw: d => { d.p([[8, 72], [92, 72], [78, 92], [22, 92]], BRN); d.r(48, 8, 4, 64, DK); d.p([[53, 10], [53, 66], [86, 66]], RED); d.p([[46, 22], [46, 66], [16, 66]], BLU); d.c(36, 82, 3, null); d.c(50, 82, 3, null); d.c(64, 82, 3, null); d.p([[52, 8], [64, 12], [52, 16]], YEL); } },
  castle: { name: '성', emoji: '🏰', draw: d => { d.r(14, 42, 72, 48, '#a8a8b3'); d.r(8, 30, 24, 60, '#8e8e9b'); d.r(68, 30, 24, 60, '#8e8e9b'); d.r(38, 24, 24, 66, '#a8a8b3'); d.r(15, 30, 8, 6, null); d.r(77, 30, 8, 6, null); d.r(46, 24, 8, 6, null); d.r(49, 4, 2, 20, DK); d.p([[51, 4], [66, 9], [51, 14]], RED); d.r(42, 64, 16, 26, null); d.c(50, 64, 8, null); d.r(17, 48, 6, 10, null); d.r(77, 48, 6, 10, null); } },
  icecream: { name: '아이스크림', emoji: '🍦', draw: d => { d.p([[28, 52], [72, 52], [50, 96]], '#e0a458'); d.c(50, 42, 24, PNK); d.c(50, 24, 17, '#ffe6a7'); d.c(52, 7, 6, RED); d.l(38, 58, 54, 84, 2, null); d.l(62, 58, 46, 84, 2, null); d.l(34, 62, 66, 62, 2, null); } },
  rocket: { name: '로켓', emoji: '🚀', draw: d => { d.e(50, 46, 19, 40, '#dfe3ea'); d.p([[34, 20], [50, 2], [66, 20]], RED); d.e(50, 22, 16, 18, RED); d.p([[34, 56], [14, 86], [36, 78]], RED); d.p([[66, 56], [86, 86], [64, 78]], RED); d.p([[40, 84], [60, 84], [50, 100]], ORG); d.c(50, 46, 9, null); d.c(50, 46, 4, BLU); d.r(42, 74, 16, 10, '#9aa3b2'); } },
  penguin: { name: '펭귄', emoji: '🐧', draw: d => { d.e(18, 60, 7, 20, DK, 0.3); d.e(82, 60, 7, 20, DK, -0.3); d.e(38, 94, 11, 5, ORG); d.e(62, 94, 11, 5, ORG); d.e(50, 54, 30, 40, DK); d.e(50, 64, 20, 28, '#f5f5f5'); d.c(41, 36, 4, null); d.c(59, 36, 4, null); d.p([[44, 42], [56, 42], [50, 50]], ORG); } },
  whale: { name: '고래', emoji: '🐳', draw: d => { d.e(44, 58, 40, 26, BLU); d.p([[74, 54], [92, 30], [98, 42], [88, 60], [98, 78], [92, 86], [72, 68]], BLU); d.e(40, 70, 26, 10, '#a8d0ff'); d.c(24, 52, 3, null); d.l(40, 32, 40, 14, 4, '#9ad0f5'); d.l(40, 14, 28, 8, 4, '#9ad0f5'); d.l(40, 14, 52, 8, 4, '#9ad0f5'); } },
  lighthouse: { name: '등대', emoji: '🗼', draw: d => { d.e(50, 95, 42, 6, '#6b7280'); d.p([[38, 30], [62, 30], [70, 92], [30, 92]], RED); d.p([[34, 52], [66, 52], [68, 64], [32, 64]], '#f4f1de'); d.r(36, 18, 28, 12, DK); d.p([[32, 18], [68, 18], [50, 4]], RED); d.l(30, 24, 8, 16, 3, YEL); d.l(70, 24, 92, 16, 3, YEL); d.r(46, 36, 8, 10, null); d.r(44, 76, 12, 16, null); } },
  windmill: { name: '풍차', emoji: '🌬️', draw: d => { d.p([[40, 40], [60, 40], [68, 94], [32, 94]], '#c9a27e'); const bl = a => { const c = Math.cos(a), s = Math.sin(a); d.p([[50 + 6 * c - 4 * s, 36 + 6 * s + 4 * c], [50 + 36 * c - 4 * s, 36 + 36 * s + 4 * c], [50 + 36 * c - 10 * s, 36 + 36 * s + 10 * c], [50 + 6 * c - 10 * s, 36 + 6 * s + 10 * c]], '#d8c690'); }; for (let k = 0; k < 4; k++) bl(0.6 + k * Math.PI / 2); d.c(50, 36, 5, BRN); d.r(45, 76, 10, 18, null); d.c(50, 58, 4, null); } },
  robot: { name: '로봇', emoji: '🤖', draw: d => { d.l(50, 14, 50, 5, 3, DK); d.c(50, 5, 4, RED); d.r(26, 14, 48, 34, '#9aa3b2', 6); d.c(38, 30, 6, null); d.c(62, 30, 6, null); d.r(38, 40, 24, 4, null); d.r(22, 52, 56, 34, '#7a8394', 6); d.r(8, 54, 12, 28, '#9aa3b2', 5); d.r(80, 54, 12, 28, '#9aa3b2', 5); d.r(30, 86, 14, 12, DK); d.r(56, 86, 14, 12, DK); d.c(50, 68, 8, null); d.c(50, 68, 3, RED); } },
  cactus: { name: '선인장', emoji: '🌵', draw: d => { d.r(38, 14, 24, 72, GRN, 12); d.r(12, 48, 30, 10, GRN, 5); d.r(12, 30, 12, 28, GRN, 6); d.r(58, 40, 30, 10, GRN, 5); d.r(76, 24, 12, 26, GRN, 6); d.r(26, 82, 48, 16, '#c1666b', 3); d.l(46, 24, 46, 70, 2, null); d.l(54, 28, 54, 66, 2, null); d.c(50, 10, 5, PNK); } }
};
// 난이도 = 그림의 복잡도(그 칸 수에서 힌트 덩어리가 얼마나 많은지). 가장 단순한 그림은 빼고 나머지를 3등분
const SKIP_SIMPLEST = 0.4;
const POOLS = {};
function pools(n) {
  if (POOLS[n]) return POOLS[n];
  const info = k => {
    const { alpha, hole } = rasterize(k, n, false);
    const sil = alpha.reduce((s, a) => s + (a >= 0.5 ? 1 : 0), 0);
    const cnt = thr => Array.from(alpha, (a, i) => (a >= 0.5 && hole[i] < thr ? 1 : 0));
    const strict = cnt(HOLE_THR[2]).reduce((s, v) => s + v, 0);
    const { rows, cols } = cluesOf(cnt(HOLE_THR[1]), n);
    return { k, keep: strict >= sil * 0.6, s: rows.concat(cols).reduce((s, c) => s + c.length, 0) };
  };
  // 작은 칸에서 디테일 때문에 모양이 무너지는 그림은 제외
  const all = Object.keys(PICS).map(info).filter(o => o.keep).sort((a, b) => a.s - b.s || (a.k < b.k ? -1 : 1)).map(o => o.k);
  let ranked = all.slice(Math.round(all.length * SKIP_SIMPLEST));
  if (ranked.length < 3 * STAGES) ranked = all;
  const third = Math.ceil(ranked.length / 3);
  return (POOLS[n] = [ranked.slice(0, third), ranked.slice(third, third * 2), ranked.slice(third * 2)]);
}
// skipHoles: 구멍(null) 동작을 무시하고 겉모습(실루엣)만 그림
function makeDrawer(ctx, skipHoles) {
  const set = col => {
    if (col === null) { ctx.globalCompositeOperation = 'destination-out'; ctx.fillStyle = ctx.strokeStyle = '#000'; }
    else { ctx.globalCompositeOperation = 'source-over'; ctx.fillStyle = ctx.strokeStyle = col; }
  };
  const d = {
    c(x, y, r, col) { set(col); ctx.beginPath(); ctx.arc(x, y, r, 0, 7); ctx.fill(); },
    e(x, y, rx, ry, col, rot = 0) { set(col); ctx.beginPath(); ctx.ellipse(x, y, rx, ry, rot, 0, 7); ctx.fill(); },
    r(x, y, w, h, col, rad = 0) { set(col); ctx.beginPath(); if (ctx.roundRect) ctx.roundRect(x, y, w, h, rad); else ctx.rect(x, y, w, h); ctx.fill(); },
    p(pts, col) { set(col); ctx.beginPath(); pts.forEach(([x, y], i) => (i ? ctx.lineTo(x, y) : ctx.moveTo(x, y))); ctx.closePath(); ctx.fill(); },
    l(x1, y1, x2, y2, w, col) { set(col); ctx.lineWidth = w; ctx.lineCap = 'round'; ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); },
    a(x, y, r, a0, a1, w, col) { set(col); ctx.lineWidth = w; ctx.lineCap = 'round'; ctx.beginPath(); ctx.arc(x, y, r, a0, a1); ctx.stroke(); }
  };
  if (!skipHoles) return d;
  // 색 인자의 위치가 함수마다 달라서 구멍(null) 호출만 걸러냄
  const colAt = { c: 4, e: 5, r: 5, p: 2, l: 6, a: 7 };
  const out = {};
  for (const k in d) out[k] = (...args) => { if (args[colAt[k] - 1] === null) return; d[k](...args); };
  return out;
}
// 큰 캔버스에 그린 뒤 칸마다 덮인 비율(alpha)·구멍 비율(hole)·평균 색을 구함
function rasterize(key, n, flip) {
  const S = 8, R = n * S;
  const render = skipHoles => {
    const cv = document.createElement('canvas');
    cv.width = cv.height = R;
    const ctx = cv.getContext('2d', { willReadFrequently: true });
    ctx.scale(R / 100, R / 100);
    if (flip) { ctx.translate(100, 0); ctx.scale(-1, 1); }
    PICS[key].draw(makeDrawer(ctx, skipHoles));
    return ctx.getImageData(0, 0, R, R).data;
  };
  const data = render(false), sil = render(true);
  const alpha = new Float32Array(n * n), hole = new Float32Array(n * n), color = [];
  for (let cy = 0; cy < n; cy++) for (let cx = 0; cx < n; cx++) {
    let sa = 0, ss = 0, hp = 0, r = 0, g = 0, b = 0;
    for (let y = 0; y < S; y++) for (let x = 0; x < S; x++) {
      const q = ((cy * S + y) * R + cx * S + x) * 4, a = data[q + 3] / 255, s = sil[q + 3] / 255;
      sa += a; ss += s; r += data[q] * a; g += data[q + 1] * a; b += data[q + 2] * a;
      if (s > 0.5 && a < 0.5) hp++;
    }
    const i = cy * n + cx;
    alpha[i] = ss / (S * S); // 구멍을 뺀 겉모습 기준
    hole[i] = hp / (S * S);
    color[i] = sa > 0 ? `rgb(${Math.round(r / sa)},${Math.round(g / sa)},${Math.round(b / sa)})` : '#444';
  }
  return { alpha, hole, color };
}
// 난이도가 높을수록 작은 구멍(눈·창문·무늬)도 칸에 반영 → 힌트가 잘게 쪼개짐
const HOLE_THR = [0.15, 0.1, 0.06];
// 그림을 조금 흐트러뜨려 힌트를 잘게 쪼갬(그림이 조금 깨져도 퍼즐이 어려워지도록)
const NOISE = [0.25, 0.4, 0.55];   // 그림 안쪽 칸을 비우는 확률
const SPECK = [0.03, 0.08, 0.14];     // 그림 가장자리 바깥에 점을 찍는 확률
// 줄 추론 횟수 순위(0~1)에서 몇 번째 후보를 고를지: 쉬움은 낮게, 어려움은 가장 어려운 것
const PICK_Q = [0.45, 0.75, 1];
// 후보를 여러 개 만들어 논리만으로 풀리는 것 중 난이도 목표에 맞는 것을 선택
// (큰 판이나 어려운 설정에서 풀리는 후보가 없으면 흐트러뜨리는 정도를 줄여 다시 시도)
function makePicture(key, n, flip, diff = 1, seed = 1) {
  if (key === 'random') return makeRandom(n, diff, seed);
  const { alpha, hole, color } = rasterize(key, n, flip);
  const base = Array.from(alpha, (a, i) => (a >= 0.5 && hole[i] < HOLE_THR[diff] ? 1 : 0));
  const tries = n <= 15 ? 50 : 30;
  let first = null;
  for (const scale of [1, 0.75, 0.55, 0.35, 0.15, 0]) {
    const cands = [];
    for (let k = 0; k < tries; k++) {
      const r = rng(seed + k * 7919), grid = base.slice();
      for (let i = 0; i < n * n; i++) {
        const x = i % n, y = (i / n) | 0;
        const nb = (x > 0 && base[i - 1]) + (x < n - 1 && base[i + 1]) + (y > 0 && base[i - n]) + (y < n - 1 && base[i + n]);
        if (base[i]) { if (nb >= 2 && r() < NOISE[diff] * scale) grid[i] = 0; }
        else if (nb >= 1 && r() < SPECK[diff] * scale) grid[i] = 1;
      }
      const { rows, cols } = cluesOf(grid, n), st = solveStats(rows, cols, n);
      const cand = { grid, rows, cols, color, steps: st.steps };
      if (!first) first = cand;
      if (st.solved) cands.push(cand);
      if (scale === 0) break; // 흐트러뜨림이 없으면 후보가 하나뿐
    }
    if (cands.length >= 3 || (scale === 0 && cands.length)) {
      cands.sort((a, b) => a.steps - b.steps);
      return cands[Math.min(cands.length - 1, Math.round((cands.length - 1) * PICK_Q[diff]))];
    }
  }
  return first;
}
/* ---------------- 랜덤 무늬 (그림이 아니라 무작위 패턴. 더 어려움) ---------------- */
const RANDOM_INFO = { name: '랜덤 무늬', emoji: '🎲' };
const picInfo = k => (k === 'random' ? RANDOM_INFO : PICS[k]);
const P_RANDOM = [0.25, 0.4, 0.6];                         // 이 확률로 그림 대신 랜덤 무늬가 나옴
const RAND_PARAM = [{ blur: 2, dens: 0.6 }, { blur: 1, dens: 0.55 }, { blur: 0, dens: 0.5 }];
function noiseGrid(n, blur, dens, seed) {
  const r = rng(seed);
  let g = Array.from({ length: n * n }, () => r());
  for (let p = 0; p < blur; p++) {
    const h = new Array(n * n);
    for (let y = 0; y < n; y++) for (let x = 0; x < n; x++) {
      let s = 0, c = 0;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
        const yy = y + dy, xx = x + dx;
        if (yy >= 0 && yy < n && xx >= 0 && xx < n) { s += g[yy * n + xx]; c++; }
      }
      h[y * n + x] = s / c;
    }
    g = h;
  }
  const th = [...g].sort((a, b) => a - b)[Math.floor(n * n * (1 - dens))];
  return g.map(v => (v >= th ? 1 : 0));
}
// 무지개 빛 대각선 그라데이션
function randomColors(n, seed) {
  const h0 = seed % 360;
  return Array.from({ length: n * n }, (_, i) => `hsl(${(h0 + ((i % n) + ((i / n) | 0)) * 300 / (2 * n)) % 360},75%,58%)`);
}
function makeRandom(n, diff, seed) {
  const { blur, dens } = RAND_PARAM[diff], color = randomColors(n, seed), tries = n <= 15 ? 60 : 30;
  let first = null;
  for (const extra of [0, 1, 2, 3]) {
    const cands = [];
    for (let k = 0; k < tries; k++) {
      const grid = noiseGrid(n, blur + extra, dens, seed + k * 7919), { rows, cols } = cluesOf(grid, n), st = solveStats(rows, cols, n);
      const cand = { grid, rows, cols, color, steps: st.steps };
      if (!first) first = cand;
      if (st.solved) cands.push(cand);
    }
    if (cands.length >= 3 || (extra === 3 && cands.length)) {
      cands.sort((a, b) => a.steps - b.steps);
      return cands[Math.min(cands.length - 1, Math.round((cands.length - 1) * PICK_Q[diff]))];
    }
  }
  return first;
}
// 그림 고르기: 사람마다 다른 순서로 섞되 고양이는 3배 잘 뽑히게 함. 같은 칸 수·난이도 안에서는 그림이 겹치지 않음
function shuffledPool(pool, seed) {
  const r = rng(seed);
  return pool.map(k => ({ k, s: Math.pow(r(), 1 / (PICS[k].cat ? 3 : 1)) })).sort((a, b) => b.s - a.s).map(o => o.k);
}
function pickPic(rec) {
  if (rng(hash(store.salt + ':r:' + (rec.free ? rec.seed : rec.id)))() < P_RANDOM[rec.diff]) return { pic: 'random', flip: false };
  const pool = pools(rec.size)[rec.diff];
  if (rec.free) return { pic: shuffledPool(pool, rec.seed)[0], flip: !!((rec.seed >>> 8) & 1) };
  const order = shuffledPool(pool, hash(store.salt + ':' + rec.size + '-' + rec.diff));
  return { pic: order[rec.stage % order.length], flip: rng(hash(store.salt + rec.id))() < 0.5 };
}
// 저장된 그림(rec.grid)이 있으면 그대로 사용해서 진행 상황과 어긋나지 않게 함
const picColors = rec => (rec.pic === 'random' ? randomColors(rec.size, rec.seed) : rasterize(rec.pic, rec.size, rec.flip).color);
function buildPuzzle(rec) {
  const n = rec.size;
  if (rec.grid && rec.grid.length === n * n) {
    const grid = Array.from(rec.grid, Number);
    return Object.assign({ grid, color: picColors(rec) }, cluesOf(grid, n));
  }
  const p = makePicture(rec.pic, n, rec.flip, rec.diff, rec.seed);
  rec.grid = p.grid.join('');
  return p;
}

/* ---------------- 다이얼로그 ---------------- */
const dlg = $('#dlg');
function showDialog({ title, html = '', buttons = [] }) {
  dlg.innerHTML = `<form method="dialog"><h2>${title}</h2><div class="dbody">${html}</div><div class="dbtns"></div></form>`;
  const box = dlg.querySelector('.dbtns');
  buttons.forEach(b => {
    const el = document.createElement('button');
    el.type = 'button'; el.textContent = b.label; el.className = b.cls || '';
    el.onclick = () => { if (!b.keep) dlg.close(); if (b.fn) b.fn(); };
    box.appendChild(el);
  });
  if (!dlg.open) dlg.showModal();
}

/* ---------------- 홈 ---------------- */
const label = r => (r.free ? '직접 설정 · ' : '') + `${r.size}×${r.size} ${DIFFS[r.diff]}${!r.free && r.stage != null ? ' ' + (r.stage + 1) : ''}`;
const hasMarks = r => r.board && /[12]/.test(r.board);
const pct = r => r.total ? Math.min(99, Math.round((r.board.split('1').length - 1) / r.total * 100)) : 0;
function levelRec(L) {
  return store.games[L.id] || { id: L.id, size: L.size, diff: L.diff, seed: hash('nemo:' + L.id), stage: L.stage, free: false, board: '', lock: [], hints: 0, time: 0, done: false, total: 0 };
}
const isDone = L => !!(store.games[L.id] && store.games[L.id].done);
function nextLevel() { return LEVELS.find(L => !isDone(L)); }
// 방금 푼 문제 다음 순서의 안 푼 문제(없으면 처음부터 찾음)
function nextAfter(L) { return LEVELS.slice(LEVELS.indexOf(L) + 1).find(x => !isDone(x)) || nextLevel(); }

function renderHome() {
  // 이어하기 배너
  const last = store.last && store.games[store.last];
  let b = '';
  if (last && !last.done) {
    b = bannerHtml('이어서 하기', `${label(last)} · ${hasMarks(last) ? '진행 ' + pct(last) + '% · ' : ''}${fmtTime(last.time)}`, store.last);
  } else {
    const nx = nextLevel();
    if (nx) b = bannerHtml(Object.values(store.games).some(g => g.done) ? '다음 문제' : '시작하기', label(nx), nx.id);
  }
  $('#resume').innerHTML = b;

  // 코스: 별 하나 = 칸 수·난이도 한 조합(문제 STAGES개)
  const doneCnt = LEVELS.filter(isDone).length;
  const starCnt = GROUPS.filter(g => g.levels.every(isDone)).length;
  const cur = nextLevel(), curKey = cur && cur.size + '-' + cur.diff;
  let html = `<p class="sum">별 ${starCnt} / ${GROUPS.length} · 문제 ${doneCnt} / ${LEVELS.length}</p><div class="path">`;
  let lastSize = 0;
  GROUPS.forEach((g, idx) => {
    if (g.size !== lastSize) { lastSize = g.size; html += `<div class="chip">${g.size} × ${g.size}</div>`; }
    const d = g.levels.filter(isDone).length;
    const st = d === STAGES ? 'done' : d > 0 || g.levels.some(L => store.games[L.id] && hasMarks(store.games[L.id])) ? 'part' : '';
    const isCur = g.key === curKey;
    html += `<button class="node ${st} ${isCur ? 'cur' : ''}" data-group="${g.key}" style="--off:${Math.round(Math.sin(idx * 1.1) * 54)}px">` +
      `<span class="dot">${isCur && st !== 'done' ? '▶' : '★'}</span><span class="lab">${DIFFS[g.diff]} · ${d}/${STAGES}</span></button>`;
  });
  $('#tabCourse').innerHTML = html + '</div>';
  const curEl = $('#tabCourse .node.cur');
  if (curEl && !$('#home').hidden) setTimeout(() => curEl.scrollIntoView({ block: 'center' }), 0);

  // 직접 설정
  const f = store.settings.free;
  $('#fsize').value = f.size; $('#fsizeOut').textContent = `${f.size} × ${f.size}`;
  document.querySelectorAll('#fdiff button').forEach(btn => btn.classList.toggle('on', +btn.dataset.d === f.diff));
}
// 도감: 완성한 그림을 색깔 그대로 모아서 보여줌
function renderAlbum() {
  const done = Object.values(store.games).filter(r => r.done && picInfo(r.pic) && r.grid);
  if (!done.length) {
    $('#tabAlbum').innerHTML = '<p class="sum">아직 완성한 그림이 없어요.<br>퍼즐을 풀면 여기에 그림이 모여요!</p>';
    return;
  }
  $('#tabAlbum').innerHTML = `<div class="album">${done.map(r =>
    `<div class="pcard"><canvas data-id="${r.id}" width="${r.size * 4}" height="${r.size * 4}"></canvas><b>${picInfo(r.pic).emoji} ${picInfo(r.pic).name}</b><small>${label(r)}</small></div>`).join('')}</div>`;
  $('#tabAlbum').querySelectorAll('canvas').forEach(cv => {
    const r = store.games[cv.dataset.id], color = picColors(r), ctx = cv.getContext('2d');
    for (let i = 0; i < r.size * r.size; i++) if (r.grid[i] === '1') {
      ctx.fillStyle = color[i];
      ctx.fillRect((i % r.size) * 4, ((i / r.size) | 0) * 4, 4, 4);
    }
  });
}
function bannerHtml(small, big, id) { return `<button class="banner" data-go="${id}"><div><small>${small}</small><b>${big}</b></div><span class="go">▶</span></button>`; }

// 별을 누르면 그 안의 문제 목록을 보여줌
function openGroup(key) {
  const g = GROUPS.find(x => x.key === key);
  const d = g.levels.filter(isDone).length;
  const cells = g.levels.map(L => {
    const r = store.games[L.id], st = r && r.done ? 'done' : r && hasMarks(r) ? 'part' : '';
    return `<button type="button" class="pnum ${st}" data-pick="${L.id}">${st === 'done' ? '★' : L.stage + 1}</button>`;
  }).join('');
  const go = g.levels.find(L => store.games[L.id] && hasMarks(store.games[L.id]) && !isDone(L)) || g.levels.find(L => !isDone(L));
  showDialog({
    title: `${g.size}×${g.size} · ${DIFFS[g.diff]}`,
    html: `<p style="margin:0 0 10px">${d} / ${STAGES} 완료 · 아무 문제나 골라서 풀 수 있어요</p><div class="pgrid">${cells}</div>`,
    buttons: [...(go ? [{ label: store.games[go.id] && hasMarks(store.games[go.id]) ? '이어서 풀기' : '다음 문제 풀기', cls: 'primary', fn: () => openLevel(go.id) }] : []), { label: '닫기' }]
  });
}
function openLevel(id) {
  const L = LEVELS.find(x => x.id === id);
  if (!L) { const r = store.games[id]; if (r) openGame(r); return; }
  const r = levelRec(L), title = `${L.size}×${L.size} · ${DIFFS[L.diff]} · ${L.stage + 1}번 문제`;
  if (r.done) {
    showDialog({ title, html: `이미 완성했어요! (${fmtTime(r.time)}, 힌트 ${r.hints}회)`, buttons: [
      { label: '다시 풀기', cls: 'primary', fn: () => openGame(freshRec(L)) },
      { label: '닫기' }] });
  } else if (hasMarks(r)) {
    showDialog({ title, html: `진행 ${pct(r)}% · ${fmtTime(r.time)}`, buttons: [
      { label: '이어하기', cls: 'primary', fn: () => openGame(r) },
      { label: '처음부터', cls: 'danger', fn: () => openGame(freshRec(L)) },
      { label: '닫기' }] });
  } else openGame(r);
}
function freshRec(L) { const r = levelRec(L); return Object.assign(r, { board: '', lock: [], hints: 0, time: 0, done: false, grid: '' }); }

document.addEventListener('click', e => {
  const t = e.target.closest('[data-go],[data-pick],.node,.tabs button,#fdiff button');
  if (!t) return;
  if (t.dataset.go) {
    const r = store.games[t.dataset.go];
    if (r) openGame(r); else openLevel(t.dataset.go);
  } else if (t.dataset.pick) openLevel(t.dataset.pick);
  else if (t.classList.contains('node')) openGroup(t.dataset.group);
  else if (t.dataset.tab) {
    document.querySelectorAll('.tabs button').forEach(b => b.classList.toggle('on', b === t));
    $('#tabCourse').hidden = t.dataset.tab !== 'course';
    $('#tabFree').hidden = t.dataset.tab !== 'free';
    $('#tabAlbum').hidden = t.dataset.tab !== 'album';
    if (t.dataset.tab === 'album') renderAlbum();
  } else if (t.dataset.d !== undefined) {
    store.settings.free.diff = +t.dataset.d; save(); renderHome();
  }
});
$('#fsize').addEventListener('input', e => {
  store.settings.free.size = +e.target.value; $('#fsizeOut').textContent = `${e.target.value} × ${e.target.value}`;
});
$('#fsize').addEventListener('change', save);
$('#fstart').addEventListener('click', () => {
  const f = store.settings.free, old = store.games.free;
  const start = () => openGame({ id: 'free', size: f.size, diff: f.diff, seed: (Math.random() * 4294967295) >>> 0, free: true, board: '', lock: [], hints: 0, time: 0, done: false, total: 0 });
  if (old && !old.done && hasMarks(old)) {
    showDialog({ title: '새 퍼즐을 시작할까요?', html: '진행 중인 "직접 설정" 퍼즐은 사라져요.', buttons: [
      { label: '새로 시작', cls: 'primary', fn: start }, { label: '취소' }] });
  } else start();
});

/* ---------------- 설정 / 백업 ---------------- */
$('#btnSettings').addEventListener('click', () => {
  const code = btoa(unescape(encodeURIComponent(JSON.stringify(store))));
  showDialog({
    title: '설정',
    html: `<p>진행 상황은 이 기기의 브라우저에 저장돼요. 기기를 바꾸거나 브라우저 데이터를 지우기 전에 백업 코드를 복사해 두세요.</p>
      <b style="color:var(--text)">백업 코드</b>
      <textarea id="bk" readonly>${code}</textarea>
      <b style="color:var(--text)">불러오기</b>
      <textarea id="rs" placeholder="백업 코드를 붙여넣기"></textarea>
      ${memoryOnly ? '<p style="color:var(--x)">⚠ 이 브라우저는 저장이 막혀 있어 창을 닫으면 기록이 사라져요.</p>' : ''}`,
    buttons: [
      { label: '백업 코드 복사', keep: true, fn: () => { const t = $('#bk'); t.select(); try { navigator.clipboard.writeText(t.value); } catch (e) { document.execCommand('copy'); } } },
      { label: '불러오기 적용', keep: true, fn: () => {
        try {
          const o = JSON.parse(decodeURIComponent(escape(atob($('#rs').value.trim()))));
          if (!o.games) throw 0;
          store = Object.assign(defaults(), o); save(); dlg.close(); renderHome();
        } catch (e) { alert('코드가 올바르지 않아요.'); }
      } },
      { label: '모든 기록 지우기', cls: 'danger', fn: () => {
        if (confirm('정말 모든 기록을 지울까요?')) { store = defaults(); save(); renderHome(); }
      } },
      { label: '닫기' }]
  });
});

/* ---------------- 게임 ---------------- */
let G = null, timerId = null;
const scroller = $('#scroller'), boardEl = $('#board'), cellsEl = $('#cells');
function showScreen(name) { $('#home').hidden = name !== 'home'; $('#game').hidden = name !== 'game'; }

function openGame(rec) {
  dlg.open && dlg.close();
  store.last = rec.id; store.games[rec.id] = rec; save();
  showScreen('game');
  $('#gTitle').textContent = label(rec);
  $('#gTime').textContent = fmtTime(rec.time);
  $('#loading').hidden = false; scroller.hidden = true;
  setTimeout(() => {
    if (!rec.pic) { Object.assign(rec, pickPic(rec)); rec.board = ''; rec.lock = []; }
    startGame(rec, buildPuzzle(rec));
  }, 30);
}

function startGame(rec, p) {
  const n = rec.size;
  rec.total = p.grid.reduce((a, b) => a + b, 0);
  const board = new Uint8Array(n * n);
  if (rec.board && rec.board.length === n * n) for (let i = 0; i < n * n; i++) board[i] = +rec.board[i];
  G = {
    rec, n, sol: p.grid, rows: p.rows, cols: p.cols, board, locked: new Set(rec.lock || []),
    color: p.color, undo: [], tool: 'fill', done: rec.done, rowOk: [], colOk: [], cs: 28,
    cellEls: [], rowEls: [], colEls: []
  };
  buildBoard();
  $('#loading').hidden = true; scroller.hidden = false;
  G.cs = fitCs(false);
  applyCs();
  scroller.scrollLeft = 0; scroller.scrollTop = 0;
  setTool('fill');
  updateBar();
  clearInterval(timerId);
  timerId = setInterval(tick, 1000);
  if (rec.done) { G.done = true; revealColors(); }
}

function buildBoard() {
  const { n, rows, cols } = G;
  boardEl.style.setProperty('--n', n);
  const g5 = i => (i % 5 === 4 && i < n - 1 ? ' g5' : '');
  $('#colclues').innerHTML = cols.map((c, i) => `<div class="cc${g5(i)}">${c.map(v => `<span>${v}</span>`).join('')}</div>`).join('');
  $('#rowclues').innerHTML = rows.map((c, i) => `<div class="rc${g5(i)}">${c.map(v => `<span>${v}</span>`).join('')}</div>`).join('');
  let h = '';
  G.base = [];
  for (let i = 0; i < n * n; i++) {
    const x = i % n, y = (i / n) | 0;
    const cls = 'c' + (x % 5 === 4 && x < n - 1 ? ' gr' : '') + (y % 5 === 4 && y < n - 1 ? ' gb' : '');
    G.base.push(cls);
    h += `<div class="${cls}"></div>`;
  }
  cellsEl.innerHTML = h;
  G.cellEls = [...cellsEl.children];
  G.rowEls = [...$('#rowclues').children];
  G.colEls = [...$('#colclues').children];
  for (let i = 0; i < n * n; i++) paintCell(i);
  for (let i = 0; i < n; i++) { refreshLine('r', i); refreshLine('c', i); }
  inkCv.width = inkCv.height = n * INK; // 손그림용 캔버스를 칸 위에 얹음
  cellsEl.appendChild(inkCv);
}
function paintCell(i) {
  const b = G.board[i];
  G.cellEls[i].className = G.base[i] + (b === 1 ? ' f' : b === 2 ? ' x' : '') + (G.locked.has(i) ? ' lk' : '');
}
function refreshLine(kind, k) {
  const n = G.n;
  const vals = [];
  for (let t = 0; t < n; t++) vals.push((kind === 'r' ? G.board[k * n + t] : G.board[t * n + k]) === 1 ? 1 : 0);
  const ok = sameArr(lineClue(vals), kind === 'r' ? G.rows[k] : G.cols[k]);
  if (kind === 'r') { G.rowOk[k] = ok; G.rowEls[k].classList.toggle('ok', ok); }
  else { G.colOk[k] = ok; G.colEls[k].classList.toggle('ok', ok); }
}
function setCell(i, v) {
  G.board[i] = v; paintCell(i);
  refreshLine('r', (i / G.n) | 0); refreshLine('c', i % G.n);
}

/* 확대/축소 */
function fitCs(allowSmall) {
  // 행 힌트 폭은 칸 크기에 거의 비례(+고정 여백)하므로 한 번 재서 역산
  const probe = 20;
  G.cs = probe; applyCs();
  const rcw = $('#rowclues').offsetWidth, per = (rcw - 16) / probe;
  const v = Math.floor((scroller.clientWidth - 18) / (G.n + per));
  return Math.max(allowSmall ? 10 : 20, Math.min(44, v));
}
function applyCs() { boardEl.style.setProperty('--cs', G.cs + 'px'); }
function setCs(v, ax, ay) {
  v = Math.max(10, Math.min(64, Math.round(v)));
  if (v === G.cs) return;
  const ratio = v / G.cs;
  if (ax === undefined) { ax = scroller.clientWidth / 2; ay = scroller.clientHeight / 2; }
  const sl = scroller.scrollLeft, st = scroller.scrollTop;
  G.cs = v; applyCs();
  scroller.scrollLeft = (sl + ax) * ratio - ax;
  scroller.scrollTop = (st + ay) * ratio - ay;
}
$('#btnZoomIn').onclick = () => setCs(G.cs + 4);
$('#btnZoomOut').onclick = () => setCs(G.cs - 4);
$('#btnFit').onclick = () => { G.cs = fitCs(true); applyCs(); scroller.scrollLeft = 0; scroller.scrollTop = 0; };

/* 도구 */
function setTool(t) {
  G.tool = t;
  document.querySelectorAll('.tool').forEach(b => b.classList.toggle('on', b.dataset.tool === t));
}
document.querySelectorAll('.tool').forEach(b => b.onclick = () => setTool(b.dataset.tool));
function updateBar() {
  const left = MAX_HINTS - G.rec.hints;
  $('#hintLeft').textContent = left;
  $('#btnHint').disabled = left <= 0 || G.done;
  $('#btnUndo').disabled = G.done;
}

/* 포인터 입력: 손가락·펜·마우스 모두 드래그로 칠하기 */
const ptrs = new Map();
let stroke = null, pinch = null;

function cellAt(e) {
  const r = cellsEl.getBoundingClientRect();
  const x = Math.floor((e.clientX - r.left) / G.cs), y = Math.floor((e.clientY - r.top) / G.cs);
  return x < 0 || y < 0 || x >= G.n || y >= G.n ? -1 : y * G.n + x;
}
function bresenham(a, b, fn) {
  const n = G.n;
  let x0 = a % n, y0 = (a / n) | 0;
  const x1 = b % n, y1 = (b / n) | 0;
  const dx = Math.abs(x1 - x0), dy = -Math.abs(y1 - y0), sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
  let err = dx + dy;
  for (;;) {
    fn(y0 * n + x0);
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
}
function paintStroke(i) {
  if (G.locked.has(i)) return;
  const cur = G.board[i];
  if (cur === stroke.to) return;
  if (stroke.from === -1 ? cur === 0 : cur !== stroke.from) return;
  stroke.changes.push([i, cur]);
  setCell(i, stroke.to);
}
function beginStroke(e) {
  const i = cellAt(e);
  if (i < 0) return;
  const eraserEnd = e.pointerType === 'pen' && (e.buttons & 32);
  const tool = eraserEnd ? 'erase' : G.tool;
  let from, to;
  if (tool === 'erase') { from = -1; to = 0; }
  else { const want = tool === 'fill' ? 1 : 2, s0 = G.board[i]; from = s0; to = s0 === want ? 0 : want; }
  stroke = { id: e.pointerId, from, to, last: i, start: i, axis: null, type: e.pointerType, changes: [] };
  paintStroke(i);
}
function continueStroke(e) {
  let j = cellAt(e);
  if (j < 0 || j === stroke.last) return;
  const n = G.n;
  if (stroke.type === 'touch') { // 손가락은 한 줄(가로/세로)로 고정해서 번지지 않게
    const sx = stroke.start % n, sy = (stroke.start / n) | 0;
    if (!stroke.axis) {
      const dx = Math.abs((j % n) - sx), dy = Math.abs(((j / n) | 0) - sy);
      if (!dx && !dy) return;
      stroke.axis = dx >= dy ? 'h' : 'v';
    }
    j = stroke.axis === 'h' ? sy * n + (j % n) : ((j / n) | 0) * n + sx;
  }
  bresenham(stroke.last, j, paintStroke);
  stroke.last = j;
}
function revert(changes) {
  for (let k = changes.length - 1; k >= 0; k--) setCell(changes[k][0], changes[k][1]);
}
function cancelStroke() { if (stroke) { revert(stroke.changes); stroke = null; } }
function endStroke() {
  if (!stroke) return;
  if (stroke.changes.length) {
    G.undo.push(stroke.changes);
    if (G.undo.length > 300) G.undo.shift();
    persist();
    checkWin();
  }
  stroke = null;
}
/* 손그림: 펜(또는 마우스)으로 직접 칠하면 잉크가 보이고, 떼면 칸에 반영됨. 엑스도 손으로 그려서 표시 */
const INK = 32; // 칸 하나가 캔버스에서 차지하는 픽셀
const PEND_MS = 1200; // 엑스의 두 번째 획을 기다려 주는 시간
const inkCv = document.createElement('canvas'), inkCtx = inkCv.getContext('2d');
inkCv.className = 'ink';
let ink = null, pend = [], pendTimer = null;
const useInk = e => e.pointerType === 'pen' || e.pointerType === 'mouse'; // 펜·마우스는 직접 그리기, 손가락은 칸 누르기
// 획이 이어지는 동안은 칸 위치·색을 한 번만 계산해 두고 재사용 (펜 이벤트가 아주 잦아서)
function inkPt(e, r) {
  return [(e.clientX - r.left) / r.width * G.n * INK, (e.clientY - r.top) / r.height * G.n * INK];
}
let inkColor = '#1f2a44';
function inkStyle(erase) {
  inkCtx.lineCap = inkCtx.lineJoin = 'round';
  if (erase) { inkCtx.strokeStyle = 'rgba(150,150,150,.5)'; inkCtx.lineWidth = INK * 0.7; }
  else { inkCtx.strokeStyle = inkColor; inkCtx.lineWidth = INK * 0.1; }
}
function inkSeg(a, b) { inkCtx.beginPath(); inkCtx.moveTo(a[0], a[1]); inkCtx.lineTo(b[0] + 0.01, b[1]); inkCtx.stroke(); }
const clearInk = () => inkCtx.clearRect(0, 0, inkCv.width, inkCv.height);
function beginInk(e) {
  const erase = !!(e.pointerType === 'pen' && (e.buttons & 32));
  if (erase) { resolvePend(); clearInk(); }
  clearTimeout(pendTimer);
  inkColor = getComputedStyle(document.documentElement).getPropertyValue('--ink').trim() || '#1f2a44';
  const rect = cellsEl.getBoundingClientRect(), p = inkPt(e, rect);
  ink = { id: e.pointerId, erase, rect, pts: [p] };
  inkStyle(erase); inkSeg(p, p);
}
function moveInk(e) {
  const evs = e.getCoalescedEvents ? e.getCoalescedEvents() : [];
  inkStyle(ink.erase);
  (evs.length ? evs : [e]).forEach(ev => {
    const p = inkPt(ev, ink.rect), prev = ink.pts[ink.pts.length - 1];
    ink.pts.push(p); inkSeg(prev, p);
  });
  // 두 번째 획이 첫 획을 가로지르는 순간 바로 엑스로 바꿈(펜을 떼길 기다리지 않음)
  if (!ink.erase && pend.length) {
    const a = ink.pts[0], b = ink.pts[ink.pts.length - 1];
    if (Math.hypot(b[0] - a[0], b[1] - a[1]) > INK * 0.45) {
      for (const q of pend) {
        const pt = crossPoint(q, { a, b }, true);
        if (pt) { ink = null; makeX(q, pt); return; }
      }
    }
  }
}
// 선이 지나간 칸 찾기: 같은 굵기로 작은 캔버스에 다시 그려서 칸별 덮인 비율을 계산
function inkCells(pts, w, thr) {
  const n = G.n, S = 8, k = S / INK, cv = document.createElement('canvas');
  cv.width = cv.height = n * S;
  const c = cv.getContext('2d', { willReadFrequently: true });
  c.lineCap = c.lineJoin = 'round'; c.strokeStyle = '#000'; c.lineWidth = w * S;
  c.beginPath();
  pts.forEach(([x, y], i) => (i ? c.lineTo(x * k, y * k) : c.moveTo(x * k, y * k)));
  c.lineTo(pts[pts.length - 1][0] * k + 0.01, pts[pts.length - 1][1] * k);
  c.stroke();
  const d = c.getImageData(0, 0, n * S, n * S).data, out = [];
  for (let cy = 0; cy < n; cy++) for (let cx = 0; cx < n; cx++) {
    let cnt = 0;
    for (let y = 0; y < S; y++) for (let x = 0; x < S; x++) if (d[((cy * S + y) * n * S + cx * S + x) * 4 + 3] > 127) cnt++;
    if (cnt / (S * S) >= thr) out.push(cy * n + cx);
  }
  return out;
}
function commitChanges(changes) {
  if (!changes.length) return;
  G.undo.push(changes);
  if (G.undo.length > 300) G.undo.shift();
  persist(); checkWin();
}
const inkCellOf = (x, y) => Math.min(G.n - 1, Math.max(0, Math.floor(y / INK))) * G.n + Math.min(G.n - 1, Math.max(0, Math.floor(x / INK)));
// 칠하기(또는 지우기): 시작한 칸이 이미 채워져 있으면 지우개처럼 동작
function applyFill(pts, erase) {
  const xs = pts.map(p => p[0]), ys = pts.map(p => p[1]);
  const tap = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)) < INK * 0.35;
  const first = inkCellOf(pts[0][0], pts[0][1]);
  const cells = tap ? [first] : inkCells(pts, erase ? 0.9 : 0.55, erase ? 0.25 : 0.3);
  if (erase) stroke = { from: -1, to: 0, changes: [] };
  else { const s0 = G.board[first]; stroke = { from: s0, to: s0 === 1 ? 0 : 1, changes: [] }; }
  cells.forEach(paintStroke);
  const ch = stroke.changes; stroke = null;
  commitChanges(ch);
}
// 짧고 비교적 곧은 선은 엑스의 한 획일 수 있어서 잠깐 기다림 (펜은 삐뚤어도 인식하도록 느슨하게)
function lineInfo(pts) {
  const xs = pts.map(p => p[0]), ys = pts.map(p => p[1]);
  const dim = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys));
  if (dim < INK * 0.3 || dim > INK * 5) return null;
  let len = 0;
  for (let i = 1; i < pts.length; i++) len += Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]);
  const a = pts[0], b = pts[pts.length - 1];
  if (!len || Math.hypot(b[0] - a[0], b[1] - a[1]) / len < 0.45) return null; // 꼬불꼬불한 낙서는 바로 칠하기
  return { a, b };
}
// 두 직선이 서로 가로지르는지(엑스 모양): 교차점을 돌려줌
function crossPoint(p, q, strict) {
  const r = [p.b[0] - p.a[0], p.b[1] - p.a[1]], s = [q.b[0] - q.a[0], q.b[1] - q.a[1]];
  const rl = Math.hypot(...r), sl = Math.hypot(...s), cr = r[0] * s[1] - r[1] * s[0];
  if (!rl || !sl || Math.abs(cr) / (rl * sl) < 0.34) return null; // 20도보다 좁게 겹치면(거의 평행) 엑스가 아님
  const qp = [q.a[0] - p.a[0], q.a[1] - p.a[1]];
  const t = (qp[0] * s[1] - qp[1] * s[0]) / cr, u = (qp[0] * r[1] - qp[1] * r[0]) / cr;
  if (t >= -0.35 && t <= 1.35 && u >= -0.35 && u <= 1.35) return [p.a[0] + t * r[0], p.a[1] + t * r[1]];
  // 딱 만나진 않아도 두 선이 같은 자리에 겹쳐 있으면(손으로 그린 엑스) 겹친 곳의 가운데를 엑스 위치로 (획을 마친 뒤에만)
  if (strict) return null;
  const box = c => [Math.min(c.a[0], c.b[0]), Math.min(c.a[1], c.b[1]), Math.max(c.a[0], c.b[0]), Math.max(c.a[1], c.b[1])];
  const A = box(p), B = box(q);
  const ox = Math.min(A[2], B[2]) - Math.max(A[0], B[0]), oy = Math.min(A[3], B[3]) - Math.max(A[1], B[1]);
  if (ox <= 0 || oy <= 0) return null;
  const small = Math.min((A[2] - A[0]) * (A[3] - A[1]), (B[2] - B[0]) * (B[3] - B[1])) || 1;
  if (ox * oy / small < 0.3) return null;
  return [(Math.max(A[0], B[0]) + Math.min(A[2], B[2])) / 2, (Math.max(A[1], B[1]) + Math.min(A[3], B[3])) / 2];
}
function redrawPend() {
  clearInk(); inkStyle(false);
  pend.forEach(s => s.pts.forEach((p, i) => inkSeg(s.pts[Math.max(0, i - 1)], p)));
}
// 기다리던 선 q와 새 선이 가로지른 지점에 엑스 표시(이미 엑스면 지움)
function makeX(q, pt) {
  const cell = inkCellOf(pt[0], pt[1]), cur = G.board[cell], changes = [];
  pend = pend.filter(x => x !== q);
  if (!G.locked.has(cell)) { changes.push([cell, cur]); setCell(cell, cur === 2 ? 0 : 2); }
  commitChanges(changes);
  clearTimeout(pendTimer);
  if (pend.length) { redrawPend(); pendTimer = setTimeout(resolvePend, PEND_MS); } else clearInk();
}
function endInk() {
  const s = ink; ink = null;
  if (!s) return;
  if (s.erase) { applyFill(s.pts, true); clearInk(); return; }
  const li = lineInfo(s.pts);
  if (!li) { resolvePend(); applyFill(s.pts, false); clearInk(); return; }
  const me = { pts: s.pts, ...li };
  // 이미 기다리던 선과 가로지르면 엑스 완성 (교차점이 있는 칸에 표시)
  for (const q of pend) {
    const pt = crossPoint(q, me);
    if (pt) { makeX(q, pt); return; }
  }
  pend.push(me);
  clearTimeout(pendTimer);
  pendTimer = setTimeout(resolvePend, PEND_MS);
}
// 짝이 안 맞아 남은 사선은 그냥 칠한 것으로 처리
function resolvePend() {
  clearTimeout(pendTimer);
  if (!G || !pend.length) return;
  const rest = pend; pend = [];
  rest.forEach(q => applyFill(q.pts, false));
  clearInk();
}
function touchPts() { return [...ptrs.values()].filter(p => p.type === 'touch'); }

// 펜·마우스로 그릴 땐 도구 버튼 대신 안내만 보여주고, 손가락으로 누를 땐 도구 버튼을 보여줌
const setInkInput = on => $('#game').classList.toggle('ink-input', on);
setInkInput(matchMedia('(pointer: fine)').matches && !('ontouchstart' in window));
cellsEl.addEventListener('contextmenu', e => e.preventDefault());
let penAt = -1e9; // 펜이 마지막으로 감지된 시각 (그 직후의 터치는 손바닥으로 보고 무시)
cellsEl.addEventListener('pointerdown', e => {
  if (!G || G.done) return;
  if (e.pointerType === 'pen') penAt = performance.now();
  if (e.pointerType === 'touch' && performance.now() - penAt < 2500) return;
  setInkInput(useInk(e));
  e.preventDefault();
  try { cellsEl.setPointerCapture(e.pointerId); } catch (_) {}
  ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY, type: e.pointerType });
  if (useInk(e)) {
    // 손바닥 터치 기록이 남아 펜 입력을 막지 않도록 정리
    for (const [id, p] of ptrs) if (p.type === 'touch') ptrs.delete(id);
    pinch = null;
    beginInk(e); return;
  }
  if (e.pointerType === 'touch') {
    if (ink) return; // 펜으로 그리는 중에 손바닥이 닿아도 무시
    const ts = touchPts();
    if (ts.length >= 2) { // 두 손가락: 핀치 확대/축소 + 이동
      cancelStroke();
      const [a, b] = ts;
      pinch = { d0: Math.hypot(a.x - b.x, a.y - b.y), cs0: G.cs, mx: (a.x + b.x) / 2, my: (a.y + b.y) / 2 };
      return;
    }
  }
  beginStroke(e);
});
cellsEl.addEventListener('pointermove', e => {
  if (e.pointerType === 'pen') penAt = performance.now(); // 펜이 화면 위에 떠 있기만 해도 손바닥 터치는 무시
  const p = ptrs.get(e.pointerId);
  if (!p) return;
  p.x = e.clientX; p.y = e.clientY;
  if (pinch && e.pointerType === 'touch') {
    const ts = touchPts();
    if (ts.length >= 2) {
      const [a, b] = ts, r = scroller.getBoundingClientRect();
      setCs(pinch.cs0 * Math.hypot(a.x - b.x, a.y - b.y) / pinch.d0, (a.x + b.x) / 2 - r.left, (a.y + b.y) / 2 - r.top);
      // 두 손가락을 같이 움직이면 화면 이동
      const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
      scroller.scrollLeft -= mx - pinch.mx; scroller.scrollTop -= my - pinch.my;
      pinch.mx = mx; pinch.my = my;
    }
    return;
  }
  if (ink && ink.id === e.pointerId) { moveInk(e); return; }
  if (stroke && stroke.id === e.pointerId) {
    const evs = e.getCoalescedEvents ? e.getCoalescedEvents() : [];
    (evs.length ? evs : [e]).forEach(ev => continueStroke(ev));
  }
});
function pointerEnd(e) {
  ptrs.delete(e.pointerId);
  if (ink && ink.id === e.pointerId) endInk();
  if (stroke && stroke.id === e.pointerId) endStroke();
  if (pinch && touchPts().length < 2) pinch = null;
}
cellsEl.addEventListener('pointerup', pointerEnd);
cellsEl.addEventListener('pointercancel', e => { if (stroke && stroke.id === e.pointerId) cancelStroke(); pointerEnd(e); });

/* 되돌리기 / 힌트 */
$('#btnUndo').onclick = () => {
  if (G.done) return;
  const ch = G.undo.pop();
  if (ch) { revert(ch); persist(); }
};
$('#btnHint').onclick = () => {
  if (G.done || G.rec.hints >= MAX_HINTS) return;
  const { n, sol, board } = G;
  const wrongRows = [], needRows = [];
  for (let y = 0; y < n; y++) {
    let wrong = false, need = false;
    for (let x = 0; x < n; x++) {
      const i = y * n + x;
      if (G.locked.has(i)) continue;
      if (board[i] === 1 && !sol[i]) wrong = true;
      if (board[i] !== 1 && sol[i]) need = true;
    }
    if (wrong) wrongRows.push(y); else if (need) needRows.push(y);
  }
  const pool = wrongRows.length ? wrongRows : needRows;
  if (!pool.length) { showDialog({ title: '힌트', html: '더 알려줄 칸이 없어요.', buttons: [{ label: '확인' }] }); return; }
  const y = pool[Math.floor(Math.random() * pool.length)];
  for (let x = 0; x < n; x++) {
    const i = y * n + x;
    G.locked.add(i);
    setCell(i, sol[i] ? 1 : 2);
  }
  G.rec.hints++;
  G.undo = []; // 힌트 이전으로는 되돌리지 않음
  persist(); updateBar(); checkWin();
};

/* 저장 / 타이머 / 완성 */
function persist() {
  const r = G.rec;
  r.board = Array.from(G.board).join('');
  r.lock = [...G.locked];
  save();
}
function tick() {
  if (!G || G.done || $('#game').hidden || document.hidden) return;
  G.rec.time++;
  $('#gTime').textContent = fmtTime(G.rec.time);
  if (G.rec.time % 5 === 0) persist();
}
document.addEventListener('visibilitychange', () => { if (G && !$('#game').hidden) persist(); });
window.addEventListener('pagehide', () => { if (G && !$('#game').hidden) persist(); });

// 완성하면 칠한 칸이 그림 본래의 색으로 바뀜
function revealColors() {
  G.board.forEach((v, i) => { if (v === 1) G.cellEls[i].style.backgroundColor = G.color[i]; });
  $('#gTitle').textContent = `${picInfo(G.rec.pic).emoji} ${picInfo(G.rec.pic).name}`;
}
function checkWin() {
  if (!G.rowOk.every(Boolean) || !G.colOk.every(Boolean)) return;
  G.done = true; G.rec.done = true;
  for (let i = 0; i < G.n * G.n; i++) if (G.board[i] === 2) { G.board[i] = 0; paintCell(i); }
  persist(); updateBar();
  const n = G.n;
  revealColors();
  const pic = picInfo(G.rec.pic);
  $('#gTitle').textContent = `${pic.emoji} ${pic.name}`;
  const prev = `<div class="preview" style="grid-template-columns:repeat(${n},1fr)">` +
    Array.from(G.board, (v, i) => `<i style="${v === 1 ? 'background:' + G.color[i] : ''}"></i>`).join('') + '</div>';
  const L = LEVELS.find(x => x.id === G.rec.id), nx = L && nextAfter(L);
  const btns = [];
  if (nx) btns.push({ label: '다음 문제', cls: 'primary', fn: () => openGame(levelRec(nx)) });
  btns.push({ label: '목록으로', fn: goHome });
  showDialog({ title: `🎉 ${pic.name} 완성!`, html: `${prev}<div style="text-align:center">걸린 시간 ${fmtTime(G.rec.time)} · 힌트 ${G.rec.hints}회</div>`, buttons: btns });
}
function goHome() {
  if (G) persist();
  clearInterval(timerId);
  showScreen('home'); renderHome();
}
$('#gBack').onclick = goHome;

/* 시작 */
renderHome();
showScreen('home');
if ('serviceWorker' in navigator && location.protocol.startsWith('http')) navigator.serviceWorker.register('sw.js').catch(() => {});
