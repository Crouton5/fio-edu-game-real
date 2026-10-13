'use strict';

/* ---------- Constants ---------- */
const INK = '#16202a', MUTED = '#5b6b7a', ACC = '#0b6bcb';
const R_INT = 0.1;      // internal resistance of a source (ohm)
const G_WIRE = 1000;    // a wire is a 1 milli-ohm resistor
const SHORT_A = 8;      // source current above this = short circuit
const FULL_W = 2;       // lamp power for full brightness
const BURN_W = 3.5;     // lamp power at which it burns out

const TYPES = {
  batterij:  { n: 'Batterij',          g: 'Voeding',      v: 4.5, min: 1.5, max: 12,  step: 1.5, u: 'V', lbl: 'Spanning' },
  bron:      { n: 'Spanningsbron',     g: 'Voeding',      v: 6,   min: 0,   max: 12,  step: 0.1, u: 'V', lbl: 'Spanning' },
  lamp:      { n: 'Lampje',            g: 'Verbruikers',  v: 20,  min: 5,   max: 100, step: 1,   u: 'Ω', lbl: 'Weerstand' },
  weerstand: { n: 'Weerstand',         g: 'Verbruikers',  v: 20,  min: 5,   max: 100, step: 1,   u: 'Ω', lbl: 'Weerstand' },
  potmeter:  { n: 'Potmeter',          g: 'Verbruikers',  v: 50,  min: 5,   max: 100, step: 1,   u: 'Ω', lbl: 'Weerstand' },
  druk:      { n: 'Drukschakelaar',    g: 'Schakelaars' },
  tuimel:    { n: 'Tuimelschakelaar',  g: 'Schakelaars' },
  ampere:    { n: 'Ampèremeter',       g: 'Meters' },
  volt:      { n: 'Voltmeter',         g: 'Meters' },
  draad:     { n: 'Draad',             g: 'Draden', r: 0.001 },
  gum:       { n: 'Gum',               g: 'Testobjecten', r: 1e9 },
  liniaal:   { n: 'Houten liniaal',    g: 'Testobjecten', r: 1e9 },
  munt:      { n: 'Koperen muntje',    g: 'Testobjecten', r: 0.01 },
  potlood:   { n: 'Potlood (grafiet)', g: 'Testobjecten', r: 8 }
};
const isSrc = t => t === 'batterij' || t === 'bron';
const fmt = n => String(+n.toFixed(2)).replace('.', ',');
const $ = id => document.getElementById(id);

/* ---------- State ---------- */
let comps = [], wires = [], nextId = 1;
let sel = null, drag = null, snap = null;
let sol = { I: {}, U: {}, wI: [] };
let real = true, conv = false, shorted = false, cur = 0;
let W = 0, H = 0, last = performance.now();

const HANDLE = 50;   // afstand van het draaibolletje tot het midden
const cv = $('board'), ctx = cv.getContext('2d');

/* ---------- Circuit model ---------- */
function add(type, x, y) {
  const c = { id: nextId++, type, x, y, val: TYPES[type].v, rot: 0, closed: false, pressed: false, burned: false };
  comps.push(c);
  return c;
}
function clearAll() { comps = []; wires = []; sel = null; renderProps(); }
function load(list, ws) {
  clearAll();
  list.forEach(([t, x, y]) => add(t, x, y));
  ws.forEach(([i, a, j, b]) => wires.push({ a: comps[i].id + ':' + a, b: comps[j].id + ':' + b }));
}
const byId = id => comps.find(c => c.id === id);
const tp = k => {
  const [i, t] = k.split(':'), c = byId(+i), d = t === '1' ? 40 : -40;
  return { x: c.x + d * Math.cos(c.rot), y: c.y + d * Math.sin(c.rot) };
};

function res(c, open) {
  if (c.id === open) return 1e9;
  switch (c.type) {
    case 'lamp': return c.burned ? 1e9 : c.val;
    case 'weerstand': case 'potmeter': return c.val;
    case 'druk': return c.pressed ? 0.001 : 1e9;
    case 'tuimel': return c.closed ? 0.001 : 1e9;
    case 'ampere': return 0.01;
    case 'volt': return 1e6;
    default: return TYPES[c.type].r;
  }
}

/* Nodal analysis: every terminal is a node, every wire a tiny resistor. */
function solve(open) {
  const n = comps.length * 2, ix = new Map(comps.map((c, i) => [c.id, i]));
  const A = Array.from({ length: n }, () => new Float64Array(n + 1));
  const st = (a, b, g) => { A[a][a] += g; A[b][b] += g; A[a][b] -= g; A[b][a] -= g; };
  const nd = k => { const [i, t] = k.split(':'); return 2 * ix.get(+i) + +t; };
  comps.forEach((c, i) => {
    const a = 2 * i, b = a + 1;
    A[a][a] += 1e-9; A[b][b] += 1e-9;
    if (isSrc(c.type)) { st(a, b, 1 / R_INT); A[b][n] += c.val / R_INT; A[a][n] -= c.val / R_INT; }
    else st(a, b, 1 / res(c, open));
  });
  wires.forEach(w => st(nd(w.a), nd(w.b), G_WIRE));
  for (let i = 0; i < n; i++) {
    let p = i;
    for (let r = i + 1; r < n; r++) if (Math.abs(A[r][i]) > Math.abs(A[p][i])) p = r;
    [A[i], A[p]] = [A[p], A[i]];
    for (let r = i + 1; r < n; r++) {
      const f = A[r][i] / A[i][i];
      if (f) for (let k = i; k <= n; k++) A[r][k] -= f * A[i][k];
    }
  }
  const v = new Float64Array(n);
  for (let i = n - 1; i >= 0; i--) {
    let s = A[i][n];
    for (let k = i + 1; k < n; k++) s -= A[i][k] * v[k];
    v[i] = s / A[i][i];
  }
  const I = {}, U = {};
  comps.forEach((c, i) => {
    const d = v[2 * i] - v[2 * i + 1];
    U[c.id] = Math.abs(d);
    I[c.id] = isSrc(c.type) ? (c.val + d) / R_INT : d / res(c, open);   // current from terminal 0 to 1
  });
  return { I, U, wI: wires.map(w => (v[nd(w.a)] - v[nd(w.b)]) * G_WIRE) };
}

const bright = (c, s) => c.burned ? 0 : Math.min(1, Math.sqrt(s.I[c.id] ** 2 * c.val / FULL_W));
const lit = (c, s) => bright(c, s) > 0.2;

function update() {
  sol = solve();
  let burnt = false;
  comps.forEach(c => {
    if (c.type === 'lamp' && !c.burned && sol.I[c.id] ** 2 * c.val > BURN_W) { burnW = sol.I[c.id] ** 2 * c.val; c.burned = true; burnt = true; }
  });
  if (burnt) { sol = solve(); renderProps(); lose('burn', burnW); }
  shorted = comps.some(c => isSrc(c.type) && Math.abs(sol.I[c.id]) > SHORT_A);
  shortT = shorted ? shortT + dt : 0;                 // 1,2 s uitstel: geen pop-up bij een kort tussenmomentje
  if (!shorted) shortFired = false;
  else if (shortT > 1.2 && !shortFired) { shortFired = true; lose('short'); }
  const b = $('banner');
  if (shorted) b.textContent = 'Kortsluiting! De stroom loopt zonder weerstand van + naar −. Haal een draad weg of voeg een verbruiker toe.';
  else if (comps.some(c => c.burned)) b.textContent = 'Lampje doorgebrand: de spanning was te hoog. Selecteer het lampje en klik op Herstel.';
  b.hidden = !(shorted || comps.some(c => c.burned));
}

/* ---------- Drawing ---------- */
const L = (x1, y1, x2, y2) => { ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); };
const rr = (x, y, w, h, f) => { ctx.beginPath(); ctx.roundRect(x, y, w, h, 5); ctx.fillStyle = f; ctx.fill(); ctx.stroke(); };
const ci = (r, f) => { ctx.beginPath(); ctx.arc(0, 0, r, 0, 7); ctx.fillStyle = f; ctx.fill(); ctx.stroke(); };
let curRot = 0;
const text = (s, x, y, font, color) => {
  ctx.save(); ctx.translate(x, y); ctx.rotate(-curRot);
  ctx.font = font; ctx.fillStyle = color; ctx.textAlign = 'center'; ctx.fillText(s, 0, 0);
  ctx.restore();
};

function drawComp(c) {
  const I = sol.I[c.id] || 0, U = sol.U[c.id] || 0, T = TYPES[c.type];
  ctx.save();
  ctx.translate(c.x, c.y);
  curRot = c.rot; ctx.save(); ctx.rotate(c.rot);
  ctx.lineWidth = 2.5; ctx.strokeStyle = INK; ctx.lineCap = 'round';
  if (c === sel) { ctx.setLineDash([5, 4]); ctx.strokeStyle = ACC; ctx.strokeRect(-46, -32, 92, 64); ctx.setLineDash([]);
    ctx.strokeStyle = ACC; L(0, -32, 0, -HANDLE); ctx.beginPath(); ctx.arc(0, -HANDLE, 7, 0, 7); ctx.fillStyle = ACC; ctx.fill();
    ctx.strokeStyle = INK; }
  L(-40, 0, -20, 0); L(20, 0, 40, 0);

  switch (c.type) {
    case 'batterij': case 'bron':
      if (real) {
        rr(-22, -15, 40, 30, c.type === 'bron' ? '#8b98a6' : '#e6b93a');
        rr(18, -6, 6, 12, '#9aa5b1');
        text(fmt(c.val) + ' V', -2, 5, 'bold 13px system-ui', INK);
      } else {
        if (c.type === 'bron') ci(19, '#fff');
        L(-6, -8, -6, 8); L(6, -15, 6, 15);
      }
      text('−', -30, -8, 'bold 16px system-ui', INK);
      text('+', 30, -8, 'bold 16px system-ui', INK);
      if (shorted && Math.abs(I) > SHORT_A) { ctx.fillStyle = 'rgba(220,38,38,.35)'; ctx.fillRect(-24, -17, 48, 34); text('🔥', 0, -36, '26px system-ui', INK); }
      break;
    case 'lamp': {
      const b = bright(c, sol), r = real ? 17 : 14;
      ctx.beginPath(); ctx.arc(0, 0, r, 0, 7);
      ctx.shadowColor = '#ffc800'; ctx.shadowBlur = 50 * b; ctx.fillStyle = c.burned ? '#9ca3af' : '#fff'; ctx.fill();
      ctx.shadowBlur = 0; ctx.fillStyle = `rgba(255,200,40,${b})`; ctx.fill(); ctx.stroke();
      if (real) {
        ctx.beginPath(); ctx.moveTo(-10, 8); ctx.lineTo(-5, -4); ctx.lineTo(0, 4); ctx.lineTo(5, -4); ctx.lineTo(10, 8); ctx.stroke();
      } else { L(-10, -10, 10, 10); L(-10, 10, 10, -10); }
      break;
    }
    case 'weerstand':
      if (real) { rr(-20, -8, 40, 16, '#e7d3a6'); ctx.fillStyle = '#8b4513'; [-10, -2, 6].forEach(x => ctx.fillRect(x, -8, 4, 16)); }
      else rr(-18, -8, 36, 16, '#fff');
      break;
    case 'potmeter':
      if (real) {
        ci(17, '#cfd8e0');
        const a = (c.val - 5) / 95 * 4.7 - 2.35;
        L(0, 0, 13 * Math.sin(a), -13 * Math.cos(a));
      } else { rr(-18, -8, 36, 16, '#fff'); L(-8, 22, 6, -14); L(6, -14, 7, -6); L(6, -14, -2, -10); }
      break;
    case 'druk': case 'tuimel': {
      const on = c.type === 'druk' ? c.pressed : c.closed;
      if (real) {
        rr(-24, 6, 48, 12, '#cfd8e0');
        if (c.type === 'druk') { ctx.beginPath(); ctx.arc(0, on ? 0 : -6, 11, 0, 7); ctx.fillStyle = '#d64545'; ctx.fill(); ctx.stroke(); }
        else L(-16, 6, on ? 16 : 12, on ? 6 : -16);
      } else {
        ctx.beginPath(); ctx.arc(-20, 0, 2.5, 0, 7); ctx.arc(20, 0, 2.5, 0, 7); ctx.fillStyle = INK; ctx.fill();
        L(-20, 0, on ? 20 : 16, on ? 0 : -14);
        if (c.type === 'druk') L(-6, -18, 6, -18);
      }
      break;
    }
    case 'ampere': case 'volt': {
      const a = c.type === 'ampere';
      ci(18, real ? (a ? '#fde7c8' : '#d6ecff') : '#fff');
      text(a ? 'A' : 'V', 0, 6, 'bold 18px system-ui', INK);
      text(fmt(a ? Math.abs(I) : U) + (a ? ' A' : ' V'), 0, 34, 'bold 13px system-ui', INK);
      break;
    }
    case 'draad': ctx.strokeStyle = real ? '#b8622a' : INK; ctx.lineWidth = real ? 5 : 2.5; L(-20, 0, 20, 0); break;
    case 'gum': real ? rr(-18, -10, 36, 20, '#f0a3b8') : rr(-18, -8, 36, 16, '#fff'); break;
    case 'liniaal':
      if (real) { rr(-26, -9, 52, 18, '#e3c58f'); for (let x = -22; x <= 22; x += 6) L(x, -9, x, -4); }
      else rr(-18, -8, 36, 16, '#fff');
      break;
    case 'munt': real ? (ci(15, '#c9793f'), ctx.beginPath(), ctx.arc(0, 0, 9, 0, 7), ctx.stroke()) : rr(-18, -8, 36, 16, '#fff'); break;
    case 'potlood':
      if (real) {
        rr(-24, -7, 34, 14, '#f2c230');
        ctx.beginPath(); ctx.moveTo(10, -7); ctx.lineTo(24, 0); ctx.lineTo(10, 7); ctx.closePath(); ctx.fillStyle = '#e8c8a0'; ctx.fill(); ctx.stroke();
        ctx.fillStyle = INK; ctx.beginPath(); ctx.moveTo(20, -2); ctx.lineTo(24, 0); ctx.lineTo(20, 2); ctx.fill();
      } else rr(-18, -8, 36, 16, '#fff');
      break;
  }

  ctx.restore(); curRot = 0;
  if (c.type !== 'ampere' && c.type !== 'volt') {
    const name = c.burned ? 'Lampje kapot' : T.n + (T.v !== undefined ? ' ' + fmt(c.val) + ' ' + T.u : '');
    text(name, 0, 34, '12px system-ui', MUTED);
  } else text(T.n, 0, 48, '12px system-ui', MUTED);
  ctx.restore();
}

function segDots(o, a, b, I) {
  if (Math.abs(I) < 1e-4) return;
  const d = Math.hypot(b.x - a.x, b.y - a.y);
  if (!d) return;
  const speed = 15 + Math.min(Math.abs(I), 4) * 80;
  o.ph = (o.ph || 0) + (((I > 0) === conv) ? 1 : -1) * speed * dt;
  const off = ((o.ph % 18) + 18) % 18;
  ctx.fillStyle = conv ? '#ea580c' : '#2563eb'; ctx.strokeStyle = '#fff'; ctx.lineWidth = 1;
  for (let k = off; k < d; k += 18) {
    ctx.beginPath(); ctx.arc(a.x + (b.x - a.x) * k / d, a.y + (b.y - a.y) * k / d, 3.5, 0, 7); ctx.fill(); ctx.stroke();
  }
}

let dt = 0;
function draw() {
  ctx.clearRect(0, 0, W, H);
  ctx.lineCap = 'round';
  wires.forEach(w => {
    const a = tp(w.a), b = tp(w.b);
    if (w === sel) { ctx.strokeStyle = 'rgba(11,107,203,.35)'; ctx.lineWidth = 11; L(a.x, a.y, b.x, b.y); }
    ctx.strokeStyle = real ? '#b8622a' : INK; ctx.lineWidth = real ? 5 : 2.5; L(a.x, a.y, b.x, b.y);
  });
  comps.forEach(drawComp);
  wires.forEach((w, i) => segDots(w, tp(w.a), tp(w.b), sol.wI[i] || 0));
  comps.forEach(c => segDots(c, tp(c.id + ':0'), tp(c.id + ':1'), sol.I[c.id] || 0));

  const used = new Set(); wires.forEach(w => { used.add(w.a); used.add(w.b); });
  comps.forEach(c => [0, 1].forEach(t => {
    const k = c.id + ':' + t, p = tp(k), hot = k === snap;
    ctx.beginPath(); ctx.arc(p.x, p.y, hot ? 8 : 5, 0, 7);
    ctx.fillStyle = hot ? ACC : used.has(k) ? INK : '#fff'; ctx.fill();
    ctx.strokeStyle = INK; ctx.lineWidth = 2; ctx.stroke();
  }));
  if (drag && drag.kind === 'wire') {
    const a = tp(drag.from), b = snap ? tp(snap) : drag.p;
    ctx.setLineDash([6, 5]); ctx.strokeStyle = ACC; ctx.lineWidth = 3; L(a.x, a.y, b.x, b.y); ctx.setLineDash([]);
  }
  if (!comps.length) text('Sleep een onderdeel uit de lijst naar dit bord', W / 2, H / 2, '16px system-ui', MUTED);
}

function frame(t) {
  dt = Math.min((t - last) / 1000, 0.05); last = t;
  update(); draw(); updateReadout(); updateChallenge();
  requestAnimationFrame(frame);
}

/* ---------- Interaction ---------- */
const pos = e => { const r = cv.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top }; };
function setRot(c, r) {
  let deg = r * 180 / Math.PI;
  const step = Math.round(deg / 15) * 15;
  if (Math.abs(deg - step) < 4) deg = step;          // magnetisch: klikt vast op elke 15°
  c.rot = deg * Math.PI / 180;
}
const rotate = (c, deg) => { c.rot += deg * Math.PI / 180; };
function nearTerm(p, max, skip) {
  let best = null, bd = max;
  comps.forEach(c => [0, 1].forEach(t => {
    const k = c.id + ':' + t, q = tp(k), d = Math.hypot(p.x - q.x, p.y - q.y);
    if (k !== skip && d < bd) { bd = d; best = k; }
  }));
  return best;
}
function distSeg(p, a, b) {
  const dx = b.x - a.x, dy = b.y - a.y, l2 = dx * dx + dy * dy || 1;
  const t = Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / l2));
  return Math.hypot(p.x - a.x - t * dx, p.y - a.y - t * dy);
}

cv.addEventListener('pointerdown', e => {
  const p = pos(e); cv.setPointerCapture(e.pointerId);
  if (comps.includes(sel) && Math.hypot(p.x - (sel.x + HANDLE * Math.sin(sel.rot)), p.y - (sel.y - HANDLE * Math.cos(sel.rot))) < 11) {
    drag = { kind: 'rot', c: sel }; return;
  }
  const k = nearTerm(p, 12);
  if (k) { drag = { kind: 'wire', from: k, p }; return; }
  const c = [...comps].reverse().find(c => {
    const dx = p.x - c.x, dy = p.y - c.y, sn = Math.sin(c.rot), cs = Math.cos(c.rot);
    return Math.abs(dx * cs + dy * sn) < 26 && Math.abs(-dx * sn + dy * cs) < 22;
  });
  if (c) {
    sel = c; drag = { kind: 'comp', c, dx: p.x - c.x, dy: p.y - c.y, sx: p.x, sy: p.y, moved: false };
    if (c.type === 'druk') c.pressed = true;
  } else sel = wires.find(w => distSeg(p, tp(w.a), tp(w.b)) < 7) || null;
  renderProps();
});
cv.addEventListener('pointermove', e => {
  if (!drag) return;
  const p = pos(e);
  if (drag.kind === 'rot') { setRot(drag.c, Math.atan2(p.y - drag.c.y, p.x - drag.c.x) + Math.PI / 2); return; }
  if (drag.kind === 'wire') { drag.p = p; snap = nearTerm(p, 22, drag.from); }
  else {
    if (Math.hypot(p.x - drag.sx, p.y - drag.sy) > 4) drag.moved = true;
    if (drag.moved) { drag.c.x = Math.max(50, Math.min(W - 50, p.x - drag.dx)); drag.c.y = Math.max(40, Math.min(H - 50, p.y - drag.dy)); }
  }
});
function endDrag() {
  if (!drag) return;
  if (drag.kind === 'wire' && snap && !wires.some(w => (w.a === drag.from && w.b === snap) || (w.b === drag.from && w.a === snap)))
    wires.push({ a: drag.from, b: snap });
  if (drag.kind === 'comp') {
    drag.c.pressed = false;
    if (!drag.moved && drag.c.type === 'tuimel') { drag.c.closed = !drag.c.closed; renderProps(); }
  }
  drag = null; snap = null;
}
cv.addEventListener('pointerup', endDrag);
cv.addEventListener('pointercancel', endDrag);

window.addEventListener('keydown', e => {
  if (e.key.toLowerCase() === 'r' && comps.includes(sel) && e.target.tagName !== 'INPUT') rotate(sel, e.shiftKey ? -90 : 90);
  if ((e.key === 'Delete' || e.key === 'Backspace') && sel && e.target.tagName !== 'INPUT') removeSel();
});
function removeSel() {
  if (comps.includes(sel)) { comps = comps.filter(c => c !== sel); wires = wires.filter(w => !w.a.startsWith(sel.id + ':') && !w.b.startsWith(sel.id + ':')); }
  else wires = wires.filter(w => w !== sel);
  sel = null; renderProps();
}

/* ---------- Palette (drag onto the board, or click to add) ---------- */
(function buildPalette() {
  let html = '', group = '';
  Object.entries(TYPES).forEach(([k, T]) => {
    if (T.g !== group) { group = T.g; html += `<h2>${group}</h2>`; }
    html += `<button data-t="${k}">${T.n}</button>`;
  });
  $('palette').innerHTML = html;
  let dragType = null;
  $('palette').addEventListener('pointerdown', e => {
    const b = e.target.closest('button'); if (!b) return;
    dragType = b.dataset.t; b.releasePointerCapture(e.pointerId);
  });
  window.addEventListener('pointerup', e => {
    if (!dragType) return;
    const r = cv.getBoundingClientRect();
    if (e.clientX > r.left && e.clientX < r.right && e.clientY > r.top && e.clientY < r.bottom) {
      sel = add(dragType, Math.max(50, Math.min(W - 50, e.clientX - r.left)), Math.max(40, Math.min(H - 50, e.clientY - r.top)));
      renderProps();
    }
    dragType = null;
  });
  $('palette').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    sel = add(b.dataset.t, W / 2 + Math.random() * 80 - 40, H / 2 + Math.random() * 80 - 40);
    renderProps();
  });
})();

/* ---------- Properties panel ---------- */
function renderProps() {
  const el = $('props');
  if (!sel) { el.innerHTML = '<h2>Onderdeel</h2><p class="hint">Klik op een onderdeel om het aan te passen. Sleep van het ene aansluitpunt naar het andere om een draad te maken.</p>'; return; }
  if (!comps.includes(sel)) { el.innerHTML = '<h2>Draad</h2><button id="del">Verwijder draad</button>'; $('del').onclick = removeSel; return; }
  const T = TYPES[sel.type];
  let h = `<h2>${T.n}</h2>`;
  if (T.v !== undefined) h += `<label>${T.lbl}: <output id="valOut">${fmt(sel.val)} ${T.u}</output><input id="val" type="range" min="${T.min}" max="${T.max}" step="${T.step}" value="${sel.val}"></label>`;
  if (sel.type === 'tuimel') h += `<button id="tog">${sel.closed ? 'Schakelaar openen' : 'Schakelaar sluiten'}</button> `;
  if (sel.type === 'druk') h += '<p class="hint">Houd de knop ingedrukt op het bord.</p>';
  if (sel.burned) h += '<button id="fix">Herstel lampje</button> ';
  h += '<p class="hint">Draaien: sleep het blauwe bolletje, gebruik de knoppen of druk op R.</p><button id="rotL">↺ 90°</button> <button id="rotR">↻ 90°</button> ';
  h += '<p id="readout"></p><button id="del">Verwijder</button>';
  el.innerHTML = h;
  if ($('val')) $('val').oninput = e => { sel.val = +e.target.value; $('valOut').textContent = fmt(sel.val) + ' ' + T.u; };
  if ($('tog')) $('tog').onclick = () => { sel.closed = !sel.closed; renderProps(); };
  if ($('fix')) $('fix').onclick = () => { sel.burned = false; renderProps(); };
  $('rotL').onclick = () => rotate(sel, -90);
  $('rotR').onclick = () => rotate(sel, 90);
  $('del').onclick = removeSel;
}
function updateReadout() {
  const r = $('readout');
  if (!r || !comps.includes(sel)) return;
  const I = Math.abs(sol.I[sel.id] || 0), U = sol.U[sel.id] || 0;
  if (sel.type === 'druk' || sel.type === 'tuimel') { r.textContent = `Stroom: ${fmt(I)} A`; return; }
  r.textContent = `Spanning: ${fmt(U)} V · Stroom: ${fmt(I)} A` + (sel.type === 'lamp' ? ` · Vermogen: ${fmt(U * I)} W` : '');
}

/* ---------- Beloning & pop-ups ---------- */
const POINTS = 150;
let points = 0, stars = 0, shortT = 0, shortFired = false, burnW = 0, hintUsed = false, failed = false, modalAct = null;

function renderScore() {
  $('scorePts').textContent = points + ' punten';
  $('scoreStars').textContent = '★ ' + stars;
}
function bump(id) { const e = $(id); e.classList.remove('bump'); void e.offsetWidth; e.classList.add('bump'); }

const calm = () => matchMedia('(prefers-reduced-motion: reduce)').matches;

/* Confetti: twee kanonnen onderin en een bui van boven */
const fx = $('confetti'), fctx = fx.getContext('2d');
let bits = [], fxOn = false;
function confetti() {
  if (calm()) return;
  const d = window.devicePixelRatio || 1, w = innerWidth, h = innerHeight;
  fx.width = w * d; fx.height = h * d; fctx.setTransform(d, 0, 0, d, 0, 0);
  const cols = ['#0b6bcb', '#15803d', '#e0a100', '#c2410c', '#d946ef', '#06b6d4'];
  const mk = (x, y, vx, vy, drag) => bits.push({
    x, y, vx, vy, drag, w: 6 + Math.random() * 6, h: 8 + Math.random() * 8,
    r: Math.random() * 6, vr: (Math.random() - 0.5) * 0.4, f: Math.random() * 6, c: cols[Math.random() * cols.length | 0]
  });
  for (let i = 0; i < 80; i++) {
    const a = 0.3 + (Math.random() - 0.5) * 0.7, v = 14 + Math.random() * 10;
    mk(0, h, Math.sin(a) * v, -Math.cos(a) * v, 0.99);
    mk(w, h, -Math.sin(a) * v, -Math.cos(a) * v, 0.99);
  }
  for (let i = 0; i < 70; i++) mk(Math.random() * w, -20 - Math.random() * 200, (Math.random() - 0.5) * 2, 1 + Math.random() * 2, 0.94);
  if (!fxOn) { fxOn = true; requestAnimationFrame(stepFx); }
}
function stepFx() {
  fctx.clearRect(0, 0, innerWidth, innerHeight);
  bits = bits.filter(b => b.y < innerHeight + 30);
  bits.forEach(b => {
    b.vy += 0.35; b.vx *= b.drag; b.vy *= b.drag; b.x += b.vx; b.y += b.vy; b.r += b.vr; b.f += 0.15;
    fctx.save(); fctx.translate(b.x, b.y); fctx.rotate(b.r); fctx.scale(1, Math.cos(b.f));
    fctx.fillStyle = b.c; fctx.fillRect(-b.w / 2, -b.h / 2, b.w, b.h); fctx.restore();
  });
  if (bits.length) requestAnimationFrame(stepFx); else fxOn = false;
}

function countUp(el, to) {
  const t0 = performance.now();
  const step = t => {
    const k = calm() ? 1 : Math.min(1, (t - t0) / 700);
    el.textContent = '+' + Math.round(to * k) + ' punten';
    if (k < 1) requestAnimationFrame(step);
  };
  requestAnimationFrame(step);
}

function showModal(kind, o) {
  $('modal').className = 'overlay ' + kind;
  $('mIcon').textContent = o.icon;
  $('mTitle').textContent = o.title;
  $('mStars').hidden = !o.stars;
  if (o.stars) $('mStars').innerHTML = [0, 1, 2].map(i =>
    i < o.stars ? `<span class="star on" style="--i:${i}">★</span>` : '<span class="star">☆</span>').join('');
  $('mPoints').hidden = !o.points;
  if (o.points) countUp($('mPoints'), o.points);
  $('mText').textContent = o.text;
  $('mPrimary').textContent = o.primaryLabel;
  $('mSecondary').textContent = o.secondaryLabel || '';
  $('mSecondary').hidden = !o.secondaryLabel;
  modalAct = o.onPrimary;
  $('modal').hidden = false;
  $('mPrimary').focus();
}
const closeModal = () => { $('modal').hidden = true; };
$('mPrimary').onclick = () => { closeModal(); if (modalAct) modalAct(); };
$('mSecondary').onclick = closeModal;
window.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('modal').hidden) closeModal(); });

function winChallenge() {
  const n = Math.max(1, 3 - (hintUsed ? 1 : 0) - (failed ? 1 : 0));   // 3 sterren: zonder tip en zonder fout
  points += POINTS; stars += n;
  starsBy[cur] = n; save();
  renderScore(); bump('scorePts'); bump('scoreStars');
  const last = cur >= CH.length - 1;
  showModal('win', {
    icon: '🏆', title: 'You Win!', stars: n, points: POINTS,
    text: `${['', 'Goed gedaan, volgende keer nog beter!', 'Mooi gedaan!', 'Perfect! Zonder tip en zonder fouten.'][n]} Je hebt "${CH[cur].t}" afgerond. ${CH[cur].win}`,
    primaryLabel: last ? 'Klaar' : 'Volgende opdracht', secondaryLabel: 'Blijf bouwen',
    onPrimary: () => { if (last) showMap(); else pickChallenge(cur + 1); }
  });
  confetti();
}
function lose(kind, w) {
  failed = true;
  const burn = kind === 'burn';
  showModal('lose', {
    icon: burn ? '💡' : '🔥', title: 'You Lose',
    text: burn
      ? `Het lampje is doorgebrand: het kreeg ${fmt(w)} W, maar kan maximaal ${fmt(BURN_W)} W aan (P = U × I). De spanning was te hoog of de weerstand te laag. Verlaag de spanning of verhoog de weerstand en probeer het opnieuw.`
      : 'Kortsluiting! De stroom liep zonder weerstand van + naar −, waardoor de batterij oververhit raakt. Zoek de directe verbinding en haal die weg, of zet een lampje in de kring.',
    primaryLabel: 'Opnieuw proberen',
    onPrimary: () => { if (burn) comps.forEach(c => { c.burned = false; }); renderProps(); }
  });
}

/* ---------- Opdrachten (beginnersniveau, volgorde van het werkboek) ---------- */
const lamps = () => comps.filter(c => c.type === 'lamp' && !c.burned);
const anyLit = () => lamps().some(l => lit(l, sol));
const hasSrc = () => comps.some(c => isSrc(c.type));
const OBJECTS = ['gum', 'liniaal', 'munt', 'potlood'];
const A = x => Math.abs(x);

const CH = [
  { t: 'Vrij bouwen',
    goal: 'Bouw wat je wilt en probeer dingen uit.',
    needs: 'Alle onderdelen' },

  { t: 'Het lampje laten branden',
    goal: 'Laat het lampje branden.',
    needs: 'Batterij, lampje, 2 draden',
    hint: 'Maak een gesloten kring: van de + van de batterij naar het lampje, en van het lampje terug naar de −. Sleep van een aansluitpunt (cirkeltje) naar een ander aansluitpunt om een draad te maken.',
    win: 'Dit is een stroomkring: de stroom kan van + via het lampje terug naar −.',
    check: () => !shorted && hasSrc() && anyLit() },

  { t: 'Aan en uit met een schakelaar',
    goal: 'Bouw een kring waarin je het lampje met de tuimelschakelaar aan en uit kunt zetten. Laat hem eindigen in de stand "aan".',
    needs: 'Batterij, lampje, tuimelschakelaar, 3 draden',
    hint: 'Zet de schakelaar in dezelfde kring als het lampje (in serie). Klik op de schakelaar om hem te sluiten of te openen.',
    win: 'Een open schakelaar onderbreekt de kring, dus dan loopt er geen stroom.',
    check: () => {
      const s = comps.find(c => c.type === 'tuimel' && c.closed);
      if (!s || shorted || !anyLit()) return false;
      const open = solve(s.id);
      return !lamps().some(l => lit(l, open));
    } },

  { t: 'De stroom meten',
    goal: 'Laat het lampje branden en meet de stroomsterkte door het lampje met de ampèremeter.',
    needs: 'Batterij, lampje, ampèremeter',
    hint: 'Een ampèremeter zet je in serie: in de kring zelf, net als een schakelaar. Niet ernaast.',
    win: 'In serie meet je precies de stroom die door het lampje gaat.',
    check: () => {
      const L = lamps().find(l => lit(l, sol));
      return !shorted && !!L && comps.some(c => c.type === 'ampere' && A(sol.I[c.id]) > 0.005 && A(A(sol.I[c.id]) - A(sol.I[L.id])) < 0.005);
    } },

  { t: 'De spanning meten',
    goal: 'Laat het lampje branden en meet de spanning over het lampje met de voltmeter.',
    needs: 'Batterij, lampje, voltmeter',
    hint: 'Bouw eerst de kring zonder voltmeter. Verbind daarna de twee aansluitingen van de voltmeter met de twee kanten van het lampje (parallel).',
    win: 'Een voltmeter sluit je parallel aan, over het onderdeel dat je wilt meten.',
    check: () => {
      const L = lamps().find(l => lit(l, sol));
      return !shorted && !!L && comps.some(c => c.type === 'volt' && sol.U[c.id] > 0.3 && A(sol.U[c.id] - sol.U[L.id]) < 0.05);
    } },

  { t: 'Geleider of isolator?',
    goal: 'Zet een testobject in de kring zodat het lampje brandt. Probeer alle objecten uit: welke laten stroom door?',
    needs: 'Batterij, lampje, testobject (gum, liniaal, muntje, potlood)',
    hint: 'Zet het testobject in serie met het lampje, zoals je met de schakelaar deed. Brandt het lampje niet? Dan is het object een isolator.',
    win: 'Objecten waarmee het lampje brandt zijn geleiders. De andere zijn isolatoren.',
    check: () => !shorted && anyLit() && comps.some(c => OBJECTS.includes(c.type) && A(sol.I[c.id]) > 0.01) },

  { t: 'Serieschakeling',
    goal: 'Zet twee lampjes achter elkaar en laat ze allebei branden.',
    needs: 'Batterij, 2 lampjes',
    hint: 'Verbind lampje 1 met lampje 2, en sluit de uiteinden aan op de batterij. Branden ze zwak? Klik op de batterij en zet de spanning hoger.',
    win: 'In serie is de stroomsterkte overal even groot. Gaat één lampje stuk, dan gaat het andere ook uit.',
    check: () => {
      const Ls = lamps();
      if (shorted || Ls.length < 2 || !Ls.every(l => lit(l, sol))) return false;
      if (!Ls.every(l => A(A(sol.I[l.id]) - A(sol.I[Ls[0].id])) < 0.002)) return false;
      return Ls.every(x => { const s = solve(x.id); return Ls.every(l => l === x || !lit(l, s)); });
    } },

  { t: 'Parallelschakeling',
    goal: 'Laat 2 lampjes branden op 1 batterij. Als één lampje stukgaat, moet het andere blijven branden.',
    needs: 'Batterij, 2 lampjes',
    hint: 'Geef elk lampje zijn eigen weg: verbind beide lampjes apart met de + en de − van de batterij.',
    win: 'In een parallelschakeling heeft elk lampje een eigen tak. De ene tak werkt ook als de andere stuk is.',
    check: () => {
      const Ls = lamps();
      if (shorted || Ls.length < 2 || !hasSrc() || !Ls.every(l => lit(l, sol))) return false;
      return Ls.every(x => { const s = solve(x.id); return Ls.every(l => l === x || lit(l, s)); });
    } },

  { t: 'Precies 0,5 A',
    goal: 'Zorg dat de ampèremeter precies 0,5 A aangeeft.',
    needs: 'Spanningsbron, lampje of weerstand, ampèremeter',
    hint: 'Gebruik I = U / R. Met 6 V en 12 Ω krijg je 0,5 A. Klik op een onderdeel om de waarde aan te passen.',
    win: 'Je hebt de wet van Ohm gebruikt: I = U / R.',
    check: () => !shorted && comps.some(c => c.type === 'ampere' && A(A(sol.I[c.id]) - 0.5) < 0.01) },

  { t: 'Foutzoeken: losse draad',
    goal: 'Deze schakeling doet niets. Zoek de fout en repareer hem.',
    needs: 'Alles ligt al op het bord',
    hint: 'Kijk goed: is de kring overal gesloten? Eén draad ontbreekt.',
    win: 'Een losse draad onderbreekt de kring, dus er loopt geen stroom.',
    setup: () => load([['batterij', 200, 100], ['lamp', 420, 100], ['weerstand', 420, 300]], [[0, 1, 1, 0], [1, 1, 2, 1]]),
    check: () => !shorted && anyLit() },

  { t: 'Foutzoeken: voltmeter',
    goal: 'Het lampje brandt bijna niet. Zoek de fout. Laat het lampje branden en laat de voltmeter de spanning over het lampje meten.',
    needs: 'Alles ligt al op het bord',
    hint: 'Een voltmeter hoort parallel aan het lampje, niet in serie. Verwijder een draad (klik erop en kies Verwijder) en sluit de voltmeter anders aan.',
    win: 'Een voltmeter in serie laat bijna geen stroom door. Parallel meet hij de spanning.',
    setup: () => load([['batterij', 200, 100], ['lamp', 420, 100], ['volt', 420, 300]], [[0, 1, 1, 0], [1, 1, 2, 1], [2, 0, 0, 0]]),
    check: () => {
      const L = lamps().find(l => lit(l, sol));
      return !shorted && !!L && comps.some(c => c.type === 'volt' && sol.U[c.id] > 0.3 && A(sol.U[c.id] - sol.U[L.id]) < 0.05);
    } },

  { t: 'Kortsluiting oplossen', startsShorted: true,
    goal: 'De batterij wordt heet! Zoek de oorzaak en los de kortsluiting op, zodat het lampje brandt.',
    needs: 'Alles ligt al op het bord',
    hint: 'Kortsluiting is een verbinding van + naar − zonder weerstand. Welk onderdeel staat los van het lampje direct op de batterij aangesloten? Klik erop.',
    win: 'Een gesloten schakelaar parallel aan de batterij sluit kort. In huis beschermt een zekering hiertegen.',
    setup: () => { load([['batterij', 300, 100], ['lamp', 300, 230], ['tuimel', 300, 360]], [[0, 0, 1, 0], [1, 0, 2, 0], [0, 1, 1, 1], [1, 1, 2, 1]]); comps[2].closed = true; },
    check: () => !shorted && anyLit() }
];

const done = new Set();
let starsBy = {};
const SAVE_KEY = 'stroomkring-voortgang';
function save() {
  try { localStorage.setItem(SAVE_KEY, JSON.stringify({ points, stars, done: [...done], starsBy })); } catch (e) { /* geen opslag beschikbaar */ }
}
function loadSave() {
  try {
    const d = JSON.parse(localStorage.getItem(SAVE_KEY) || 'null');
    if (!d) return;
    points = d.points | 0; stars = d.stars | 0; starsBy = d.starsBy || {};
    (d.done || []).forEach(i => done.add(i));
  } catch (e) { /* kapotte opslag negeren */ }
}
let lastOk = false, hintOpen = false;

function renderChallenges() {
  const c = CH[cur];
  let h = `<h2>Opdracht ${cur ? cur + ' van ' + (CH.length - 1) : ''}</h2><div class="chcard"><h3>${c.t}</h3><p>${c.goal}</p><p class="hint">Nodig: ${c.needs}</p>`;
  if (c.hint) h += `<button id="hintBtn">${hintOpen ? 'Verberg tip' : 'Toon tip'}</button>` + (hintOpen ? `<p class="hint">${c.hint}</p>` : '');
  if (c.check && lastOk) {
    h += `<p class="good">✓ Gelukt!</p><p>${c.win}</p>`;
    if (cur < CH.length - 1) h += '<button id="nextBtn">Volgende opdracht</button>';
  }
  $('challenges').innerHTML = h + '</div>';
}
function pickChallenge(i) {
  cur = i; lastOk = false; hintOpen = false; hintUsed = false; failed = false;
  closeModal();
  clearAll();
  if (CH[cur].setup) CH[cur].setup();
  shortT = 0; shortFired = !!CH[cur].startsShorted;
  renderChallenges();
}
$('challenges').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  if (b.id === 'hintBtn') { hintOpen = !hintOpen; if (hintOpen) hintUsed = true; renderChallenges(); }
  else if (b.id === 'nextBtn') pickChallenge(cur + 1);
  else pickChallenge(+b.dataset.i);
});
function updateChallenge() {
  const c = CH[cur];
  if (!c.check) return;
  const ok = !!c.check();
  if (ok === lastOk) return;
  lastOk = ok;
  const first = ok && !done.has(cur);
  if (ok) done.add(cur);
  renderChallenges();
  if (first) winChallenge();
}

/* ---------- Level map (Duolingo-stijl) ---------- */
const UNITS = [
  { t: 'Unit 1', s: 'Stroomkring en meten', from: 1, to: 5 },
  { t: 'Unit 2', s: 'Serie en parallel', from: 6, to: 8 },
  { t: 'Unit 3', s: 'Foutzoeken en veiligheid', from: 9, to: 11 }
];
function renderMap() {
  const total = CH.length - 1, n = done.size;
  const cu = Array.from({ length: total }, (_, i) => i + 1).find(i => !done.has(i));   // eerstvolgende opdracht
  let h = '<div class="maplane"><button class="free" data-i="0">🧪 Vrij bouwen</button>' +
    `<div class="prog"><div style="width:${n / total * 100}%"></div></div><span class="progtxt">${n} van ${total} opdrachten gehaald</span>`;
  UNITS.forEach(u => {
    let cnt = 0, nodes = '';
    for (let i = u.from; i <= u.to; i++) {
      const st = done.has(i) ? 'done' : i === cu ? 'cur' : 'lock';
      if (st === 'done') cnt++;
      const sc = starsBy[i] || 1;
      nodes += `<div class="nodewrap" style="--x:${Math.round(Math.sin((i - 1) * 1.1) * 58)}px">` +
        (st === 'cur' ? '<span class="start">START</span>' : '') +
        `<button class="node ${st}" data-i="${i}" aria-label="${CH[i].t}">${{ done: '✓', cur: '★', lock: '🔒' }[st]}</button>` +
        `<span class="nlabel">${CH[i].t}</span><span class="nstars">${st === 'done' ? '★'.repeat(sc) + '☆'.repeat(3 - sc) : ''}</span></div>`;
    }
    h += `<div class="unit"><div><b>${u.t}</b><span>${u.s}</span></div><span class="ucount">${cnt}/${u.to - u.from + 1}</span></div><div class="path">${nodes}</div>`;
  });
  $('map').innerHTML = h + '</div>';
}
function showMap() {
  document.body.classList.add('on-map');
  renderMap();
  const el = $('map').querySelector('.node.cur');
  if (el) el.scrollIntoView({ block: 'center' });
}
function showGame() { document.body.classList.remove('on-map'); resize(); }
function toast(m) {
  const t = $('toast'); t.textContent = m; t.hidden = false;
  clearTimeout(toast.id); toast.id = setTimeout(() => { t.hidden = true; }, 2000);
}
$('map').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  if (b.classList.contains('lock')) {
    b.classList.remove('shake'); void b.offsetWidth; b.classList.add('shake');
    toast('Rond eerst de vorige opdracht af.');
    return;
  }
  pickChallenge(+b.dataset.i); showGame();
});
$('btnMap').onclick = showMap;

/* ---------- Toolbar & setup ---------- */
function renderTools() {
  $('btnView').textContent = 'Weergave: ' + (real ? 'Realistisch' : 'Schakelschema');
  $('btnDir').textContent = 'Stroomrichting: ' + (conv ? 'Conventioneel (+ → −)' : 'Elektronen (− → +)');
}
$('btnView').onclick = () => { real = !real; renderTools(); };
$('btnDir').onclick = () => { conv = !conv; renderTools(); };
$('btnClear').onclick = () => { clearAll(); };

function resize() {
  const r = cv.getBoundingClientRect(), d = window.devicePixelRatio || 1;
  W = r.width; H = r.height;
  cv.width = W * d; cv.height = H * d;
  ctx.setTransform(d, 0, 0, d, 0, 0);
}
new ResizeObserver(resize).observe(cv);

loadSave(); renderTools(); renderProps(); renderChallenges(); renderScore(); resize(); showMap();
requestAnimationFrame(frame);