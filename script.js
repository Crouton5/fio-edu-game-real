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

const cv = $('board'), ctx = cv.getContext('2d');

/* ---------- Circuit model ---------- */
function add(type, x, y) {
  const c = { id: nextId++, type, x, y, val: TYPES[type].v, closed: false, pressed: false, burned: false };
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
const tp = k => { const [i, t] = k.split(':'); const c = byId(+i); return { x: c.x + (t === '1' ? 40 : -40), y: c.y }; };

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
    if (c.type === 'lamp' && !c.burned && sol.I[c.id] ** 2 * c.val > BURN_W) { c.burned = true; burnt = true; }
  });
  if (burnt) { sol = solve(); renderProps(); }
  shorted = comps.some(c => isSrc(c.type) && Math.abs(sol.I[c.id]) > SHORT_A);
  const b = $('banner');
  if (shorted) b.textContent = 'Kortsluiting! De stroom loopt zonder weerstand van + naar −. Haal een draad weg of voeg een verbruiker toe.';
  else if (comps.some(c => c.burned)) b.textContent = 'Lampje doorgebrand: de spanning was te hoog. Selecteer het lampje en klik op Herstel.';
  b.hidden = !(shorted || comps.some(c => c.burned));
}

/* ---------- Drawing ---------- */
const L = (x1, y1, x2, y2) => { ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); };
const rr = (x, y, w, h, f) => { ctx.beginPath(); ctx.roundRect(x, y, w, h, 5); ctx.fillStyle = f; ctx.fill(); ctx.stroke(); };
const ci = (r, f) => { ctx.beginPath(); ctx.arc(0, 0, r, 0, 7); ctx.fillStyle = f; ctx.fill(); ctx.stroke(); };
const text = (s, x, y, font, color) => { ctx.font = font; ctx.fillStyle = color; ctx.textAlign = 'center'; ctx.fillText(s, x, y); };

function drawComp(c) {
  const I = sol.I[c.id] || 0, U = sol.U[c.id] || 0, T = TYPES[c.type];
  ctx.save();
  ctx.translate(c.x, c.y);
  ctx.lineWidth = 2.5; ctx.strokeStyle = INK; ctx.lineCap = 'round';
  if (c === sel) { ctx.setLineDash([5, 4]); ctx.strokeStyle = ACC; ctx.strokeRect(-46, -32, 92, 64); ctx.setLineDash([]); ctx.strokeStyle = INK; }
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
  const k = nearTerm(p, 12);
  if (k) { drag = { kind: 'wire', from: k, p }; return; }
  const c = [...comps].reverse().find(c => Math.abs(p.x - c.x) < 26 && Math.abs(p.y - c.y) < 22);
  if (c) {
    sel = c; drag = { kind: 'comp', c, dx: p.x - c.x, dy: p.y - c.y, sx: p.x, sy: p.y, moved: false };
    if (c.type === 'druk') c.pressed = true;
  } else sel = wires.find(w => distSeg(p, tp(w.a), tp(w.b)) < 7) || null;
  renderProps();
});
cv.addEventListener('pointermove', e => {
  if (!drag) return;
  const p = pos(e);
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
  h += '<p id="readout"></p><button id="del">Verwijder</button>';
  el.innerHTML = h;
  if ($('val')) $('val').oninput = e => { sel.val = +e.target.value; $('valOut').textContent = fmt(sel.val) + ' ' + T.u; };
  if ($('tog')) $('tog').onclick = () => { sel.closed = !sel.closed; renderProps(); };
  if ($('fix')) $('fix').onclick = () => { sel.burned = false; renderProps(); };
  $('del').onclick = removeSel;
}
function updateReadout() {
  const r = $('readout');
  if (!r || !comps.includes(sel)) return;
  const I = Math.abs(sol.I[sel.id] || 0), U = sol.U[sel.id] || 0;
  if (sel.type === 'druk' || sel.type === 'tuimel') { r.textContent = `Stroom: ${fmt(I)} A`; return; }
  r.textContent = `Spanning: ${fmt(U)} V · Stroom: ${fmt(I)} A` + (sel.type === 'lamp' ? ` · Vermogen: ${fmt(U * I)} W` : '');
}

/* ---------- Challenges ---------- */
const CH = [
  { t: 'Vrij bouwen', d: 'Bouw wat je wilt. Probeer ook de testobjecten: welke laten stroom door?' },
  { t: '1. Parallel', d: 'Laat 2 lampjes branden op 1 batterij. Als er één stukgaat, moet de andere blijven branden.',
    check() {
      const Ls = comps.filter(c => c.type === 'lamp' && !c.burned);
      if (Ls.length < 2 || shorted || !comps.some(c => isSrc(c.type)) || !Ls.every(l => lit(l, sol))) return false;
      return Ls.every(x => { const s = solve(x.id); return Ls.every(l => l === x || lit(l, s)); });
    } },
  { t: '2. Precies 0,5 A', d: 'Zorg dat de ampèremeter precies 0,5 A aangeeft. Tip: I = U / R.',
    check: () => !shorted && comps.some(c => c.type === 'ampere' && Math.abs(Math.abs(sol.I[c.id]) - 0.5) < 0.01) },
  { t: '3. Foutzoeken: draad los', d: 'Deze schakeling doet niets. Vind de fout en repareer hem.',
    setup: () => load([['batterij', 180, 300], ['lamp', 400, 160], ['weerstand', 400, 300]], [[0, 1, 1, 0], [1, 1, 2, 1]]),
    check: () => comps.some(c => c.type === 'lamp' && lit(c, sol)) },
  { t: '4. Foutzoeken: voltmeter', d: 'Het lampje brandt bijna niet. Er is iets verkeerd aangesloten. Laat het lampje branden en de voltmeter de lampspanning meten.',
    setup: () => load([['batterij', 180, 300], ['lamp', 400, 160], ['volt', 400, 300]], [[0, 1, 1, 0], [1, 1, 2, 1], [2, 0, 0, 0]]),
    check: () => comps.some(c => c.type === 'lamp' && lit(c, sol)) && comps.some(c => c.type === 'volt' && sol.U[c.id] > 0.3) }
];
function renderChallenges() {
  $('challenges').innerHTML = '<h2>Opdrachten</h2>' +
    CH.map((c, i) => `<button data-i="${i}" class="${i === cur ? 'on' : ''}">${c.t}</button>`).join('') +
    `<p id="chText">${CH[cur].d}</p><p id="chStatus"></p>`;
}
$('challenges').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  cur = +b.dataset.i;
  if (CH[cur].setup) CH[cur].setup(); else if (cur === 0) clearAll();
  renderChallenges();
});
function updateChallenge() {
  const s = $('chStatus'), c = CH[cur];
  if (s && c.check) s.innerHTML = c.check() ? '<span class="good">✓ Gelukt!</span>' : '';
}

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

renderTools(); renderProps(); renderChallenges(); resize();
requestAnimationFrame(frame);