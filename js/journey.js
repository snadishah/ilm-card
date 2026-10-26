(function(){"use strict";
function main(){
/* ---------- small maths ---------- */
const TAU = Math.PI * 2;
const clamp = (x, a = 0, b = 1) => Math.min(b, Math.max(a, x));
const lerp = (a, b, t) => a + (b - a) * t;
const sstep = (a, b, x) => { const t = clamp((x - a) / (b - a)); return t * t * (3 - 2 * t); };
const ease = t => t * t * (3 - 2 * t);
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
const rand = mulberry32(20261010);
const R = (a = 1, b) => b === undefined ? rand() * a : a + rand() * (b - a);
const pick = arr => arr[(rand() * arr.length) | 0];

const PERM = new Uint8Array(512);
(function () { const p = []; for (let i = 0; i < 256; i++) p.push(i); const r = mulberry32(99); for (let i = 255; i > 0; i--) { const j = (r() * (i + 1)) | 0; const t = p[i]; p[i] = p[j]; p[j] = t; } for (let i = 0; i < 512; i++) PERM[i] = p[i & 255]; })();
function vnoise(x, y) {
  const xi = Math.floor(x), yi = Math.floor(y), xf = x - xi, yf = y - yi;
  const u = xf * xf * (3 - 2 * xf), v = yf * yf * (3 - 2 * yf);
  const h = (i, j) => PERM[(PERM[i & 255] + j) & 255] / 255;
  return lerp(lerp(h(xi, yi), h(xi + 1, yi), u), lerp(h(xi, yi + 1), h(xi + 1, yi + 1), u), v);
}
function fbm(x, y, o = 3) { let a = .5, f = 1, s = 0, n = 0; for (let i = 0; i < o; i++) { s += a * vnoise(x * f, y * f); n += a; a *= .5; f *= 2.03; } return s / n; }

/* ---------- palette (sRGB hex, converted to linear once) ---------- */
const PAL = {
  grassA: '#74b267', grassB: '#8fc476', grassC: '#58995f', meadow: '#a8cf7c',
  dirt: '#cdb686', dirtD: '#b19a69', sand: '#e0d3a2', pave: '#a4b89e', asphalt: '#4c5d56', line: '#ece8cf',
  hillA: '#6ba47c', hillB: '#86b792',
  mud: '#c9ab7c', mudL: '#dcc497', mudD: '#a98d63', wood: '#7b5b3d', woodD: '#5b4331', straw: '#dfcb7c', strawD: '#c9b266',
  plaster: '#ece2c0', plasterG: '#b4d3a9', plasterS: '#9cc3a0', plasterO: '#dcc784', trim: '#2f7d5b', trimD: '#1f5a43',
  leafA: '#3f9160', leafB: '#2f7c53', leafC: '#59a86d', leafD: '#246749', olive: '#84a85d', palm: '#4b9c5d', palmD: '#357f4c',
  bark: '#6c5541', barkL: '#8b7153',
  white: '#f7f5ea', cream: '#f3ecd2', dark: '#22332c', glass: '#24493f', iron: '#3b5148',
  terracotta: '#c17b4f', amber: '#f2b24f', teal: '#3c8f86', red: '#c9563e', rose: '#d98c8c', mustard: '#d9b24a', sky: '#8fc1c9', plum: '#8c5f86',
  water: '#63bfae', concrete: '#c9cdbd', concreteD: '#a9b0a0'
};
const _colCache = {};
function col(hex) { return _colCache[hex] || (_colCache[hex] = new THREE.Color(hex).convertSRGBToLinear()); }
const _matCache = {};
function mat(hex) { return _matCache[hex] || (_matCache[hex] = new THREE.MeshLambertMaterial({ color: col(hex) })); }

/* ---------- geometry cache: every primitive sits on the ground (base at y=0) ---------- */
const GEO = {};
function geo(key, make) { if (!GEO[key]) { let g = make(); if (g.index) g = g.toNonIndexed(); g.computeBoundingBox(); GEO[key] = g; } return GEO[key]; }
const gBox = () => geo('box', () => new THREE.BoxGeometry(1, 1, 1).translate(0, .5, 0));
const gTaper = (k = .92) => geo('taper' + k, () => { const g = new THREE.BoxGeometry(1, 1, 1).translate(0, .5, 0); const p = g.attributes.position; for (let i = 0; i < p.count; i++) if (p.getY(i) > .5) { p.setX(i, p.getX(i) * k); p.setZ(i, p.getZ(i) * k); } return g; });
const gCyl = (ratio = 1, seg = 8) => geo('cyl' + ratio.toFixed(2) + '_' + seg, () => new THREE.CylinderGeometry(ratio, 1, 1, seg).translate(0, .5, 0));
const gCone = (seg = 6) => geo('cone' + seg, () => new THREE.ConeGeometry(1, 1, seg).translate(0, .5, 0));
const gIco = (d = 0) => geo('ico' + d, () => new THREE.IcosahedronGeometry(1, d));
const gDome = (seg = 8) => geo('dome' + seg, () => new THREE.SphereGeometry(1, seg, 4, 0, TAU, 0, Math.PI / 2));

/* ---------- Kit: bakes many coloured primitives into one flat-shaded mesh ---------- */
const YAX = new THREE.Vector3(0, 1, 0);
const _E = new THREE.Euler(), _Q = new THREE.Quaternion(), _T = new THREE.Matrix4(), _V = new THREE.Vector3(), _S = new THREE.Vector3();
const _TRI = [new THREE.Vector3(), new THREE.Vector3(), new THREE.Vector3()], _AB = new THREE.Vector3(), _AC = new THREE.Vector3();
class Kit {
  constructor() { this.P = []; this.N = []; this.C = []; this.stack = [new THREE.Matrix4()]; }
  get M() { return this.stack[this.stack.length - 1]; }
  at(x, y, z, ry, fn, s = 1) {
    const m = new THREE.Matrix4().compose(new THREE.Vector3(x, y, z), new THREE.Quaternion().setFromAxisAngle(YAX, ry || 0), new THREE.Vector3(s, s, s));
    m.premultiply(this.M); this.stack.push(m); fn(); this.stack.pop(); return this;
  }
  add(g, o) {
    const pa = g.attributes.position.array, bb = g.boundingBox;
    _E.set(o.rx || 0, o.ry || 0, o.rz || 0, 'YXZ'); _Q.setFromEuler(_E);
    _T.compose(_V.set(o.x || 0, o.y || 0, o.z || 0), _Q, _S.set(o.sx ?? 1, o.sy ?? 1, o.sz ?? 1)).premultiply(this.M);
    const c1 = col(o.c), c2 = o.c2 ? col(o.c2) : c1;
    const oj = 1 + (rand() * 2 - 1) * (o.jit ?? 0.035), fj = o.fjit || 0;
    const y0 = bb.min.y, yh = (bb.max.y - bb.min.y) || 1;
    const P = this.P, N = this.N, C = this.C;
    for (let i = 0; i < pa.length; i += 9) {
      const f = oj * (fj ? 1 + (rand() * 2 - 1) * fj : 1);
      for (let k = 0; k < 3; k++) {
        const v = _TRI[k].set(pa[i + k * 3], pa[i + k * 3 + 1], pa[i + k * 3 + 2]);
        const t = (v.y - y0) / yh; v.applyMatrix4(_T);
        P.push(v.x, v.y, v.z);
        C.push((c1.r + (c2.r - c1.r) * t) * f, (c1.g + (c2.g - c1.g) * t) * f, (c1.b + (c2.b - c1.b) * t) * f);
      }
      _AB.subVectors(_TRI[1], _TRI[0]); _AC.subVectors(_TRI[2], _TRI[0]); _AB.cross(_AC).normalize();
      N.push(_AB.x, _AB.y, _AB.z, _AB.x, _AB.y, _AB.z, _AB.x, _AB.y, _AB.z);
    }
    return this;
  }
  box(x, y, z, w, h, d, c, o = {}) { return this.add(gBox(), Object.assign({ x, y, z, sx: w, sy: h, sz: d, c }, o)); }
  taper(x, y, z, w, h, d, c, o = {}) { return this.add(gTaper(o.k || .92), Object.assign({ x, y, z, sx: w, sy: h, sz: d, c }, o)); }
  cyl(x, y, z, rt, rb, h, c, o = {}) { const m = Math.max(rb, 1e-4); return this.add(gCyl(rt / m, o.seg || 8), Object.assign({ x, y, z, sx: m, sy: h, sz: m, c }, o)); }
  cone(x, y, z, r, h, c, o = {}) { return this.add(gCone(o.seg || 6), Object.assign({ x, y, z, sx: r, sy: h, sz: r, c }, o)); }
  ico(x, y, z, sx, sy, sz, c, o = {}) { return this.add(gIco(o.d || 0), Object.assign({ x, y, z, sx, sy, sz, c }, o)); }
  dome(x, y, z, r, h, c, o = {}) { return this.add(gDome(o.seg || 8), Object.assign({ x, y, z, sx: r, sy: h, sz: r, c }, o)); }
  geometry() {
    const g = new THREE.BufferGeometry();
    g.setAttribute('position', new THREE.BufferAttribute(new Float32Array(this.P), 3));
    g.setAttribute('normal', new THREE.BufferAttribute(new Float32Array(this.N), 3));
    g.setAttribute('color', new THREE.BufferAttribute(new Float32Array(this.C), 3));
    g.computeBoundingSphere(); g.computeBoundingBox();
    return g;
  }
  mesh(material, cast = true, receive = true) { const m = new THREE.Mesh(this.geometry(), material); m.castShadow = cast; m.receiveShadow = receive; m.matrixAutoUpdate = false; return m; }
}

/* ---------- shared materials ---------- */
const uTime = { value: 0 };
const M = {};
M.world = new THREE.MeshLambertMaterial({ vertexColors: true });
M.glow = new THREE.MeshBasicMaterial({ color: 0x1d3f36 });               // window panes: dark glass by day, lamp-lit at night
M.lit = new THREE.MeshBasicMaterial({ vertexColors: true });              // always-on emissive bits
function windMaterial(sway) {
  const m = new THREE.MeshLambertMaterial({ vertexColors: true });
  m.onBeforeCompile = sh => {
    sh.uniforms.uTime = uTime; sh.uniforms.uSway = { value: sway };
    sh.vertexShader = 'uniform float uTime;uniform float uSway;\n' + sh.vertexShader.replace('#include <begin_vertex>',
      '#include <begin_vertex>\n#ifdef USE_INSTANCING\nfloat ph=instanceMatrix[3][0]*.31+instanceMatrix[3][2]*.27;float hh=max(transformed.y,0.);float sw=(sin(uTime*1.5+ph)+.5*sin(uTime*2.7+ph*1.7))*uSway*hh*hh;transformed.x+=sw;transformed.z+=sw*.6;\n#endif');
  };
  return m;
}
M.tree = windMaterial(0.0016);
M.grass = windMaterial(0.11);

/* ---------- canvas textures (redrawn once the web fonts arrive) ---------- */
const TEX = [];
function canvasTex(w, h, draw) {
  const c = document.createElement('canvas'); c.width = w; c.height = h; const x = c.getContext('2d'); draw(x, w, h);
  const t = new THREE.CanvasTexture(c); t.encoding = THREE.sRGBEncoding; t.anisotropy = 4; t.userData = { draw, x, w, h }; TEX.push(t); return t;
}
function redrawTextures() { for (const t of TEX) { const u = t.userData; u.x.clearRect(0, 0, u.w, u.h); u.draw(u.x, u.w, u.h); t.needsUpdate = true; } }
const FD = '"Fraunces", Georgia, serif', FB = '"Figtree", "Segoe UI", Arial, sans-serif';
const glowTex = (function () {
  const c = document.createElement('canvas'); c.width = c.height = 128; const x = c.getContext('2d');
  const g = x.createRadialGradient(64, 64, 0, 64, 64, 64); g.addColorStop(0, 'rgba(255,255,255,1)'); g.addColorStop(.25, 'rgba(255,255,255,.55)'); g.addColorStop(.6, 'rgba(255,255,255,.12)'); g.addColorStop(1, 'rgba(255,255,255,0)');
  x.fillStyle = g; x.fillRect(0, 0, 128, 128); return new THREE.CanvasTexture(c);
})();
function glowSprite(hex, size, opacity = 1) {
  const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: glowTex, color: col(hex), blending: THREE.AdditiveBlending, depthWrite: false, transparent: true, opacity, fog: false }));
  s.scale.setScalar(size); s.userData.base = opacity; return s;
}
function signMesh(tex, w, h, lit = false) {
  const m = new THREE.Mesh(new THREE.PlaneGeometry(w, h), lit ? new THREE.MeshBasicMaterial({ map: tex }) : new THREE.MeshLambertMaterial({ map: tex }));
  return m;
}
function drawCardIcon(x, cx, cy, s, fill, notch) {
  // a microSD outline: the thing the whole company is named after
  x.save(); x.translate(cx, cy); x.scale(s, s); x.beginPath();
  x.moveTo(-.34, -.5); x.lineTo(.18, -.5); x.lineTo(.36, -.3); x.lineTo(.36, -.02); x.lineTo(.28, .06); x.lineTo(.36, .14); x.lineTo(.36, .5); x.lineTo(-.34, .5); x.closePath();
  x.fillStyle = fill; x.fill(); x.fillStyle = notch;
  for (let i = 0; i < 4; i++) x.fillRect(-.24 + i * .12, -.42, .07, .2);
  x.restore();
}
/* ---------- the route: Multan (x=0) west across the Chenab to two villages in Muzaffargarh ---------- */
const ROAD_PTS = [[-120, 8], [-70, 7], [-25, 6], [20, 6], [60, 5], [95, 0], [125, -10], [150, -16], [181, -16], [214, -16], [250, -8], [280, 6], [310, 12], [345, 10], [385, -2], [425, -18], [465, -30], [505, -35], [535, -31], [556, -25]];
const roadCurve = new THREE.CatmullRomCurve3(ROAD_PTS.map(p => new THREE.Vector3(p[0], 0, p[1])), false, 'catmullrom', 0.5);
roadCurve.arcLengthDivisions = 900;
const ROAD_N = 460, roadS = [], roadT = [];
for (let i = 0; i <= ROAD_N; i++) { roadS.push(roadCurve.getPointAt(i / ROAD_N)); roadT.push(roadCurve.getTangentAt(i / ROAD_N)); }
function roadDist(x, z) {
  let best = 1e9;
  for (let i = 0; i <= ROAD_N; i++) { const p = roadS[i], dx = p.x - x; if (dx > 60 || dx < -60) continue; const dz = p.z - z, d = dx * dx + dz * dz; if (d < best) best = d; }
  return best === 1e9 ? 999 : Math.sqrt(best);
}
function roadUAtX(x) { let bi = 0, bd = 1e9; for (let i = 0; i <= ROAD_N; i++) { const d = Math.abs(roadS[i].x - x); if (d < bd) { bd = d; bi = i; } } return bi / ROAD_N; }
const riverX = z => 181 + 15 * Math.sin((z + 16) * 0.013) + 0.05 * (z + 16);
const riverHW = z => 21 + 4.5 * Math.sin(z * 0.02 + 1.3);
const PADS = [
  { x: -22, z: -4, rx: 92, rz: 46, kind: 'town' },
  { x: 300, z: -14, rx: 48, rz: 40, kind: 'village' },
  { x: 576, z: -42, rx: 52, rz: 30, kind: 'village' }
];
const POND = { x: 512, z: -84, r: 13 };
const ORCHARD = { x0: 226, x1: 272, z0: 22, z1: 70 };
const OCC = [];                                      // circles kept clear of trees and grass
const occ = (x, z, r) => OCC.push({ x, z, r });
function padAt(x, z) { let k = 0, kind = null; for (const p of PADS) { const d = Math.hypot((x - p.x) / p.rx, (z - p.z) / p.rz); const v = 1 - sstep(.78, 1.2, d); if (v > k) { k = v; kind = p.kind; } } return { k, kind }; }
function inRiver(x, z, m = 0) { return Math.abs(x - riverX(z)) < riverHW(z) + m; }

function H(x, z) {
  let h = (fbm(x * .012, z * .012) - .5) * 6 + (fbm(x * .05 + 9, z * .05) - .5) * 1.1;
  const rd = roadDist(x, z);
  h *= sstep(4, 34, rd) * .8;
  const pd = padAt(x, z); h *= 1 - pd.k;
  const az = Math.abs(z + 8);
  h += sstep(112, 250, az) * (7 + 26 * fbm(x * .0065 + 3, z * .0065 + 1));
  h += sstep(610, 720, x) * 16 * fbm(x * .01, z * .01 + 7) + sstep(-110, -175, x) * 12 * fbm(x * .01 + 5, z * .01);
  if (az > 250 || x > 700 || x < -180) h += (sstep(250, 700, az) * 52 + sstep(700, 1150, x) * 60 + sstep(-180, -640, x) * 40) * fbm(x * .0042 + 11, z * .0042 + 2);
  h -= (1 - sstep(2.7, 4.6, rd)) * .16;                                   // seat for the road ribbon
  const dr = Math.abs(x - riverX(z)), hw = riverHW(z);
  h = lerp(h, -3.4, 1 - sstep(hw - 7, hw + 9, dr));                       // the Chenab
  const dp = Math.hypot(x - POND.x, z - POND.z);
  h = lerp(h, -1.7, 1 - sstep(POND.r - 5, POND.r + 4, dp));
  return h;
}

/* ---------- field plots along the road ---------- */
const CROPS = {
  wheat: ['#9bcb72', '#8bbf65'], paddy: ['#b3dc7f', '#a1cf6f'], fodder: ['#70b173', '#62a467'],
  plough: ['#c6b687', '#b6a676'], ripe: ['#ded88f', '#d2ca80']
};
const CROP_BAG = ['wheat', 'wheat', 'wheat', 'paddy', 'paddy', 'fodder', 'fodder', 'plough', 'ripe'];
const FIELDS = [];
function fieldBlocked(x, z, r) {
  if (inRiver(x, z, r + 14)) return true;
  for (const p of PADS) if (Math.hypot((x - p.x) / (p.rx + r), (z - p.z) / (p.rz + r)) < 1.12) return true;
  if (Math.hypot(x - POND.x, z - POND.z) < POND.r + r + 6) return true;
  if (x > ORCHARD.x0 - r && x < ORCHARD.x1 + r && z > ORCHARD.z0 - r && z < ORCHARD.z1 + r) return true;
  for (const f of FIELDS) if (Math.hypot(x - f.x, z - f.z) < (r + Math.max(f.w, f.d) * .5) * .82) return true;
  return false;
}
(function () {
  for (let u = 0.12; u < 0.985; u += 0.036) {
    const p = roadCurve.getPointAt(u), t = roadCurve.getTangentAt(u), ang = Math.atan2(t.z, t.x);
    for (const side of [-1, 1]) for (let row = 0; row < 3; row++) {
      const w = R(25, 31), d = R(22, 27), off = 6.5 + d / 2 + row * 29 + R(0, 2);
      const cx = p.x - t.z * side * off, cz = p.z + t.x * side * off;
      if (fieldBlocked(cx, cz, Math.max(w, d) * .5)) continue;
      const type = pick(CROP_BAG);
      FIELDS.push({ x: cx, z: cz, w, d, cos: Math.cos(ang), sin: Math.sin(ang), type, row });
    }
  }
})();
function fieldAt(x, z) {
  for (const f of FIELDS) {
    const dx = x - f.x, dz = z - f.z; if (dx > 22 || dx < -22 || dz > 22 || dz < -22) continue;
    const lx = dx * f.cos + dz * f.sin, lz = -dx * f.sin + dz * f.cos;
    if (Math.abs(lx) < f.w / 2 && Math.abs(lz) < f.d / 2) return { f, lx, lz, edge: Math.min(f.w / 2 - Math.abs(lx), f.d / 2 - Math.abs(lz)) };
  }
  return null;
}

const _gc = new THREE.Color();
function groundColor(x, z, h) {
  const n = fbm(x * .035, z * .035, 2), n2 = vnoise(x * .21 + 4, z * .21);
  _gc.copy(col(PAL.grassA)).lerp(col(PAL.grassB), sstep(.38, .7, n));
  if (n < .34) _gc.lerp(col(PAL.grassC), .55);
  if (n2 > .74) _gc.lerp(col(PAL.meadow), .45);
  const az = Math.abs(z + 8); _gc.lerp(col(h > 15 ? PAL.hillB : PAL.hillA), Math.max(sstep(112, 210, az), sstep(640, 760, x), sstep(-140, -220, x)) * .85); if (h > 34) _gc.lerp(col('#a3c9ac'), sstep(34, 62, h) * .7);
  const fa = fieldAt(x, z);
  if (fa) { const c = CROPS[fa.f.type]; if (fa.f.row <= 1) _gc.copy(col(c[1])).lerp(col(PAL.dirtD), fa.f.type === 'paddy' ? .12 : .34); else _gc.copy(col(c[(Math.floor((fa.lz + 40) / 1.9) & 1)])); if (fa.edge < 1.1) _gc.lerp(col(PAL.dirtD), .6); }
  const rd = roadDist(x, z); _gc.lerp(col(PAL.dirt), (1 - sstep(3.2, 8.5, rd)) * .9);
  const pd = padAt(x, z);
  if (pd.k > 0) {
    if (pd.kind === 'town') _gc.lerp(col(PAL.pave), pd.k * .92 * (.8 + .2 * n2));
    else { const n3 = fbm(x * .09 + 3, z * .09 + 8, 2); _gc.lerp(col(n3 > .6 ? PAL.dirtD : PAL.dirt), pd.k * sstep(.3, .52, n3) * .94); if (n3 > .7) _gc.lerp(col('#c2a877'), .5); }
  }
  const dr = Math.abs(x - riverX(z)) - riverHW(z);
  if (dr < 13) _gc.lerp(col(PAL.sand), 1 - sstep(-1, 13, dr)); if (dr < -3) _gc.lerp(col('#8fb99d'), .7);
  const dp = Math.hypot(x - POND.x, z - POND.z) - POND.r; if (dp < 6) _gc.lerp(col(PAL.dirtD), (1 - sstep(-2, 6, dp)) * .8);
  return _gc.multiplyScalar(.95 + rand() * .1);
}

function buildTerrain(scene, LOW) {
  terrainPatch(scene, -180, 720, -270, 270, LOW ? 4.4 : 3.3, 0, null);
  terrainPatch(scene, -760, 1320, -860, 860, 20, -2.4, [-160, 700, -250, 250]);
}
function terrainPatch(scene, x0, x1, z0, z1, step, drop, hole) {
  const nx = Math.ceil((x1 - x0) / step), nz = Math.ceil((z1 - z0) / step), W = nx + 1;
  const px = new Float32Array(W * (nz + 1)), pz = new Float32Array(W * (nz + 1)), py = new Float32Array(W * (nz + 1));
  for (let j = 0; j <= nz; j++) for (let i = 0; i <= nx; i++) {
    const k = j * W + i, edge = i === 0 || j === 0 || i === nx || j === nz;
    px[k] = x0 + i * step + (edge ? 0 : (rand() - .5) * step * .55); pz[k] = z0 + j * step + (edge ? 0 : (rand() - .5) * step * .55);
    py[k] = H(px[k], pz[k]) + drop;
  }
  const P = new Float32Array(nx * nz * 18), C = new Float32Array(nx * nz * 18), N = new Float32Array(nx * nz * 18);
  let o = 0; const a = new THREE.Vector3(), b = new THREE.Vector3(), c = new THREE.Vector3();
  const tri = (i0, i1, i2) => {
    a.set(px[i0], py[i0], pz[i0]); b.set(px[i1], py[i1], pz[i1]); c.set(px[i2], py[i2], pz[i2]);
    const cx = (a.x + b.x + c.x) / 3, cz = (a.z + b.z + c.z) / 3, ch = (a.y + b.y + c.y) / 3, g = groundColor(cx, cz, ch);
    _AB.subVectors(b, a); _AC.subVectors(c, a); _AB.cross(_AC).normalize();
    for (const v of [a, b, c]) { P[o] = v.x; P[o + 1] = v.y; P[o + 2] = v.z; C[o] = g.r; C[o + 1] = g.g; C[o + 2] = g.b; N[o] = _AB.x; N[o + 1] = _AB.y; N[o + 2] = _AB.z; o += 3; }
  };
  for (let j = 0; j < nz; j++) for (let i = 0; i < nx; i++) {
    const A = j * W + i, B = A + 1, Cc = A + W, D = Cc + 1;
    if (hole && px[A] > hole[0] && px[D] < hole[1] && pz[A] > hole[2] && pz[D] < hole[3]) continue;
    if ((i + j) & 1) { tri(A, Cc, B); tri(B, Cc, D); } else { tri(A, Cc, D); tri(A, D, B); }
  }
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(P.subarray(0, o), 3)); g.setAttribute('normal', new THREE.BufferAttribute(N.subarray(0, o), 3)); g.setAttribute('color', new THREE.BufferAttribute(C.subarray(0, o), 3));
  g.computeBoundingSphere();
  const m = new THREE.Mesh(g, M.world); m.receiveShadow = true; m.matrixAutoUpdate = false; scene.add(m);
}

/* ---------- road ribbon ---------- */
function buildRoad(scene) {
  const k = new Kit(), A = new THREE.Vector3(), B = new THREE.Vector3(), Cc = new THREE.Vector3(), D = new THREE.Vector3(), c = new THREE.Color();
  const quad = (p, q, r, s, color) => {          // p,q at sample i (left,right); r,s at i+1
    for (const v of [p, q, r, q, s, r]) { k.P.push(v.x, v.y, v.z); k.N.push(0, 1, 0); k.C.push(color.r, color.g, color.b); }
  };
  const strip = (o0, o1, y, colorAt, skip) => {
    for (let i = 0; i < ROAD_N; i++) {
      if (skip && skip(i)) continue;
      const p = roadS[i], t = roadT[i], q = roadS[i + 1], u = roadT[i + 1];
      A.set(p.x - t.z * o0, y, p.z + t.x * o0); B.set(p.x - t.z * o1, y, p.z + t.x * o1);
      Cc.set(q.x - u.z * o0, y, q.z + u.x * o0); D.set(q.x - u.z * o1, y, q.z + u.x * o1);
      quad(A, B, Cc, D, colorAt(roadS[i].x, i));
    }
  };
  const base = (x, i) => c.copy(col(PAL.asphalt)).lerp(col(PAL.dirt), sstep(70, 105, x)).lerp(col(PAL.asphalt), (1 - sstep(8, 16, Math.abs(x - 181) - 34))).multiplyScalar(.97 + (i % 7) * .008);
  strip(-3.2, 3.2, .06, base);
  const track = x => c.copy(col('#52625b')).lerp(col(PAL.dirtD), sstep(70, 105, x)).lerp(col('#52625b'), (1 - sstep(8, 16, Math.abs(x - 181) - 34)));
  strip(-1.55, -.85, .075, track); strip(.85, 1.55, .075, track);
  const paved = i => { const x = roadS[i].x; return x < 74 || Math.abs(x - 181) < 34; };
  strip(-3.62, -3.2, .1, () => c.copy(col('#d5dcc6')), i => !paved(i)); strip(3.2, 3.62, .1, () => c.copy(col('#d5dcc6')), i => !paved(i));
  strip(-.12, .12, .08, () => c.copy(col(PAL.line)), i => { const x = roadS[i].x; return !((x < 78) || Math.abs(x - 181) < 36) || (i % 4 > 1); });
  const m = k.mesh(M.world, false, true); scene.add(m);
}

/* ---------- water ---------- */
const waterTex = (function () {
  const c = document.createElement('canvas'); c.width = c.height = 256; const x = c.getContext('2d');
  x.fillStyle = '#cfe9df'; x.fillRect(0, 0, 256, 256);
  const r = mulberry32(5);
  for (let i = 0; i < 90; i++) { const y = r() * 256, w = 30 + r() * 90, xx = r() * 256, a = .1 + r() * .35; x.fillStyle = `rgba(255,255,255,${a})`; for (const ox of [-256, 0, 256]) { x.beginPath(); x.ellipse(xx + ox, y, w / 2, 1.4 + r() * 1.6, 0, 0, TAU); x.fill(); } }
  for (let i = 0; i < 50; i++) { const y = r() * 256, w = 40 + r() * 80, xx = r() * 256; x.fillStyle = 'rgba(70,140,125,.18)'; for (const ox of [-256, 0, 256]) { x.beginPath(); x.ellipse(xx + ox, y, w / 2, 2 + r() * 2, 0, 0, TAU); x.fill(); } }
  const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.encoding = THREE.sRGBEncoding; t.anisotropy = 4; return t;
})();
M.water = new THREE.MeshLambertMaterial({ color: col(PAL.water), map: waterTex });
function buildWater(scene) {
  const P = [], U = [], N = [], I = []; let n = 0;
  for (let z = -276; z <= 276; z += 8) { const cx = riverX(z), hw = riverHW(z) + 5; P.push(cx - hw, -1.05, z, cx + hw, -1.05, z); U.push(0, z / 46, 1.6, z / 46); N.push(0, 1, 0, 0, 1, 0); if (n) I.push(n - 2, n, n - 1, n - 1, n, n + 1); n += 2; }
  const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(P, 3)); g.setAttribute('uv', new THREE.Float32BufferAttribute(U, 2)); g.setAttribute('normal', new THREE.Float32BufferAttribute(N, 3)); g.setIndex(I);
  const river = new THREE.Mesh(g, M.water); river.receiveShadow = true; scene.add(river);
  const pg = new THREE.CircleGeometry(POND.r + 2, 20).rotateX(-Math.PI / 2); const uv = pg.attributes.uv; for (let i = 0; i < uv.count; i++) uv.setXY(i, uv.getX(i) * .7, uv.getY(i) * .7);
  const pond = new THREE.Mesh(pg, M.water); pond.position.set(POND.x, -.55, POND.z); pond.receiveShadow = true; scene.add(pond);
}

/* ---------- plants ---------- */
const gBoxC = () => geo('boxc', () => new THREE.BoxGeometry(1, 1, 1));
function tplMango() {
  const k = new Kit();
  k.cyl(0, 0, 0, .34, .52, 2.5, PAL.bark, { seg: 6, fjit: .08 });
  k.cyl(.15, 1.9, 0, .15, .24, 1.7, PAL.bark, { seg: 5, rz: -.65 }); k.cyl(-.15, 1.9, .1, .15, .24, 1.6, PAL.bark, { seg: 5, rz: .7, ry: .6 });
  const blobs = [[0, 4.8, 0, 3.3, 2.3, 3.2, 1], [2, 4.1, .6, 2.1, 1.6, 2.0, 0], [-1.9, 4.2, -.5, 2.2, 1.7, 2.1, 0], [.3, 4.2, -2, 2.0, 1.5, 1.9, 0], [-.4, 4.3, 1.9, 2.1, 1.6, 2.0, 0], [0, 6.1, .2, 2.0, 1.3, 2.0, 0]];
  blobs.forEach((b, i) => k.ico(b[0], b[1], b[2], b[3], b[4], b[5], i % 2 ? PAL.leafB : PAL.leafD, { c2: i % 2 ? PAL.leafA : PAL.leafB, d: b[6], fjit: .1, ry: R(TAU) }));
  for (let i = 0; i < 7; i++) { const a = R(TAU), r = R(1.3, 2.7); k.ico(Math.cos(a) * r, 2.85 + R(.3), Math.sin(a) * r, .15, .2, .15, '#cdd66c'); }
  return k.geometry();
}
function tplNeem() {
  const k = new Kit();
  k.cyl(0, 0, 0, .2, .32, 3.1, PAL.barkL, { seg: 6, fjit: .08 });
  k.ico(0, 4.9, 0, 2.3, 2.5, 2.3, PAL.leafA, { c2: PAL.leafC, d: 1, fjit: .1 });
  k.ico(1.3, 4.0, .5, 1.5, 1.5, 1.5, PAL.leafB, { c2: PAL.leafA, fjit: .1 }); k.ico(-1.2, 4.2, -.6, 1.6, 1.5, 1.6, PAL.leafB, { c2: PAL.leafC, fjit: .1 }); k.ico(.2, 6.3, -.2, 1.4, 1.3, 1.4, PAL.leafC, { c2: '#74bb7c', fjit: .1 });
  return k.geometry();
}
function tplKikar() {
  const k = new Kit();
  k.cyl(0, 0, 0, .16, .26, 2.6, PAL.bark, { seg: 5, rz: .08 }); k.cyl(-.2, 2.3, 0, .1, .16, 1.7, PAL.bark, { seg: 5, rz: .75 }); k.cyl(-.1, 2.3, 0, .1, .16, 1.6, PAL.bark, { seg: 5, rz: -.7 });
  k.ico(0, 4.3, 0, 3.0, .75, 2.8, PAL.olive, { c2: '#9fbf6f', d: 1, fjit: .1 }); k.ico(1.5, 3.8, .7, 1.7, .55, 1.6, '#76994f', { fjit: .1 }); k.ico(-1.6, 3.9, -.6, 1.8, .55, 1.7, PAL.olive, { fjit: .1 });
  return k.geometry();
}
function tplPalm() {
  const k = new Kit(); let x = 0, y = 0;
  for (let i = 0; i < 7; i++) { const h = 1.15, a = .045 * i; k.cyl(x, y, 0, .19 - .008 * i, .25 - .008 * i, h + .06, i % 2 ? PAL.barkL : PAL.bark, { seg: 6, rz: -a }); x += Math.sin(a) * h; y += Math.cos(a) * h; }
  for (let f = 0; f < 10; f++) {
    const a = f / 10 * TAU + R(.25); let px = x, py = y, pz = 0, pitch = .8 + R(-.2, .15); const L = 1.05;
    for (let j = 0; j < 4; j++) {
      const w = .66 - .14 * j, dx = Math.cos(pitch) * Math.cos(a), dy = Math.sin(pitch), dz = Math.cos(pitch) * Math.sin(a);
      k.add(gBoxC(), { x: px + dx * L / 2, y: py + dy * L / 2, z: pz + dz * L / 2, sx: L * 1.06, sy: .05, sz: w, ry: -a, rz: pitch, c: j < 2 ? PAL.palmD : PAL.palm, fjit: .08 });
      px += dx * L; py += dy * L; pz += dz * L; pitch -= .56;
    }
  }
  k.ico(x, y + .1, 0, .34, .3, .34, PAL.palmD);
  for (let i = 0; i < 3; i++) { const a = R(TAU); k.ico(x + Math.cos(a) * .35, y - .45, Math.sin(a) * .35, .2, .3, .2, PAL.amber); }
  return k.geometry();
}
function tplBush() { const k = new Kit(); k.ico(0, .5, 0, .9, .65, .85, PAL.leafC, { c2: '#7cc083', fjit: .1 }); k.ico(.6, .38, .2, .6, .45, .55, PAL.leafA, { fjit: .1 }); k.ico(-.5, .34, -.3, .55, .42, .6, PAL.leafB, { fjit: .1 }); return k.geometry(); }
function tplRock() { const k = new Kit(); k.ico(0, .22, 0, .6, .36, .5, '#b4bfae', { c2: '#cbd3c2', fjit: .12 }); k.ico(.5, .13, .25, .3, .2, .28, '#a6b3a2', { fjit: .12 }); return k.geometry(); }
function bladeGeo(n, h, w, cBase, cTip, spread) {
  const P = [], C = [], N = [], cb = col(cBase), ct = col(cTip);
  for (let i = 0; i < n; i++) {
    const a = R(TAU), ox = Math.cos(a) * R(spread), oz = Math.sin(a) * R(spread), lean = R(-.3, .3), hh = h * R(.7, 1.15), yaw = R(TAU);
    for (const rot of [0, Math.PI / 2]) {
      const cx = Math.cos(yaw + rot) * w, sz = Math.sin(yaw + rot) * w, tx = ox + lean * hh * Math.cos(a), tz = oz + lean * hh * Math.sin(a);
      P.push(ox - cx, 0, oz - sz, ox + cx, 0, oz + sz, tx, hh, tz);
      C.push(cb.r, cb.g, cb.b, cb.r, cb.g, cb.b, ct.r, ct.g, ct.b); N.push(0, 1, 0, 0, 1, 0, 0, 1, 0);
    }
  }
  const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(P, 3)); g.setAttribute('color', new THREE.Float32BufferAttribute(C, 3)); g.setAttribute('normal', new THREE.Float32BufferAttribute(N, 3));
  g.computeBoundingSphere(); return g;
}
function instanced(scene, tpl, material, list, cast = true, chunk = 150) {
  const groups = {}; for (const it of list) { const key = Math.floor(it.x / chunk); (groups[key] || (groups[key] = [])).push(it); }
  const r0 = tpl.boundingSphere.radius, m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), p = new THREE.Vector3(), s = new THREE.Vector3(), out = [];
  for (const key in groups) {
    const arr = groups[key], g = new THREE.BufferGeometry();
    for (const n in tpl.attributes) g.setAttribute(n, tpl.attributes[n]);
    const box = new THREE.Box3(); let ms = 1;
    const im = new THREE.InstancedMesh(g, material, arr.length);
    arr.forEach((it, i) => { const sc = it.s || 1; q.setFromAxisAngle(YAX, it.ry || 0); m4.compose(p.set(it.x, it.y, it.z), q, s.set(sc, sc * (it.sy || 1), sc)); im.setMatrixAt(i, m4); box.expandByPoint(p); ms = Math.max(ms, sc * (it.sy || 1)); });
    g.boundingSphere = new THREE.Sphere(); box.getBoundingSphere(g.boundingSphere); g.boundingSphere.radius += r0 * ms + 2;
    im.castShadow = cast; im.receiveShadow = false; im.matrixAutoUpdate = false; im.instanceMatrix.needsUpdate = true; scene.add(im); out.push(im);
  }
  return out;
}
function isFree(x, z, m) {
  if (roadDist(x, z) < m) return false;
  if (inRiver(x, z, 4)) return false;
  if (Math.hypot(x - POND.x, z - POND.z) < POND.r + 3) return false;
  for (const o of OCC) { const dx = x - o.x, dz = z - o.z; if (dx * dx + dz * dz < (o.r + m * .3) * (o.r + m * .3)) return false; }
  return true;
}
const TREES = { mango: [], neem: [], kikar: [], palm: [], bush: [], rock: [], grass: [], wheat: [], crop: [], reed: [], flowerW: [], flowerY: [] };
const CAMPTS = [], GRASS = [];
const CLEAR = { mango: 7, neem: 6, kikar: 6.5, palm: 5.5, bush: 2.6, rock: 2 };
const TOP = { mango: 7.6, neem: 7.8, kikar: 5.2, palm: 9.4, bush: 1.2, rock: 1 };
function nearCam(x, z, r, top) { const rs = r * r * .42; for (const c of CAMPTS) { if (c.y > top + (c.sight ? 1 : 5)) continue; const dx = c.x - x, dz = c.z - z; if (dx * dx + dz * dz < (c.sight ? rs : r * r)) return true; } return false; }
function plant(kind, x, z, s, ry) { if (CLEAR[kind] && nearCam(x, z, CLEAR[kind] * (s || 1), TOP[kind] * (s || 1))) return; TREES[kind].push({ x, z, y: H(x, z) - .05, s: s || 1, ry: ry === undefined ? R(TAU) : ry }); }
function buildPlants(scene, LOW) {
  const D = LOW ? .55 : 1;
  // mango orchard in rows, the crop Multan and Muzaffargarh are known for
  for (let x = ORCHARD.x0 + 4; x < ORCHARD.x1; x += 9.5) for (let z = ORCHARD.z0 + 4; z < ORCHARD.z1; z += 9.5) plant('mango', x + R(-.8, .8), z + R(-.8, .8), R(.9, 1.15));
  for (const [x, z] of [[-64, 30], [66, 24], [252, -40], [262, -52], [338, 36], [352, -36], [470, -6], [596, -66], [628, -20]]) if (isFree(x, z, 7)) plant('mango', x, z, R(1, 1.25));
  // shisham and neem lining the road, the way canal roads are planted in Punjab
  for (let i = 30; i < ROAD_N - 6; i += 9) {
    const p = roadS[i], t = roadT[i];
    for (const side of [-1, 1]) {
      if (side === 1 && (i % 27)) continue;
      const off = 6.2 + R(1.4), x = p.x - t.z * side * off, z = p.z + t.x * side * off;
      if (padAt(x, z).k > .2 || !isFree(x, z, 5) || inRiver(x, z, 12)) continue;
      plant(rand() < .7 ? 'neem' : 'kikar', x, z, R(.85, 1.2));
    }
  }
  let tries = 0, n = 0;
  while (n < 240 * D && tries++ < 6000) { const x = R(-170, 700), z = R(-240, 230); if (!isFree(x, z, 9) || fieldAt(x, z) || padAt(x, z).k > .35) continue; const az = Math.abs(z + 8); plant(az > 120 ? (rand() < .5 ? 'neem' : 'kikar') : pick(['neem', 'kikar', 'kikar', 'neem', 'mango']), x, z, R(.8, 1.35) * (az > 120 ? 1.25 : 1)); n++; }
  // date palms: clustered on the river banks and round the villages
  n = 0; tries = 0;
  while (n < 54 * D && tries++ < 4000) { const z = R(-200, 190), side = rand() < .5 ? -1 : 1, x = riverX(z) + side * (riverHW(z) + R(9, 26)); if (!isFree(x, z, 6) || fieldAt(x, z)) continue; plant('palm', x, z, R(.85, 1.25)); n++; }
  for (const [x, z] of [[264, -8], [268, -12], [336, -8], [340, -34], [322, 6], [258, -30], [540, -52], [544, -56], [612, -50], [616, -44], [530, -64], [524, -70], [500, -70], [28, 28], [34, 31], [-78, -30], [72, -22], [88, 14]]) if (isFree(x, z, 4)) plant('palm', x, z, R(.9, 1.25));
  n = 0; tries = 0;
  while (n < 520 * D && tries++ < 9000) { const x = R(-160, 690), z = R(-170, 160); if (!isFree(x, z, 5) || fieldAt(x, z) || padAt(x, z).k > .5) continue; plant('bush', x, z, R(.6, 1.5)); n++; }
  n = 0; tries = 0;
  while (n < 150 * D && tries++ < 4000) { const x = R(-160, 690), z = R(-170, 160); if (!isFree(x, z, 4.4) || fieldAt(x, z) || padAt(x, z).k > .6) continue; plant('rock', x, z, R(.5, 1.6)); n++; }
  // grass close to where the camera travels, in loose clumps
  n = 0; tries = 0;
  while (n < 7600 * D && tries++ < 60000) {
    const i = (rand() * ROAD_N) | 0, p = roadS[i], t = roadT[i], off = (rand() < .5 ? -1 : 1) * (3.8 + Math.pow(rand(), 1.6) * 44), x = p.x - t.z * off + R(-2, 2), z = p.z + t.x * off + R(-2, 2);
    if (vnoise(x * .16, z * .16) < .34) continue;
    const pd = padAt(x, z);
    if (!isFree(x, z, 3.7) || fieldAt(x, z) || pd.kind === 'town' && pd.k > .15 || (pd.k > .7 && rand() < .82)) continue;
    const r = rand(); plant(r < .92 ? 'grass' : r < .965 ? 'flowerW' : 'flowerY', x, z, R(.7, 1.5)); n++;
  }
  // tufts and wild flowers between the houses
  for (const [x0, x1, z0, z1, cnt] of [[250, 352, -58, 34, 620], [524, 634, -84, -12, 760]]) {
    n = 0; tries = 0;
    while (n < cnt * D && tries++ < 9000) { const x = R(x0, x1), z = R(z0, z1); if (vnoise(x * .2 + 7, z * .2) < .42 || !isFree(x, z, 3.9) || fieldAt(x, z)) continue; const r = rand(); plant(r < .86 ? 'grass' : r < .94 ? 'flowerW' : 'flowerY', x, z, R(.7, 1.4)); n++; }
    n = 0; tries = 0;
    while (n < 26 * D && tries++ < 900) { const x = R(x0, x1), z = R(z0, z1); if (!isFree(x, z, 4.6) || fieldAt(x, z)) continue; plant('bush', x, z, R(.5, 1.0)); n++; }
  }
  // standing crop: low ridges that follow the ground, with ears of wheat on the plots nearest the road
  const ck = new Kit();
  for (const f of FIELDS) {
    if (f.row > (LOW ? 0 : 1)) continue;
    const c = CROPS[f.type], hgt = { wheat: .5, ripe: .56, paddy: .24, fodder: .72, plough: .16 }[f.type], seg = 4.6, ry = -Math.atan2(f.sin, f.cos);
    for (let lz = -f.d / 2 + 1.5; lz < f.d / 2 - 1; lz += 1.9) {
      const n = Math.max(1, Math.round((f.w - 2) / seg)), L = (f.w - 2) / n;
      for (let i = 0; i < n; i++) {
        const lx = -f.w / 2 + 1 + L * (i + .5), x = f.x + lx * f.cos - lz * f.sin, z = f.z + lx * f.sin + lz * f.cos;
        ck.taper(x, H(x, z) - .12, z, L + .08, hgt + .12, 1.15, c[1], { c2: c[0], k: .55, ry, jit: .05 });
        if (f.row === 0 && (f.type === 'ripe' || f.type === 'wheat') && !LOW) for (let j = 0; j < 3; j++) { const jx = lx + (j - 1) * L / 3 + R(-.3, .3), xx = f.x + jx * f.cos - lz * f.sin, zz = f.z + jx * f.sin + lz * f.cos; TREES[f.type === 'ripe' ? 'wheat' : 'crop'].push({ x: xx, z: zz, y: H(xx, zz) + hgt * .5, s: R(.55, .8), ry: R(TAU) }); }
      }
    }
  }
  scene.add(ck.mesh(M.world, true, true));
  // reeds at the water's edge
  n = 0; tries = 0;
  while (n < 260 * D && tries++ < 3000) { const z = R(-150, 130), side = rand() < .5 ? -1 : 1, x = riverX(z) + side * (riverHW(z) + R(-2.5, 3)); if (Math.abs(z + 16) < 9) continue; TREES.reed.push({ x, z, y: H(x, z) - .1, s: R(.8, 1.5), ry: R(TAU) }); n++; }
  for (let i = 0; i < 46; i++) { const a = R(TAU), r = POND.r + R(-2.4, 1.5), x = POND.x + Math.cos(a) * r, z = POND.z + Math.sin(a) * r; TREES.reed.push({ x, z, y: H(x, z) - .1, s: R(.8, 1.4), ry: R(TAU) }); }

  instanced(scene, tplMango(), M.tree, TREES.mango); instanced(scene, tplNeem(), M.tree, TREES.neem); instanced(scene, tplKikar(), M.tree, TREES.kikar);
  instanced(scene, tplPalm(), M.tree, TREES.palm); instanced(scene, tplBush(), M.world, TREES.bush); instanced(scene, tplRock(), M.world, TREES.rock);
  M.grass.side = THREE.DoubleSide;
  GRASS.push(...instanced(scene, bladeGeo(6, .42, .05, '#62a85f', '#b6de8c', .3), M.grass, TREES.grass, false, 110));
  instanced(scene, bladeGeo(5, .7, .05, '#7fb866', '#d6e894', .34), M.grass, TREES.crop, false, 110);
  instanced(scene, bladeGeo(6, .75, .05, '#b9b468', '#f0e6a0', .3), M.grass, TREES.wheat, false, 110);
  instanced(scene, bladeGeo(5, 1.7, .06, '#4d9160', '#8a7a4e', .3), M.grass, TREES.reed, false, 110);
  const fl = (c) => { const k = new Kit(); k.cyl(0, 0, 0, .012, .014, .32, '#5fa368', { seg: 3 }); k.ico(0, .34, 0, .07, .05, .07, c); k.cyl(.12, 0, .05, .012, .014, .24, '#5fa368', { seg: 3 }); k.ico(.12, .26, .05, .06, .045, .06, c); return k.geometry(); };
  instanced(scene, fl('#fbf7e6'), M.world, TREES.flowerW, false, 110); instanced(scene, fl('#f3d56a'), M.world, TREES.flowerY, false, 110);
}
/* ---------- sign and screen textures ---------- */
const texStudioSign = () => canvasTex(1024, 224, (x, w, h) => {
  x.fillStyle = '#1f5a43'; x.fillRect(0, 0, w, h); x.strokeStyle = '#f3ecd2'; x.lineWidth = 6; x.strokeRect(12, 12, w - 24, h - 24);
  drawCardIcon(x, 150, h / 2, 130, '#f3ecd2', '#1f5a43');
  x.fillStyle = '#f7f4e6'; x.font = '600 132px ' + FD; x.textBaseline = 'middle'; x.fillText('Ilm Card', 250, h / 2 - 4);
  x.font = '500 40px ' + FB; x.fillStyle = '#a8cdb0'; x.textAlign = 'right'; x.fillText('Studio', w - 44, h / 2 + 42); x.textAlign = 'left';
});
const texWhiteboard = () => canvasTex(640, 336, (x, w, h) => {
  x.fillStyle = '#fbfaf2'; x.fillRect(0, 0, w, h);
  x.fillStyle = '#1f5a43'; x.font = '600 44px ' + FB; x.fillText('Class 6 Maths', 34, 62); x.fillRect(34, 76, 300, 4);
  x.font = '500 68px ' + FD; x.fillText('3/4 + 1/4 = 1', 34, 176);
  x.strokeStyle = '#1f5a43'; x.lineWidth = 6; x.beginPath(); x.arc(520, 190, 78, 0, TAU); x.stroke();
  x.fillStyle = '#7fbf93'; x.beginPath(); x.moveTo(520, 190); x.arc(520, 190, 75, -Math.PI / 2, Math.PI); x.closePath(); x.fill();
  x.fillStyle = '#f2b24f'; x.beginPath(); x.moveTo(520, 190); x.arc(520, 190, 75, Math.PI, Math.PI * 1.5); x.closePath(); x.fill();
  x.beginPath(); x.moveTo(520, 112); x.lineTo(520, 268); x.moveTo(442, 190); x.lineTo(598, 190); x.stroke();
  x.fillStyle = '#3f7d5c'; x.font = '500 34px ' + FB; x.fillText('Homework: page 14, Q1 to Q5', 34, 286);
});
const texShopSign = () => canvasTex(768, 176, (x, w, h) => {
  x.fillStyle = '#f3ecd2'; x.fillRect(0, 0, w, h); x.fillStyle = '#1f5a43'; x.fillRect(0, 0, w, 14); x.fillRect(0, h - 14, w, 14);
  x.font = '700 78px ' + FB; x.textAlign = 'center'; x.fillText('MOBILE SHOP', w / 2, 98);
  x.font = '500 34px ' + FB; x.fillStyle = '#3f7d5c'; x.fillText('Balance, cards, repair', w / 2, 142);
});
const texBanner = () => canvasTex(320, 560, (x, w, h) => {
  x.fillStyle = '#1f5a43'; x.fillRect(0, 0, w, h); x.fillStyle = '#f2b24f'; x.fillRect(0, 0, w, 16);
  drawCardIcon(x, w / 2, 150, 170, '#f3ecd2', '#1f5a43');
  x.fillStyle = '#f7f4e6'; x.textAlign = 'center'; x.font = '600 70px ' + FD; x.fillText('Ilm Card', w / 2, 320);
  x.font = '500 34px ' + FB; x.fillStyle = '#cfe6cf'; x.fillText('yahan milta hai', w / 2, 372);
  x.fillStyle = '#f2b24f'; x.fillRect(40, 420, w - 80, 86); x.fillStyle = '#1f3d31'; x.font = '700 40px ' + FB; x.fillText('Rs 500 a month', w / 2, 476);
});
const texVan = () => canvasTex(640, 200, (x, w, h) => {
  x.fillStyle = '#f3ecd2'; x.fillRect(0, 0, w, h); x.fillStyle = '#2f7d5b'; x.fillRect(0, h - 46, w, 46);
  drawCardIcon(x, 86, 78, 100, '#2f7d5b', '#f3ecd2');
  x.fillStyle = '#1f5a43'; x.font = '600 92px ' + FD; x.textBaseline = 'middle'; x.fillText('Ilm Card', 160, 80); x.textBaseline = 'alphabetic';
  x.fillStyle = '#f3ecd2'; x.font = '600 26px ' + FB; x.fillText('Ilm bhi, tarbiyat bhi', 26, h - 14);
});
const texPhone = () => canvasTex(320, 180, (x, w, h) => {
  x.fillStyle = '#eaf6e6'; x.fillRect(0, 0, w, h);
  x.fillStyle = '#fbfaf2'; x.fillRect(120, 18, 180, 104); x.strokeStyle = '#1f5a43'; x.lineWidth = 4; x.strokeRect(120, 18, 180, 104);
  x.fillStyle = '#1f5a43'; x.font = '600 30px ' + FD; x.fillText('3/4 + 1/4', 136, 62); x.font = '600 30px ' + FD; x.fillText('= 1', 136, 100);
  x.fillStyle = '#2f7d5b'; x.beginPath(); x.moveTo(26, 150); x.quadraticCurveTo(64, 60, 104, 150); x.fill();     // teacher
  x.fillStyle = '#c68e63'; x.beginPath(); x.arc(64, 62, 22, 0, TAU); x.fill(); x.fillStyle = '#e9cf8a'; x.beginPath(); x.arc(64, 54, 24, Math.PI, TAU); x.fill();
  x.fillStyle = '#1f5a43'; x.fillRect(0, 148, w, 32); x.fillStyle = '#5c8f77'; x.fillRect(46, 162, 250, 5); x.fillStyle = '#f2b24f'; x.fillRect(46, 162, 110, 5); x.beginPath(); x.arc(156, 164, 7, 0, TAU); x.fill();
  x.fillStyle = '#f7f4e6'; x.beginPath(); x.moveTo(16, 155); x.lineTo(16, 173); x.lineTo(32, 164); x.fill();
});

/* ---------- building blocks ---------- */
function atAll(kits, x, y, z, ry, fn) { const go = i => i === kits.length ? fn() : kits[i].at(x, y, z, ry, () => go(i + 1)); go(0); }
const CLOTH = [PAL.rose, PAL.mustard, PAL.teal, PAL.white, PAL.plum, PAL.sky, '#7fbf93'];

function townBlock(k, G, x, z, ry, w, d, floors, wall) {
  occ(x, z, Math.max(w, d) * .62);
  atAll([k, G], x, 0, z, ry, () => {
    const fh = 3.15, h = floors * fh + .25;
    k.box(0, 0, 0, w, h, d, wall, { jit: .03 });
    k.box(0, h, d / 2 - .1, w, .5, .2, wall); k.box(0, h, -d / 2 + .1, w, .5, .2, wall); k.box(w / 2 - .1, h, 0, .2, .5, d, wall); k.box(-w / 2 + .1, h, 0, .2, .5, d, wall);
    k.box(0, 0, d / 2 + .5, w + .4, .16, 1.2, PAL.concrete);
    const n = Math.max(2, Math.round(w / 3.3)), bw = w / n;
    for (let i = 0; i < n; i++) {
      const sx = (i - (n - 1) / 2) * bw, open = rand() < .55;
      k.box(sx, .16, d / 2 + .02, bw - .7, 2.35, .08, open ? PAL.glass : pick([PAL.concreteD, '#8fb2a0', PAL.trim]));
      if (open) G.box(sx, .5, d / 2 + .07, bw - 1.3, 1.5, .04, PAL.amber);
      k.box(sx, 2.62, d / 2 + .52, bw - .3, .07, 1.05, pick([PAL.trim, PAL.cream, PAL.mustard, PAL.teal, '#9fc7a5']), { rx: .28 });
    }
    for (let f = 1; f < floors; f++) {
      k.box(0, f * fh, d / 2 + .03, w + .12, .15, .1, PAL.white);
      for (let i = 0; i < n; i++) {
        const sx = (i - (n - 1) / 2) * bw;
        k.box(sx, f * fh + .85, d / 2 + .02, 1.25, 1.45, .1, PAL.white);
        if (rand() < .6) G.box(sx, f * fh + .95, d / 2 + .08, 1.02, 1.25, .05, PAL.amber); else k.box(sx, f * fh + .95, d / 2 + .08, 1.02, 1.25, .05, PAL.glass);
        if (rand() < .3) k.box(sx, f * fh + .55, d / 2 + .35, 1.5, .08, .6, PAL.concrete);
      }
    }
    k.cyl(w * .22, h + .7, -d * .18, .72, .72, 1.25, pick([PAL.teal, '#6fa9a2', PAL.concreteD]), { seg: 8 });
    for (const [ax, az] of [[-.5, -.5], [.5, -.5], [-.5, .5], [.5, .5]]) k.box(w * .22 + ax, h, -d * .18 + az, .1, .7, .1, PAL.iron);
    if (rand() < .55) { k.box(-w * .22, h, -d * .22, 2.6, 2.3, 2.8, wall, { c2: PAL.white }); k.box(-w * .22, h + 2.3, -d * .22, 2.9, .14, 3.1, PAL.concrete); k.box(-w * .22, h, -d * .22 + 1.42, .9, 1.8, .06, pick([PAL.trim, PAL.teal, PAL.wood])); }
    if (rand() < .5) { pottedPlant(k, w * .34, h, d * .3, .8); pottedPlant(k, w * .2, h, d * .34, .6); pottedPlant(k, w * .4, h, d * .12, .7); }
    if (rand() < .45) { const cx = R(-w * .1, w * .2); k.cyl(cx - 1.6, h, d * .08, .03, .03, 1.7, PAL.iron, { seg: 4 }); k.cyl(cx + 1.6, h, d * .08, .03, .03, 1.7, PAL.iron, { seg: 4 }); k.box(cx, h + 1.62, d * .08, 3.2, .02, .02, PAL.dark, { jit: 0 }); for (let i = 0; i < 4; i++) k.box(cx - 1.2 + i * .8, h + .9, d * .08, .55, .72, .03, pick(CLOTH)); }
    if (rand() < .6) { k.cyl(-w * .25, h, d * .15, .05, .05, 2.2, PAL.iron, { seg: 4 }); k.box(-w * .25, h + 2.0, d * .15, .9, .05, .05, PAL.iron); k.box(-w * .25, h + 1.6, d * .15, .6, .05, .05, PAL.iron); }
  });
}

function mudHouse(k, G, x, z, ry, w, d, h, o = {}) {
  occ(x, z, Math.max(w, d) * .6);
  atAll([k, G], x, 0, z, ry, () => {
    k.box(0, 0, 0, w + .8, .32, d + .8, PAL.mudD);
    k.taper(0, .3, 0, w, h, d, PAL.mud, { c2: PAL.mudL, k: .95 });
    const top = h + .3, tw = w * .95, td = d * .95;
    k.box(0, top, td / 2 - .13, tw, .3, .26, PAL.mudL); k.box(0, top, -td / 2 + .13, tw, .3, .26, PAL.mudL); k.box(tw / 2 - .13, top, 0, .26, .3, td, PAL.mudL); k.box(-tw / 2 + .13, top, 0, .26, .3, td, PAL.mudL);
    for (let i = 0; i < Math.floor(w / 1.15); i++) k.cyl(-w / 2 + .75 + i * 1.15, h - .12, d / 2 - .3, .075, .075, .62, PAL.woodD, { seg: 5, rx: Math.PI / 2 });
    const dx = o.door ?? -w * .2, dc = o.doorC || pick([PAL.teal, PAL.trim, '#5f8f9a', PAL.wood]);
    k.box(dx, .3, d / 2 - .06, 1.2, 2.05, .12, PAL.woodD); k.box(dx, .3, d / 2 - .01, .98, 1.92, .1, dc); k.box(dx, 2.3, d / 2 - .04, 1.4, .14, .16, PAL.wood);
    k.box(dx, .16, d / 2 + .5, 1.6, .16, .7, PAL.mudD);
    const wx = o.win ?? w * .24;
    k.box(wx, 1.35, d / 2 - .06, 1.0, .9, .12, PAL.woodD); G.box(wx, 1.42, d / 2 - .0, .8, .74, .06, PAL.amber);
    k.box(wx - .52, 1.4, d / 2 + .04, .12, .8, .04, dc); k.box(wx + .52, 1.4, d / 2 + .04, .12, .8, .04, dc);
    if (o.side !== false) { k.box(w / 2 - .14, 1.5, -d * .15, .1, .7, .7, PAL.woodD); G.box(w / 2 - .09, 1.56, -d * .15, .06, .56, .56, PAL.amber); }
    k.cyl(-w / 2 - .02, h - .1, d * .2, .06, .06, .5, PAL.terracotta, { seg: 5, rz: Math.PI / 2 });
    if (o.ladder) { for (const s of [-.28, .28]) k.cyl(w / 2 + 1.1, 0, d * .1 + s, .04, .04, h + 1.1, PAL.wood, { seg: 4, rz: .26 }); for (let i = 1; i < 8; i++) k.box(w / 2 + 1.1 - i * .11, i * .42, d * .1, .05, .05, .6, PAL.wood); }
    if (o.room) { k.taper(w * .2, top, -d * .12, w * .46, 2.3, d * .58, PAL.mudL, { c2: '#e8d7b2', k: .95 }); k.box(w * .2, top + .25, d * .17, .8, 1.5, .1, PAL.teal); G.box(w * .2 + w * .15, top + 1, d * .17, .5, .5, .06, PAL.amber); }
    if (o.cot) charpai(k, -w * .15, td * .05, .2, top);
  });
}
function mudWall(k, x1, z1, x2, z2, h = 1.15, t = .42) {
  const L = Math.hypot(x2 - x1, z2 - z1), ry = -Math.atan2(z2 - z1, x2 - x1), mx = (x1 + x2) / 2, mz = (z1 + z2) / 2;
  k.box(mx, 0, mz, L + t, h, t, PAL.mud, { ry, c2: PAL.mudL }); k.box(mx, h, mz, L + t + .08, .13, t + .12, PAL.mudL, { ry });
}
function charpai(k, x, z, ry, y = 0) {
  k.at(x, y, z, ry, () => {
    const L = 1.95, W = .95, hh = .46;
    for (const sx of [-1, 1]) for (const sz of [-1, 1]) k.cyl(sx * (L / 2 - .05), 0, sz * (W / 2 - .05), .045, .05, hh + .1, PAL.wood, { seg: 5 });
    k.box(0, hh - .05, W / 2 - .05, L, .08, .08, PAL.wood); k.box(0, hh - .05, -W / 2 + .05, L, .08, .08, PAL.wood); k.box(L / 2 - .05, hh - .05, 0, .08, .08, W, PAL.wood); k.box(-L / 2 + .05, hh - .05, 0, .08, .08, W, PAL.wood);
    for (let i = 0; i < 8; i++) k.box(-L / 2 + .17 + i * .23, hh - .03, 0, .2, .035, W - .14, i % 2 ? '#eadfb6' : '#d5c48e', { jit: 0 });
  });
}
function handPump(k, x, z, ry, withHandle = true) {
  k.at(x, 0, z, ry, () => {
    k.box(0, 0, 0, 1.7, .12, 1.5, PAL.concrete); k.box(.55, .12, 0, .5, .05, .6, PAL.concreteD);
    k.cyl(0, .12, 0, .085, .1, 1.0, PAL.trimD, { seg: 6 }); k.box(0, 1.1, 0, .2, .3, .2, PAL.trimD);
    k.cyl(.08, .82, 0, .04, .05, .46, PAL.trimD, { seg: 5, rz: -Math.PI / 2 });
    if (withHandle) k.box(-.45, 1.28, 0, 1.0, .06, .06, PAL.iron, { rz: .32 });
  });
}
function matka(k, x, y, z, s = 1) { k.ico(x, y + .24 * s, z, .27 * s, .25 * s, .27 * s, PAL.terracotta, { d: 1, c2: '#d59468' }); k.cyl(x, y + .44 * s, z, .13 * s, .1 * s, .1 * s, PAL.terracotta, { seg: 6 }); }
function haystack(k, x, z, r) { occ(x, z, r + .6); k.dome(x, 0, z, r, r * 1.3, PAL.strawD, { c2: '#ecdc94', fjit: .06 }); k.cyl(x, r * 1.2, z, .04, .05, .7, PAL.wood, { seg: 4 }); }
function clothesline(k, x1, z1, x2, z2) {
  const L = Math.hypot(x2 - x1, z2 - z1), ry = -Math.atan2(z2 - z1, x2 - x1);
  k.cyl(x1, 0, z1, .05, .06, 2.15, PAL.wood, { seg: 5 }); k.cyl(x2, 0, z2, .05, .06, 2.15, PAL.wood, { seg: 5 });
  k.box((x1 + x2) / 2, 2.05, (z1 + z2) / 2, L, .025, .025, PAL.dark, { ry });
  const n = Math.floor(L / .9);
  for (let i = 0; i < n; i++) { const t = (i + .6) / (n + .2), hh = R(.55, .95); k.box(lerp(x1, x2, t), 2.05 - hh, lerp(z1, z2, t), R(.5, .72), hh, .03, pick(CLOTH), { ry: ry + R(-.08, .08) }); }
}
function pottedPlant(k, x, y, z, s = 1) { k.cyl(x, y, z, .24 * s, .18 * s, .34 * s, PAL.terracotta, { seg: 7 }); k.ico(x, y + .7 * s, z, .36 * s, .44 * s, .36 * s, PAL.leafC, { c2: '#86c98c', fjit: .1 }); k.ico(x + .16 * s, y + .5 * s, z + .1 * s, .24 * s, .26 * s, .24 * s, PAL.leafA, { fjit: .1 }); }
function carton(k, x, y, z, ry, s = 1) { k.box(x, y, z, .62 * s, .46 * s, .46 * s, '#d9c69a', { ry }); k.box(x, y + .46 * s, z, .64 * s, .02, .1 * s, PAL.trim, { ry, jit: 0 }); }
function bigTree(k, x, z, s = 1) {
  occ(x, z, 4.5 * s);
  k.at(x, 0, z, R(TAU), () => {
    k.cyl(0, 0, 0, .55, .85, 3.4, PAL.bark, { seg: 7, fjit: .08 });
    k.cyl(.3, 2.7, 0, .22, .38, 2.4, PAL.bark, { seg: 5, rz: -.8 }); k.cyl(-.3, 2.7, .2, .22, .38, 2.3, PAL.bark, { seg: 5, rz: .85, ry: .7 }); k.cyl(0, 2.9, -.3, .2, .34, 2.2, PAL.bark, { seg: 5, rx: -.8 });
    const b = [[0, 6.6, 0, 4.2, 2.8, 4.0, 1], [3, 5.6, 1, 2.8, 2.0, 2.6, 1], [-3, 5.7, -.6, 2.9, 2.1, 2.7, 1], [.4, 5.5, -3, 2.6, 1.9, 2.5, 0], [-.6, 5.6, 3, 2.7, 1.9, 2.6, 0], [0, 8.4, .3, 2.6, 1.6, 2.6, 0], [2, 7.4, -1.8, 2, 1.4, 2, 0], [-2.2, 7.5, 1.6, 2.1, 1.4, 2, 0]];
    b.forEach((v, i) => k.ico(v[0], v[1], v[2], v[3], v[4], v[5], i % 2 ? PAL.leafB : PAL.leafD, { c2: i % 2 ? PAL.leafC : PAL.leafA, d: v[6], fjit: .1, ry: R(TAU) }));
  }, s);
}

/* ---------- Multan: the studio and its street ---------- */
const SPOT = { studio: new THREE.Vector3(0, 0, -13), shop: new THREE.Vector3(299, 0, 0), phone: new THREE.Vector3(555.6, .5, -43.5), court: new THREE.Vector3(556.6, 0, -43.5) };
function buildTown(scene, k, G, L) {
  const S = SPOT.studio, W = 14, Dp = 9, f1 = 3.7, f2 = 3.1;
  occ(S.x, S.z, 10); occ(6, 0, 12);
  atAll([k, G, L], S.x, 0, S.z, 0, () => {
    k.box(0, 0, 0, W + 1.4, .28, Dp + 1.6, PAL.concrete); k.box(0, 0, Dp / 2 + 1.5, 6, .14, 1.4, PAL.concrete);
    k.box(0, .28, -.1, W - .5, .05, Dp - .5, '#a9cfae', { jit: 0 });
    k.box(-1.6, .33, .2, 6.4, .03, 4.2, '#3f8f6a', { jit: 0 }); k.box(-1.6, .35, .2, 5.8, .02, 3.6, '#57a67c', { jit: 0 });   // rug
    k.box(0, .28, -Dp / 2 + .15, W, f1, .3, PAL.plaster, { c2: PAL.white }); k.box(-W / 2 + .15, .28, 0, .3, f1, Dp, PAL.plasterG); k.box(W / 2 - .15, .28, 0, .3, f1, Dp, PAL.plasterG);
    k.box(-W / 2 + .3, .28, Dp / 2 - .3, .6, f1, .6, PAL.plasterG); k.box(W / 2 - .3, .28, Dp / 2 - .3, .6, f1, .6, PAL.plasterG);
    const y2 = .28 + f1;
    k.box(0, y2, 0, W + .4, f2, Dp + .4, PAL.plaster, { c2: PAL.white, jit: .01 }); k.box(0, y2, Dp / 2 + .22, W + .5, .4, .12, PAL.trim, { jit: 0 });
    for (let i = 0; i < 4; i++) { const x = -4.8 + i * 3.2; k.box(x, y2 + .95, Dp / 2 + .19, 1.9, 1.5, .1, PAL.white); G.box(x, y2 + 1.05, Dp / 2 + .25, 1.6, 1.3, .06, PAL.amber); k.box(x, y2 + .8, Dp / 2 + .45, 2.1, .07, .5, PAL.trim); pottedPlant(k, x - .6, y2 + .87, Dp / 2 + .5, .5); }
    const top = y2 + f2;
    k.box(0, top, Dp / 2 + .1, W + .4, .55, .2, PAL.plaster); k.box(0, top, -Dp / 2 - .1, W + .4, .55, .2, PAL.plaster); k.box(W / 2 + .1, top, 0, .2, .55, Dp + .4, PAL.plaster); k.box(-W / 2 - .1, top, 0, .2, .55, Dp + .4, PAL.plaster);
    k.cyl(-4.6, top + .8, -2.2, .9, .9, 1.5, PAL.teal, { seg: 9 }); for (const [ax, az] of [[-.6, -.6], [.6, -.6], [-.6, .6], [.6, .6]]) k.box(-4.6 + ax, top, -2.2 + az, .12, .8, .12, PAL.iron);
    k.cyl(4.8, top, -2.6, .06, .08, 1.3, PAL.iron, { seg: 5 }); k.dome(4.8, top + 1.15, -2.3, .8, .32, PAL.white, { rx: 1.0 });
    k.box(-4.3, top, Dp / 2, .16, 1.0, .16, PAL.iron); k.box(4.3, top, Dp / 2, .16, 1.0, .16, PAL.iron); k.box(0, top + .75, Dp / 2 + .02, 9.4, 2.3, .16, PAL.trimD, { jit: 0 });
    // inside: whiteboard, lights, camera, desk with the card duplicator
    k.box(-2.6, 1.05, -Dp / 2 + .32, 4.7, 2.5, .08, PAL.wood, { jit: 0 }); k.box(-2.6, 1.0, -Dp / 2 + .42, 4.2, .08, .16, PAL.concreteD);
    for (const [x, z, ry] of [[-5.3, 1.0, .7], [1.9, 1.9, -.5]]) { k.cyl(x, .28, z, .03, .03, 2.3, PAL.iron, { seg: 4 }); for (let i = 0; i < 3; i++) k.cyl(x, .28, z, .02, .02, .7, PAL.iron, { seg: 3, rz: 1.1, ry: i * 2.09 }); k.box(x, 2.3, z, .9, 1.0, .3, PAL.dark, { ry }); L.box(x + Math.sin(ry) * .17, 2.36, z + Math.cos(ry) * .17, .78, .88, .04, '#fff6d8', { ry }); }
    for (let i = 0; i < 3; i++) k.cyl(-1.2, .28, 2.3, .02, .025, 1.5, PAL.iron, { seg: 3, rz: .24, ry: i * 2.09 + .5 });
    k.box(-1.2, 1.68, 2.3, .34, .26, .5, PAL.dark); k.cyl(-1.2, 1.81, 2.02, .1, .12, .22, PAL.iron, { seg: 8, rx: -Math.PI / 2 }); L.box(-1.07, 1.9, 2.52, .05, .05, .03, '#ff5a3c');
    k.box(4.4, 1.0, -2.6, 3.4, .08, 1.3, PAL.wood); for (const [ax, az] of [[-1.55, -.5], [1.55, -.5], [-1.55, .5], [1.55, .5]]) k.box(4.4 + ax, .28, -2.6 + az, .09, .74, .09, PAL.woodD);
    k.box(3.5, 1.08, -2.6, .7, .04, .5, PAL.concreteD); k.box(3.5, 1.1, -2.86, .7, .46, .04, PAL.dark, { rx: -.2 }); L.box(3.5, 1.15, -2.83, .62, .38, .02, '#d9f3df', { rx: -.2 });
    k.box(5.2, 1.08, -2.7, .55, .95, .5, PAL.dark); for (let r = 0; r < 5; r++) for (let c = 0; c < 2; c++) { k.box(5.06 + c * .26, 1.2 + r * .16, -2.44, .2, .03, .02, PAL.concreteD); L.box(5.13 + c * .26, 1.26 + r * .16, -2.44, .03, .03, .02, '#7dffb0'); }
    for (let i = 0; i < 4; i++) k.box(4.3 + (i % 2) * .22, 1.08 + Math.floor(i / 2) * .05, -2.25, .2, .05, .16, i % 2 ? PAL.trim : PAL.cream);
    k.box(6.3, .28, -1.2, .9, 2.6, 2.6, PAL.wood); for (let s = 0; s < 4; s++) for (let b = 0; b < 7; b++) k.box(5.92, .5 + s * .62, -2.3 + b * .34, .22, R(.36, .5), .2, pick(CLOTH), { jit: .05 });
    pottedPlant(k, -6.2, .28, 3.4, 1.3); pottedPlant(k, 6.2, .28, 3.5, 1.1); pottedPlant(k, -6.2, .28, -3.6, .9);
    // wall: clock, timetable, a shelf of plants, the recording light
    k.cyl(1.3, 2.75, -Dp / 2 + .3, .36, .36, .06, PAL.trimD, { seg: 14, rx: Math.PI / 2 }); k.cyl(1.3, 2.75, -Dp / 2 + .33, .3, .3, .05, PAL.white, { seg: 14, rx: Math.PI / 2, jit: 0 }); k.box(1.3, 2.74, -Dp / 2 + .4, .03, .22, .02, PAL.dark); k.box(1.36, 2.74, -Dp / 2 + .4, .16, .03, .02, PAL.dark);
    k.box(2.7, 1.9, -Dp / 2 + .32, 1.3, 1.6, .05, PAL.cream, { jit: 0 }); k.box(2.7, 3.2, -Dp / 2 + .34, 1.3, .3, .05, PAL.trim, { jit: 0 }); for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) k.box(2.25 + c * .3, 2.05 + r * .27, -Dp / 2 + .36, .22, .16, .02, pick(['#bfe3d5', '#f2d48a', '#e6b9b0', '#cfe1c5']), { jit: 0 });
    k.box(-5.9, 2.7, -Dp / 2 + .5, 1.6, .06, .36, PAL.wood); pottedPlant(k, -6.3, 2.76, -Dp / 2 + .5, .55); pottedPlant(k, -5.6, 2.76, -Dp / 2 + .5, .45);
    k.box(-2.6, 3.66, -Dp / 2 + .34, .9, .26, .08, PAL.dark); L.box(-2.6, 3.7, -Dp / 2 + .39, .78, .18, .02, '#ff5a3c');
    for (const [x, y, z, ry] of [[3.6, .28, 3.0, .1], [4.3, .28, 3.1, -.2], [3.9, .74, 3.05, .3], [5.1, .28, 2.9, .5], [2.9, .28, 3.5, 1.2]]) carton(k, x, y, z, ry);
    for (let i = 0; i < 3; i++) L.box(-3.5 + i * 3.5, f1 + .18, .4, 1.6, .06, .22, '#fff9e2');
  });
  const sign = signMesh(texStudioSign(), 9.1, 2.0); sign.position.set(S.x, .28 + f1 + f2 + .75 + 1.15, S.z + Dp / 2 + .12); scene.add(sign);
  const wb = signMesh(texWhiteboard(), 4.4, 2.3); wb.position.set(S.x - 2.6, 2.3, S.z - Dp / 2 + .38); scene.add(wb);

  const walls = [PAL.plasterG, PAL.plasterO, PAL.plasterS, PAL.plaster, '#c5d99f', '#a9d2c0', '#e5c49a', '#93bcae', '#ead79c', '#d9b9a0'];
  for (const [x, z, w, fl] of [[-21, -15.5, 10, 2], [-37, -16, 12, 3], [-55, -15.5, 10, 2], [-73, -16, 12, 2], [-92, -15.5, 11, 3], [-110, -16, 11, 2], [21, -15.5, 10, 2], [37, -16, 11, 3], [54, -16, 9, 1]]) townBlock(k, G, x, z, 0, w, 9, fl, pick(walls));
  for (const [x, z, w, fl] of [[-104, 22, 11, 2], [-88, 23, 10, 3], [-72, 22, 12, 2], [-54, 22, 10, 3], [-38, 23, 11, 2]]) townBlock(k, G, x, z, Math.PI, w, 9, fl, pick(walls));
  for (let x = -112; x < 66; x += R(12, 17)) townBlock(k, G, x, -35 + R(-2, 2), 0, R(9, 12), 9, pick([1, 2, 2, 3, 3, 4]), pick(walls));
  for (let x = -110; x < 30; x += R(13, 18)) townBlock(k, G, x, -54 + R(-2, 2), 0, R(9, 12), 9, pick([2, 3, 4]), pick(walls));
  for (let x = -112; x < -30; x += R(13, 17)) townBlock(k, G, x, 41 + R(-2, 2), Math.PI, R(9, 12), 9, pick([1, 2, 3]), pick(walls));
  // power poles and wires along the street; the last tower before the river
  let prev = null;
  for (let x = -112; x <= 140; x += 21) {
    if (x > -30 && x < 44) { prev = null; continue; }
    const u = roadUAtX(x), p = roadCurve.getPointAt(u), z = p.z - 4.6;
    k.cyl(x, 0, z, .09, .13, 6.6, PAL.concreteD, { seg: 6 }); k.box(x, 6.1, z, .1, .1, 1.7, PAL.wood); k.cyl(x, 6.2, z - .7, .05, .05, .16, PAL.white, { seg: 5 }); k.cyl(x, 6.2, z + .7, .05, .05, .16, PAL.white, { seg: 5 });
    if (x > -100 && x < 70 && (Math.round(x) % 2)) { k.box(x, 5.0, z + .8, .06, .06, 1.6, PAL.iron); L.box(x, 4.86, z + 1.5, .34, .1, .5, '#fff3c4'); }
    if (prev) for (const s of [-.7, .7]) { const L2 = Math.hypot(x - prev.x, z - prev.z); k.box((x + prev.x) / 2, 6.26, (z + prev.z) / 2 + s, L2, .02, .02, PAL.dark, { ry: -Math.atan2(z - prev.z, x - prev.x), jit: 0 }); }
    prev = { x, z };
  }
  const tx = 86, tz = -30; occ(tx, tz, 3);
  for (let i = 0; i < 4; i++) { const a = i * Math.PI / 2 + Math.PI / 4; k.cyl(tx + Math.cos(a) * 1.3, 0, tz + Math.sin(a) * 1.3, .05, .07, 19.2, PAL.concreteD, { seg: 4, rz: Math.cos(a) * .062, rx: -Math.sin(a) * .062 }); }
  for (let y = 2; y < 19; y += 2.4) { const w = 2.5 * (1 - y / 21); k.box(tx, y, tz, w, .06, w, PAL.concreteD); }
  k.cyl(tx, 18.5, tz, .06, .06, 2.4, PAL.red, { seg: 4 }); for (const a of [0, 2.1, 4.2]) k.box(tx + Math.cos(a) * .35, 17.3, tz + Math.sin(a) * .35, .16, 1.3, .3, PAL.white, { ry: -a });
  SPOT.tower = new THREE.Vector3(tx, 19.6, tz);
  // street life: a rickshaw, a fruit cart, benches
  k.at(-34, 0, 10.2, 0, () => {
    k.box(0, .35, 0, 2.3, .9, 1.25, PAL.teal); k.taper(-.15, 1.25, 0, 1.9, .75, 1.2, PAL.cream, { k: .86 }); k.box(1.0, .35, 0, .5, .7, .9, PAL.teal); k.box(.75, 1.25, 0, .05, .6, 1.0, PAL.glass);
    for (const [x, z] of [[1.15, 0], [-.75, -.62], [-.75, .62]]) k.cyl(x, .3, z - .09, .3, .3, .18, PAL.dark, { seg: 10, rx: Math.PI / 2 });
  });
  k.at(31, 0, -9.2, .1, () => {
    k.box(0, .7, 0, 2.0, .12, 1.1, PAL.wood); for (const [x, z] of [[-.8, -.5], [.8, -.5], [-.8, .5], [.8, .5]]) { k.cyl(x, .34, z - .04, .34, .34, .08, PAL.woodD, { seg: 10, rx: Math.PI / 2 }); }
    for (const [x, z] of [[-.95, -.5], [.95, -.5], [-.95, .5], [.95, .5]]) k.box(x, .82, z, .05, 1.3, .05, PAL.wood);
    k.box(0, 2.1, 0, 2.3, .06, 1.4, PAL.cream, { rz: .04 }); k.box(0, 2.14, 0, .5, .05, 1.42, PAL.trim, { rz: .04 });
    for (let i = 0; i < 26; i++) k.ico(R(-.8, .8), .9 + R(.12), R(-.4, .4), .1, .12, .1, pick(['#e2b84a', '#cfd46a', '#e9a23f']));
  });
  // zebra crossing and the far pavement
  for (let i = 0; i < 7; i++) k.box(-3.4, .085, 3.6 + i * .82, 3.2, .012, .46, PAL.line, { jit: 0 });
  for (const [x, z] of [[-6, 12.2], [22, 12.4], [33, 12.8]]) { k.box(x, 0, z, 2.2, .5, .9, PAL.concrete); k.ico(x - .5, .78, z, .6, .42, .42, PAL.leafC, { c2: '#86c98c', fjit: .1 }); k.ico(x + .45, .72, z, .55, .36, .4, PAL.leafA, { fjit: .1 }); for (let j = 0; j < 4; j++) k.ico(x + R(-.8, .8), .98 + R(.1), z + R(-.2, .2), .07, .07, .07, pick(['#f7f5ea', '#f3d56a', PAL.rose])); }
  for (const x of [-9, -34]) { k.cyl(x, 0, 11.4, .07, .1, 4.4, PAL.trimD, { seg: 6 }); k.box(x, 4.3, 10.9, .08, .08, 1.1, PAL.trimD); L.cyl(x, 4.02, 10.5, .12, .2, .26, '#fff0bd', { seg: 6 }); }
  k.at(-15, 0, 13.4, .3, () => { for (const x of [-.55, .55]) k.cyl(x, .3, -.04, .3, .3, .08, PAL.dark, { seg: 10, rx: Math.PI / 2 }); k.box(0, .42, 0, .9, .2, .16, PAL.red); k.box(.1, .62, 0, .5, .1, .22, PAL.dark); k.box(.46, .52, 0, .06, .5, .06, PAL.iron, { rz: -.3 }); k.box(.56, .96, 0, .05, .05, .5, PAL.iron); });
  for (const x of [-10.5, 11]) { k.box(x, .4, -7.2, 1.7, .08, .5, PAL.wood); k.box(x - .7, 0, -7.2, .08, .4, .45, PAL.iron); k.box(x + .7, 0, -7.2, .08, .4, .45, PAL.iron); k.box(x, .48, -7.42, 1.7, .5, .06, PAL.wood); }
  for (const [x, z] of [[-13, -7.4], [-29, -8.6], [13, -7.6], [46, -8.8], [-46, -8.6], [-64, -8.6], [-82, -8.6], [-20, 15], [-62, 15]]) { plant('neem', x, z, R(.8, 1.0)); k.cyl(x, 0, z, 1.0, 1.0, .22, PAL.concrete, { seg: 8 }); }
}

/* ---------- the Chenab bridge ---------- */
function buildBridge(k, L) {
  const z = -16, xa = 147, xb = 215, len = xb - xa, mid = (xa + xb) / 2;
  k.box(mid, -.66, z, len, .62, 8.4, PAL.concrete, { jit: 0 });
  for (let x = xa + 5; x < xb - 2; x += 9.6) { k.box(x, -4.6, z, 1.6, 4.0, 6.6, PAL.concreteD); k.box(x, -1.05, z, 2.4, .4, 7.6, PAL.concrete); }
  for (const s of [-1, 1]) {
    k.box(mid, -.04, z + s * 3.95, len, .3, .5, PAL.concrete, { jit: 0 });
    for (let x = xa + .6; x < xb; x += 2.35) k.box(x, .26, z + s * 3.95, .24, .82, .24, PAL.white);
    k.box(mid, 1.02, z + s * 3.95, len, .16, .3, PAL.white, { jit: 0 }); k.box(mid, .6, z + s * 3.95, len, .08, .12, PAL.white, { jit: 0 });
  }
  for (let x = xa + 6; x < xb; x += 14) { k.cyl(x, 1.1, z - 3.95, .06, .08, 3.6, PAL.iron, { seg: 5 }); k.box(x, 4.6, z - 3.3, .07, .07, 1.4, PAL.iron); L.box(x, 4.48, z - 2.7, .3, .1, .4, '#fff3c4'); }
  // two wooden boats
  for (const [x, zz, ry] of [[170, 26, .5], [192, -58, -.9]]) k.at(x, -1.02, zz, ry, () => {
    k.taper(0, 0, 0, 3.6, .55, 1.25, PAL.wood, { k: 1.18 }); k.cone(2.2, .02, 0, .66, 1.0, PAL.wood, { seg: 4, rz: -Math.PI / 2, sz: .62 }); k.cone(-2.2, .02, 0, .66, 1.0, PAL.wood, { seg: 4, rz: Math.PI / 2, sz: .62 });
    k.box(0, .4, 0, .3, .06, 1.2, PAL.woodD); k.box(.9, .4, 0, .3, .06, 1.1, PAL.woodD); k.box(-.4, .55, .9, 2.6, .05, .08, PAL.woodD, { ry: .3 });
  });
}

/* ---------- first village: the mobile shop ---------- */
function buildVillage1(scene, k, G, L) {
  const S = SPOT.shop;
  for (const [x, z, ry, w, d, h, o] of [[276, -19, .08, 8, 6, 3.2, { ladder: true }], [290, -23, -.05, 7.5, 6.5, 3.3, { room: true }], [307, -21, .06, 9, 6, 3.1, { cot: true }], [320, -8, -.5, 7, 6, 3.3, {}], [269, -37, .15, 8, 6, 3.1, {}], [285, -41, -.1, 8.5, 6, 3.4, { room: true }], [302, -39, .05, 8, 6, 3.2, {}], [318, -42, -.2, 9, 6.5, 3.2, { ladder: true }], [258, -22, .4, 7, 5.5, 3.0, {}], [334, -44, -.3, 7, 6, 3.1, {}], [338, 50, 3.3, 8, 6, 3.2, {}], [352, 54, 3.0, 7, 6, 3.0, { room: true }]]) mudHouse(k, G, x, z, ry, w, d, h, o);
  mudWall(k, 271.5, -14.5, 284, -13.5); mudWall(k, 271.5, -14.5, 271.2, -22); mudWall(k, 294.5, -16.5, 311, -15.8); mudWall(k, 302, -31.5, 314, -32.5); mudWall(k, 263, -31.5, 277, -30.6);
  // mosque with a green dome
  occ(333, -23, 6.5);
  atAll([k, G], 333, 0, -23, -.25, () => {
    k.box(0, 0, 0, 8.6, .4, 7.4, PAL.concrete); k.box(0, .4, 0, 7.4, 4.0, 6.2, PAL.white, { c2: PAL.plaster });
    for (let i = 0; i < 9; i++) k.box(-3.3 + i * .82, 4.4, 3.0, .5, .42, .2, PAL.white);
    k.dome(0, 4.4, 0, 2.25, 2.3, PAL.trim, { c2: '#46a074', seg: 10 }); k.cyl(0, 4.4, 0, 2.4, 2.4, .3, PAL.white, { seg: 10 }); k.cyl(0, 6.6, 0, .04, .05, .9, PAL.amber, { seg: 4 }); k.ico(0, 7.5, 0, .14, .14, .14, PAL.amber);
    k.box(0, .4, 3.12, 1.5, 2.3, .1, PAL.trimD); k.dome(0, 2.7, 3.12, .75, .7, PAL.trimD, { sz: .08, seg: 8 }); for (const x of [-2.4, 2.4]) { k.box(x, 1.5, 3.12, .9, 1.4, .08, PAL.trimD); G.box(x, 1.6, 3.16, .7, 1.2, .05, PAL.amber); k.dome(x, 2.9, 3.12, .45, .42, PAL.trimD, { sz: .08, seg: 8 }); }
    k.cyl(4.6, 0, 2.6, .5, .62, 8.4, PAL.white, { seg: 8 }); k.cyl(4.6, 6.3, 2.6, .86, .86, .22, PAL.white, { seg: 8 }); k.cyl(4.6, 8.4, 2.6, .4, .4, 1.1, PAL.white, { seg: 8 }); k.dome(4.6, 9.5, 2.6, .52, .7, PAL.trim, { seg: 8 }); k.cyl(4.6, 10.15, 2.6, .025, .03, .6, PAL.amber, { seg: 4 });
  });
  // mobile shop
  occ(S.x, S.z, 4.5);
  atAll([k, G, L], S.x, 0, S.z, 0, () => {
    k.box(0, 0, 0, 5.2, .22, 4.0, PAL.concrete); k.box(0, .22, -1.35, 4.6, 2.9, .25, PAL.plasterG, { c2: PAL.white }); k.box(-2.2, .22, 0, .25, 2.9, 3.0, PAL.plasterG); k.box(2.2, .22, 0, .25, 2.9, 3.0, PAL.plasterG);
    k.box(0, 3.12, .1, 5.0, .2, 3.6, PAL.concrete);
    k.box(0, .22, 1.3, 4.1, .95, .5, PAL.wood, { c2: PAL.barkL }); k.box(0, 1.17, 1.3, 4.2, .06, .6, PAL.cream, { jit: 0 }); k.box(-1.1, 1.23, 1.3, 1.5, .22, .44, '#bfe3d5', { jit: 0 });
    for (let s = 0; s < 3; s++) { k.box(0, 1.2 + s * .55, -1.15, 4.0, .05, .32, PAL.wood); for (let i = 0; i < 12; i++) k.box(-1.85 + i * .33, 1.25 + s * .55, -1.15, .24, R(.2, .36), .16, pick(CLOTH), { jit: .05 }); }
    for (let i = 0; i < 8; i++) k.box(-2.3 + i * .66, 3.0, 2.25, .62, .06, 1.5, i % 2 ? PAL.trim : PAL.cream, { rx: .42, jit: 0 });
    k.box(-2.3, .22, 2.9, .08, 2.25, .08, PAL.iron); k.box(2.3, .22, 2.9, .08, 2.25, .08, PAL.iron);
    k.box(0, 3.32, 1.6, 4.9, 1.2, .12, PAL.trimD, { jit: 0 });
    L.cyl(.6, 2.56, .6, .09, .13, .2, '#fff0bd', { seg: 6 }); k.box(.6, 2.76, .6, .02, .36, .02, PAL.dark);
    k.box(3.6, .42, 1.0, 1.6, .08, .45, PAL.wood); k.box(3.0, 0, 1.0, .08, .42, .4, PAL.woodD); k.box(4.2, 0, 1.0, .08, .42, .4, PAL.woodD);
    k.box(-3.3, 0, 1.2, .08, 2.9, .08, PAL.wood); k.box(-3.3, 0, 1.2, .5, .08, .5, PAL.concreteD);
    matka(k, 3.2, .0, -.6, 1.2); matka(k, 3.9, 0, -.9, 1.0);
  });
  const sg = signMesh(texShopSign(), 4.7, 1.08); sg.position.set(S.x, 3.92, S.z + 1.67); scene.add(sg);
  const bn = signMesh(texBanner(), 1.05, 1.84); bn.position.set(S.x - 3.3, 1.95, S.z + 1.26); scene.add(bn);
  // village green: the old tree with its platform, pump, cots
  bigTree(k, 281, -3, 1.05); k.cyl(281, 0, -3, 3.3, 3.5, .5, PAL.concrete, { seg: 12 }); k.cyl(281, .5, -3, 3.0, 3.0, .06, PAL.mudL, { seg: 12, jit: 0 });
  charpai(k, 286.2, -1.2, .5); handPump(k, 311, 2.4, -.6); occ(311, 2.4, 2);
  matka(k, 312.4, 0, 3.3); matka(k, 312.9, 0, 2.5, .8);
  haystack(k, 262, -11, 2.2); haystack(k, 327, -52, 2.5); haystack(k, 346, 46, 2.0);
  clothesline(k, 294.2, -28, 301.6, -29.4);
  for (const [x, z] of [[272, -17], [279, -16.2], [296, -19], [309, -17.6]]) matka(k, x, 0, z, R(.8, 1.1));
  for (const [x, z, s] of [[268, -5, 1], [297, -12, .9], [315, -30, 1.1], [342, -18, 1], [262, -44, 1.1], [328, 16, .9]]) plant('neem', x, z, s);
  for (const [x, z] of [[254, -34], [346, -30], [300, -52], [282, -52]]) plant('kikar', x, z, 1.1);
}

/* ---------- second village: the courtyard and the lanes ---------- */
function buildVillage2(scene, k, G, L) {
  const C = SPOT.court;
  mudHouse(k, G, 556.5, -53, 0, 11, 6, 3.3, { door: -.4, win: 3.2, doorC: PAL.teal, ladder: false, side: false });
  for (const [x, z, ry, w, d, h, o] of [[574, -56, .05, 8, 6, 3.2, { room: true }], [590, -57, -.06, 9, 6.5, 3.3, { ladder: true, door: 0 }], [606, -52, -.35, 8, 6, 3.1, {}], [539, -50, .25, 7.5, 6, 3.2, { cot: true }], [584, -70, .1, 8, 6, 3.2, {}], [567, -70, -.1, 8, 6, 3.3, { room: true }], [602, -68, -.2, 8.5, 6, 3.1, {}], [548, -68, .15, 8, 6, 3.0, {}], [622, -42, -.9, 7, 6, 3.1, {}], [528, -40, .7, 7, 5.5, 3.0, {}]]) mudHouse(k, G, x, z, ry, w, d, h, o);
  // courtyard walls (kept low so the camera can look in)
  mudWall(k, 548.6, -49.6, 548.6, -35.4, 1.1); mudWall(k, 565.6, -49.6, 565.6, -35.4, 1.1); mudWall(k, 548.6, -35.4, 553.4, -35.4, 1.1); mudWall(k, 560.6, -35.4, 565.6, -35.4, 1.1);
  occ(557, -42.5, 9.5);
  k.box(557.3, .0, -43.5, 3.6, .05, 3.2, '#3f8f6a', { jit: 0 }); for (let i = 0; i < 7; i++) k.box(555.75 + i * .52, .055, -43.5, .2, .012, 3.0, i % 2 ? PAL.cream : PAL.mustard, { jit: 0 });
  k.box(555.55, 0, -43.5, .42, .3, .42, PAL.wood); k.box(555.55, .3, -43.5, .5, .05, .5, PAL.woodD);
  k.cyl(555.0, 0, -45.6, .06, .07, 1.9, PAL.wood, { seg: 5 }); k.box(555.25, 1.82, -45.6, .55, .05, .05, PAL.wood);
  charpai(k, 552.0, -47.2, .25); matka(k, 563.8, 0, -47.9, 1.2); matka(k, 564.4, 0, -47.0, 1.0); matka(k, 563.5, 0, -46.9, .8);
  k.box(550.3, 0, -44.6, .9, .34, .7, PAL.mudD); k.box(550.3, .34, -44.6, .5, .1, .4, PAL.dark); L.box(550.3, .36, -44.6, .36, .05, .26, '#ff8a3c');
  k.cyl(550.3, .44, -44.6, .26, .2, .2, PAL.iron, { seg: 8 });
  bigTree(k, 563.4, -47.6, .72);
  clothesline(k, 549.3, -48.6, 549.3, -41.6);
  pottedPlant(k, 553.2, 0, -49.0, 1); pottedPlant(k, 560.6, 0, -49.1, .9);
  // the lane to the east: saplings, hand pump, swept yard, goat pen
  for (let i = 0; i < 4; i++) { const x = 570.6 + i * 2.1; k.cyl(x, 0, -36, .5, .5, .16, PAL.mudD, { seg: 8 }); k.cyl(x, 0, -36, .035, .05, 1.1, PAL.barkL, { seg: 4 }); k.ico(x, 1.25, -36, .42, .5, .42, PAL.leafC, { c2: '#8fd195', fjit: .1 }); k.ico(x + .2, 1.0, -36.1, .26, .3, .26, PAL.leafA, { fjit: .1 }); }
  occ(574, -36, 5);
  handPump(k, 583, -40, 0, false); occ(583, -40, 3.5); matka(k, 584.4, 0, -40.9, 1.0);
  mudWall(k, 596.8, -44.5, 607.5, -41.6, .85, .3); mudWall(k, 607.5, -41.6, 606.6, -35.6, .85, .3); mudWall(k, 596.8, -44.5, 596.3, -40.6, .85, .3); occ(602, -40, 7);
  k.box(604.5, 0, -42.3, 1.6, .3, .5, PAL.wood); k.box(604.5, .3, -42.3, 1.4, .08, .36, PAL.straw);
  haystack(k, 616, -36, 2.3); haystack(k, 533, -60, 2.2); haystack(k, 610, -60, 1.8);
  clothesline(k, 578.2, -51.4, 585.6, -52.2);
  for (const [x, z] of [[571, -51.6], [594.6, -52.6], [586.2, -52.8], [600, -49]]) matka(k, x, 0, z, R(.8, 1.1));
  charpai(k, 579.5, -49.8, -.1); charpai(k, 597.2, -51.6, .3);
  for (const [x, z, s] of [[569, -61, 1.1], [596, -63, 1], [542, -60, 1.1], [620, -54, 1], [612, -22, .95]]) plant('neem', x, z, s);
  for (const [x, z] of [[626, -30], [520, -52], [578, -78]]) plant('kikar', x, z, 1.15);
  occ(547, -28.5, 5);
  for (let x = 562; x < 606; x += 3) occ(x, -28, 3.2);      // keep the morning camera's lane clear
}
/* ---------- people: small soft figures in shalwar kameez ---------- */
const PG = {
  torso: new THREE.CylinderGeometry(.15, .26, .74, 9).translate(0, .15, 0),
  head: new THREE.IcosahedronGeometry(.2, 2),
  hair: new THREE.SphereGeometry(.213, 12, 7, 0, TAU, 0, Math.PI * .5),
  veil: new THREE.SphereGeometry(.238, 12, 7, 0, TAU, 0, Math.PI * .52),
  drape: new THREE.CylinderGeometry(.15, .25, .62, 7, 1, true, Math.PI * .5, Math.PI).translate(0, .2, 0),
  arm: new THREE.CylinderGeometry(.052, .043, .4, 6).translate(0, -.2, 0),
  hand: new THREE.IcosahedronGeometry(.054, 1).translate(0, -.43, 0),
  leg: new THREE.CylinderGeometry(.088, .062, .56, 6).translate(0, -.28, 0),
  foot: new THREE.BoxGeometry(.1, .06, .2).translate(0, -.59, .04),
  eye: new THREE.SphereGeometry(.023, 6, 4),
  cap: new THREE.CylinderGeometry(.16, .185, .11, 10).translate(0, .19, 0),
  turban: new THREE.SphereGeometry(.24, 10, 6).scale(1, .62, 1).translate(0, .16, 0),
  beard: new THREE.ConeGeometry(.12, .22, 7).rotateX(Math.PI).translate(0, -.2, .1),
  braid: new THREE.CylinderGeometry(.04, .025, .4, 5).translate(0, -.2, 0)
};
const SKIN = ['#c9925f', '#b97f52', '#d6a577', '#ad7449'];
function mk(g, m, parent, x = 0, y = 0, z = 0) { const o = new THREE.Mesh(g, m); o.position.set(x, y, z); o.castShadow = true; parent.add(o); return o; }
function person(o = {}) {
  const g = new THREE.Group(), kam = mat(o.kameez || '#4f8f6a'), sal = mat(o.shalwar || '#ece7d2'), skin = mat(o.skin || pick(SKIN)), hair = mat(o.hairC || '#2b221d');
  const hips = new THREE.Group(); hips.position.y = .6; g.add(hips);
  mk(PG.torso, kam, hips);
  const head = new THREE.Group(); head.position.y = .69; hips.add(head);
  mk(PG.head, skin, head);
  const dark = mat('#1d1a18'); mk(PG.eye, dark, head, .075, .02, .182).castShadow = false; mk(PG.eye, dark, head, -.075, .02, .182).castShadow = false;
  if (o.girl) { const v = mk(PG.veil, mat(o.dupatta || PAL.cream), head); v.rotation.x = -.72; const d = mk(PG.drape, mat(o.dupatta || PAL.cream), hips, 0, 0, -.02); d.rotation.y = Math.PI; const fr = mk(PG.hair, hair, head); fr.rotation.x = -.56; }
  else { const h = mk(PG.hair, hair, head); h.rotation.x = -.5; }
  if (o.braid) { const b = mk(PG.braid, hair, head, 0, -.05, -.2); b.rotation.x = .25; }
  if (o.cap) mk(PG.cap, mat(o.capC || PAL.white), head);
  if (o.turban) mk(PG.turban, mat(o.turbanC || PAL.white), head);
  if (o.beard) mk(PG.beard, mat(o.beardC || '#e9e6da'), head);
  const limb = (geo2, m, x, y, extra, em) => { const p = new THREE.Group(); p.position.set(x, y, 0); hips.add(p); mk(geo2, m, p); mk(extra, em, p); return p; };
  const armL = limb(PG.arm, kam, .2, .44, PG.hand, skin), armR = limb(PG.arm, kam, -.2, .44, PG.hand, skin);
  const legL = limb(PG.leg, sal, .09, 0, PG.foot, mat('#3a2e26')), legR = limb(PG.leg, sal, -.09, 0, PG.foot, mat('#3a2e26'));
  armL.rotation.z = .12; armR.rotation.z = -.12;
  const s = o.scale ?? 1; g.scale.setScalar(s); if (s < .95) head.scale.setScalar(1.16);
  g.userData = { hips, head, armL, armR, legL, legR, hipY: .6 };
  if (o.at) g.position.set(o.at[0], o.at[1], o.at[2]); if (o.ry !== undefined) g.rotation.y = o.ry;
  return g;
}
function sitDown(p, y = .1, cross = true) {
  const u = p.userData; u.hips.position.y = u.hipY = y;
  if (cross) { u.legL.rotation.set(-1.5, .75, 0, 'YXZ'); u.legR.rotation.set(-1.5, -.75, 0, 'YXZ'); }
  else { u.legL.rotation.set(-.9, 0, 0); u.legR.rotation.set(-.9, 0, 0); }
}
function stand(p) { const u = p.userData; u.hips.position.y = u.hipY = .6; u.legL.rotation.set(0, 0, 0); u.legR.rotation.set(0, 0, 0); }
function walkCycle(u, ph, amp = .55) { const s = Math.sin(ph); u.legL.rotation.x = s * amp; u.legR.rotation.x = -s * amp; u.armL.rotation.x = -s * amp * .7; u.armR.rotation.x = s * amp * .7; u.hips.position.y = u.hipY + Math.abs(Math.cos(ph)) * .03; }
function face(g, x, z) { g.rotation.y = Math.atan2(x - g.position.x, z - g.position.z); }
const KID = { boyA: { scale: .78, kameez: '#5d9bb0', shalwar: '#ece7d2' }, boyB: { scale: .74, kameez: '#d9b24a', shalwar: '#ece7d2', cap: true }, girlA: { scale: .76, kameez: '#d98c8c', shalwar: '#f3ecd2', girl: true, dupatta: '#f7f5ea' }, girlB: { scale: .72, kameez: '#8c5f86', shalwar: '#e9dfc0', girl: true, dupatta: '#f2c66f' }, boyC: { scale: .8, kameez: '#3f8f6a', shalwar: '#ece7d2' }, girlC: { scale: .7, kameez: '#3c8f86', shalwar: '#f3ecd2', girl: true, dupatta: '#f7d9c9' } };

/* ---------- animation registry: each entry only runs while the journey is near it ---------- */
const ANIMS = [];
function anim(a, b, fn, objs) { ANIMS.push({ a, b, fn, objs }); }
const TAGS = [];
function tag(a, b, x, y, z, text) { TAGS.push({ a, b, pos: new THREE.Vector3(x, y, z), text }); }

/* ---------- animals ---------- */
function goat(c1, c2, s = 1) {
  const g = new THREE.Group(), k = new Kit();
  k.ico(0, .56, 0, .42, .27, .24, c1, { d: 1 }); k.ico(-.18, .6, 0, .25, .2, .2, c2, { d: 1 });
  for (const [x, z] of [[.26, .12], [.26, -.12], [-.28, .12], [-.28, -.12]]) k.cyl(x, 0, z, .04, .032, .42, c1, { seg: 5 });
  k.cyl(-.42, .62, 0, .03, .02, .14, c1, { seg: 4, rz: .9 });
  const body = k.mesh(M.world); body.matrixAutoUpdate = true; g.add(body);
  const hk = new Kit(); hk.cyl(0, 0, 0, .09, .11, .26, c1, { seg: 6, rz: -.7 }); hk.ico(.26, .26, 0, .15, .11, .1, c1, { d: 1, rz: -.3 }); hk.ico(.2, .3, .1, .04, .09, .03, c2, { rz: -.9 }); hk.ico(.2, .3, -.1, .04, .09, .03, c2, { rz: -.9 });
  hk.cone(.2, .34, .05, .022, .16, PAL.barkL, { seg: 4, rz: .5 }); hk.cone(.2, .34, -.05, .022, .16, PAL.barkL, { seg: 4, rz: .5 });
  const head = hk.mesh(M.world); head.matrixAutoUpdate = true; head.position.set(.34, .6, 0); g.add(head);
  g.scale.setScalar(s); g.userData.head = head; return g;
}
function chicken(c) { const k = new Kit(); k.ico(0, .17, 0, .13, .11, .1, c, { d: 1 }); k.ico(.12, .27, 0, .06, .065, .055, c); k.cone(.18, .26, 0, .02, .06, PAL.amber, { seg: 4, rz: -Math.PI / 2 }); k.box(.12, .32, 0, .05, .04, .015, PAL.red); k.cone(-.13, .18, 0, .06, .12, c, { seg: 4, rz: .9 }); k.cyl(.02, 0, .03, .008, .008, .1, PAL.amber, { seg: 3 }); k.cyl(.02, 0, -.03, .008, .008, .1, PAL.amber, { seg: 3 }); const m = k.mesh(M.world); m.matrixAutoUpdate = true; return m; }
function bird(c) {
  const g = new THREE.Group(), tri = (sx) => { const ge = new THREE.BufferGeometry(); ge.setAttribute('position', new THREE.Float32BufferAttribute([0, 0, -.16, 0, 0, .2, sx * .62, 0, .08], 3)); ge.computeVertexNormals(); return new THREE.Mesh(ge, new THREE.MeshBasicMaterial({ color: col(c), side: THREE.DoubleSide })); };
  const l = tri(1), r = tri(-1); g.add(l, r); g.userData = { l, r }; return g;
}
function addFlock(scene, cx, cy, cz, n, rad, a, b, c = '#f7f5ea') {
  const birds = [];
  for (let i = 0; i < n; i++) { const bd = bird(c); bd.userData.o = R(TAU); bd.userData.rad = rad * R(.7, 1.3); bd.userData.h = R(-2, 2); bd.userData.s = R(.8, 1.2); scene.add(bd); birds.push(bd); }
  anim(a, b, t => { for (const bd of birds) { const u = bd.userData, an = t * .22 * u.s + u.o; bd.position.set(cx + Math.cos(an) * u.rad, cy + u.h + Math.sin(t + u.o) * .6, cz + Math.sin(an) * u.rad * .6); bd.rotation.y = -an; const f = Math.sin(t * 7 * u.s + u.o) * .7; u.l.rotation.z = f; u.r.rotation.z = -f; } });
}

/* ---------- the van ---------- */
const gVanTop = () => geo('vantop', () => { const g = new THREE.BoxGeometry(1, 1, 1).translate(0, .5, 0); const p = g.attributes.position; for (let i = 0; i < p.count; i++) if (p.getY(i) > .5 && p.getX(i) > 0) p.setX(i, p.getX(i) - .22); return g; });
function buildVan(scene) {
  const g = new THREE.Group(), k = new Kit(), L = new Kit();
  k.box(0, .3, 0, 3.5, .74, 1.5, PAL.cream, { jit: 0 }); k.add(gVanTop(), { x: -.05, y: 1.04, z: 0, sx: 3.4, sy: .78, sz: 1.44, c: PAL.cream, jit: 0 });
  k.box(-.25, 1.82, 0, 2.9, .05, 1.38, PAL.white, { jit: 0 }); k.box(0, .88, 0, 3.53, .13, 1.53, PAL.trim, { jit: 0 });
  for (const s of [-1, 1]) { k.box(.92, 1.2, s * .722, .62, .46, .03, PAL.glass, { jit: 0 }); k.box(.2, 1.2, s * .722, .62, .46, .03, PAL.glass, { jit: 0 }); k.box(1.25, 1.42, s * .82, .06, .14, .16, PAL.iron); k.box(.55, .5, s * .755, .03, 1.2, .01, PAL.concreteD, { jit: 0 }); }
  k.box(1.645, 1.1, 0, .04, .9, 1.2, PAL.glass, { rz: .766, jit: 0 }); k.box(-1.66, 1.2, 0, .03, .46, 1.0, PAL.glass, { jit: 0 });
  k.box(1.78, .28, 0, .1, .2, 1.52, PAL.iron); k.box(-1.78, .28, 0, .1, .2, 1.52, PAL.iron); k.box(1.76, .56, 0, .03, .22, .7, PAL.iron);
  for (const s of [-1, 1]) { L.box(1.762, .7, s * .52, .04, .17, .26, '#fff3c4'); L.box(-1.762, .72, s * .58, .04, .16, .14, '#ff6a4a'); }
  for (const s of [-1, 1]) k.box(-.25, 1.87, s * .6, 2.5, .05, .05, PAL.iron); for (const x of [-1.4, -.25, .9]) k.box(x, 1.87, 0, .05, .05, 1.2, PAL.iron);
  carton(k, -.9, 1.92, .12, .1, .95); carton(k, -.2, 1.92, -.15, -.2, .95); carton(k, -.55, 2.36, 0, .3, .9);
  const body = k.mesh(M.world); g.add(body); const lit = L.mesh(M.lit, false, false); g.add(lit);
  const tex = texVan();
  for (const s of [-1, 1]) { const p = signMesh(tex, 1.42, .44); p.position.set(-.86, 1.2, s * .738); if (s < 0) p.rotation.y = Math.PI; g.add(p); }
  const wg = new THREE.CylinderGeometry(.31, .31, .2, 12).rotateX(Math.PI / 2), hg = new THREE.CylinderGeometry(.15, .15, .22, 8).rotateX(Math.PI / 2), wheels = [];
  for (const [x, z] of [[1.08, .68], [1.08, -.68], [-1.05, .68], [-1.05, -.68]]) { const w = new THREE.Group(); w.position.set(x, .31, z); const t = new THREE.Mesh(wg, mat('#26302c')); t.castShadow = true; w.add(t); w.add(new THREE.Mesh(hg, mat(PAL.cream))); const sp = new THREE.Mesh(new THREE.BoxGeometry(.5, .05, .23), mat(PAL.concreteD)); w.add(sp); g.add(w); wheels.push(w); }
  const beams = [glowSprite('#ffe9b0', 1.15, 0), glowSprite('#ffe9b0', 1.15, 0)]; beams[0].position.set(1.9, .72, .52); beams[1].position.set(1.9, .72, -.52); g.add(beams[0], beams[1]);
  const dust = []; for (let i = 0; i < 14; i++) { const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: glowTex, color: col('#e9dfbb'), transparent: true, opacity: 0, depthWrite: false })); s.userData.life = 1; scene.add(s); dust.push(s); }
  scene.add(g);
  return { g, wheels, beams, dust, u: 0, speed: 0, pos: new THREE.Vector3(), tan: new THREE.Vector3(1, 0, 0), di: 0, dAcc: 0 };
}

/* ---------- cast and scenes ---------- */
function buildActors(scene, van) {
  const add = p => { scene.add(p); return p; };
  const S = SPOT.studio;
  /* studio: a teacher at the board, someone at the duplicator, cartons going out to the van */
  const teacher = add(person({ kameez: '#8c5f86', shalwar: '#efe6cf', girl: true, dupatta: '#f3ecd2', scale: 1.1, at: [S.x - .2, .28, S.z - 3.2], ry: .35 }));
  const op = add(person({ kameez: '#5d9bb0', scale: 1.12, at: [S.x + 4.3, .28, S.z - 1.75], ry: Math.PI }));
  op.userData.armL.rotation.x = op.userData.armR.rotation.x = -1.1;
  const loader = add(person({ kameez: '#3f8f6a', scale: 1.12, cap: true, capC: '#f3ecd2' }));
  const lk = new Kit(); carton(lk, 0, 0, 0, 0, .9); const lbox = lk.mesh(M.world); lbox.matrixAutoUpdate = true; lbox.position.set(0, .22, .32); loader.userData.hips.add(lbox);
  const walkers = [add(person({ kameez: '#d9b24a', scale: 1.1 })), add(person({ kameez: '#d98c8c', girl: true, dupatta: '#f7f5ea', scale: 1.05 })), add(person(Object.assign({}, KID.boyA)))];
  anim(0, .27, t => {
    const tu = teacher.userData; tu.armR.rotation.z = -1.9 + Math.sin(t * 1.3) * .22; tu.armR.rotation.x = -.5 + Math.sin(t * .9) * .15; tu.armL.rotation.x = -.5 + Math.sin(t * 1.7) * .2; tu.head.rotation.y = Math.sin(t * .5) * .5 - .1; teacher.rotation.y = .35 + Math.sin(t * .25) * .18;
    op.userData.armL.rotation.x = -1.1 + Math.sin(t * 6) * .08; op.userData.armR.rotation.x = -1.1 + Math.cos(t * 5) * .08; op.userData.head.rotation.x = .2;
    const cyc = (t * .1) % 1, out = cyc < .5, k = out ? cyc * 2 : 2 - cyc * 2, a = new THREE.Vector3(S.x + 4.6, .14, S.z + 5.6), b = new THREE.Vector3(van.pos.x - 2.6, .05, van.pos.z - 1.2);
    const kk = ease(clamp(k * 1.25 - .125)); loader.position.lerpVectors(a, b, kk); loader.rotation.y = Math.atan2(b.x - a.x, b.z - a.z) + (out ? 0 : Math.PI);
    const lu = loader.userData; walkCycle(lu, t * 7, .5); lbox.visible = out; if (out) { lu.armL.rotation.x = lu.armR.rotation.x = -1.15; }
    walkers.forEach((w, i) => { const span = 44, ph = ((t * (.9 + i * .12) + i * 17) % (span * 2)); const x = ph < span ? -60 + ph : -60 + span * 2 - ph; w.position.set(x + i * 3, .16, -9.4 - (i % 2) * .7); w.rotation.y = ph < span ? Math.PI / 2 : -Math.PI / 2; walkCycle(w.userData, t * (6 + i) + i, .5); });
  }, [teacher, op, loader, ...walkers]);
  tag(.152, .198, S.x - 2.6, 3.9, S.z - 4, 'A whole term of lectures'); tag(.152, .198, S.x + 5.2, 2.5, S.z - 2.6, 'Copied onto cards');

  /* the road: a farmer, river birds */
  const farmer = add(person({ kameez: '#e9dfc0', shalwar: '#e9dfc0', turban: true, turbanC: '#d9b24a', scale: 1.1, at: [118, H(118, 14), 14], ry: 2.2 }));
  anim(.2, .42, t => { const u = farmer.userData; u.armL.rotation.x = u.armR.rotation.x = -1 + Math.sin(t * 2.2) * .45; u.hips.rotation.x = .25 + Math.sin(t * 2.2) * .1; });
  const fisher = add(person({ kameez: '#5d9bb0', scale: 1.05, cap: true, at: [170.2, -.8, 26.2], ry: 1.2 })); sitDown(fisher, .12, false); fisher.userData.armL.rotation.x = fisher.userData.armR.rotation.x = -1.2;
  addFlock(scene, 182, 13, -10, 9, 22, .2, .44);

  /* first village */
  const P1 = SPOT.shop;
  const keeper = add(person({ kameez: '#e9dfc0', scale: 1.12, cap: true, at: [P1.x - .2, .22, P1.z + .45], ry: .15 }));
  const father = add(person({ kameez: '#7fa3b0', scale: 1.14, at: [P1.x + 1.75, .05, P1.z + 2.45], ry: Math.PI - .25 }));
  const girl = add(person(Object.assign({}, KID.girlA, { at: [P1.x + .55, .05, P1.z + 3.0], ry: -.32 })));
  const cardG = new THREE.Mesh(new THREE.BoxGeometry(.13, .17, .015), mat('#f7f4e6')); cardG.position.set(0, -.5, .03); girl.userData.armL.add(cardG);
  const boyPeek = add(person(Object.assign({}, KID.boyB, { at: [P1.x - .75, .05, P1.z + 2.7], ry: 1.35 })));
  const elders = [add(person({ kameez: '#f3ecd2', turban: true, beard: true, scale: 1.1, at: [285.7, 0, -.9], ry: .5 + Math.PI / 2 + .3 })), add(person({ kameez: '#cfe1c5', cap: true, beard: true, beardC: '#cfcabb', scale: 1.08, at: [286.8, 0, -1.6], ry: -.9 }))];
  elders.forEach(e => { sitDown(e, .56, false); });
  const tyreBoy = add(person(Object.assign({}, KID.boyC))); const tyre = new THREE.Mesh(new THREE.TorusGeometry(.3, .07, 6, 14), mat('#26302c')); tyre.castShadow = true; scene.add(tyre);
  const carrier = add(person({ kameez: '#3c8f86', girl: true, dupatta: '#f2c66f', scale: 1.08 })); const pk = new Kit(); matka(pk, 0, 0, 0, .8); const pot = pk.mesh(M.world); pot.matrixAutoUpdate = true; pot.position.set(0, .2, 0); carrier.userData.head.add(pot);
  const roofKids = [add(person(Object.assign({}, KID.boyA, { at: [305.4, 3.72, -20.6], ry: .6 }))), add(person(Object.assign({}, KID.girlB, { at: [308.4, 3.72, -21.4], ry: -.3 })))];
  const kites = roofKids.map((kd, i) => {
    const kg = new THREE.BufferGeometry(); kg.setAttribute('position', new THREE.Float32BufferAttribute([0, .7, 0, -.5, 0, 0, .5, 0, 0, -.5, 0, 0, 0, -.75, 0, .5, 0, 0], 3)); kg.computeVertexNormals();
    const km = new THREE.Mesh(kg, new THREE.MeshBasicMaterial({ color: col(i ? PAL.amber : PAL.rose), side: THREE.DoubleSide })); scene.add(km);
    const lg = new THREE.BufferGeometry(); lg.setAttribute('position', new THREE.Float32BufferAttribute(new Float32Array(9), 3)); const line = new THREE.Line(lg, new THREE.LineBasicMaterial({ color: col('#f7f5ea'), transparent: true, opacity: .7 })); line.frustumCulled = false; scene.add(line);
    kd.userData.armL.rotation.x = -2.3; kd.userData.armR.rotation.x = -2.0; return { km, line, kd, o: i * 2.1 };
  });
  const goats1 = [[264, -14, .4, '#f1ead6', '#8a6a4b'], [266.4, -15.6, 2.1, '#8a6a4b', '#f1ead6'], [263, -17, 3.6, '#3a332d', '#f1ead6']].map(([x, z, ry, a, b]) => { const g = goat(a, b, R(.9, 1.1)); g.position.set(x, 0, z); g.rotation.y = ry; scene.add(g); return g; });
  const hens1 = [[293, -12.4], [294.2, -11.6], [292.4, -11], [313.5, 4.6]].map(([x, z], i) => { const c = chicken(i % 2 ? '#f1ead6' : '#b9743f'); c.position.set(x, 0, z); c.rotation.y = R(TAU); scene.add(c); return c; });
  anim(.36, .58, t => {
    const gu = girl.userData; gu.armL.rotation.x = -2.5 + Math.sin(t * 5) * .15; gu.armL.rotation.z = .25; gu.hips.position.y = gu.hipY + Math.abs(Math.sin(t * 5)) * .09; gu.head.rotation.x = -.25;
    father.userData.head.rotation.y = -.9 + Math.sin(t * .8) * .12; father.userData.head.rotation.x = .15; father.userData.armL.rotation.x = -1.0 + Math.sin(t * 1.4) * .08;
    keeper.userData.armL.rotation.x = -1.0 + Math.sin(t * 1.1) * .2; keeper.userData.head.rotation.y = Math.sin(t * .6) * .3;
    boyPeek.userData.hips.position.y = boyPeek.userData.hipY + Math.abs(Math.sin(t * 3 + 1)) * .05;
    elders[0].userData.armL.rotation.x = -.7 + Math.sin(t * 1.5) * .35; elders[0].userData.head.rotation.y = Math.sin(t * .7) * .25; elders[1].userData.head.rotation.x = Math.sin(t * 1.9) * .12;
    const a = -t * .55, r = 7.2; tyreBoy.position.set(281 + Math.cos(a) * r, .03, -3 + Math.sin(a) * r); tyreBoy.rotation.y = Math.atan2(Math.sin(a), -Math.cos(a)); walkCycle(tyreBoy.userData, t * 11, .8); tyreBoy.userData.armL.rotation.x = -1.1;
    const a2 = a - .16; tyre.position.set(281 + Math.cos(a2) * r, .38, -3 + Math.sin(a2) * r); tyre.rotation.set(0, Math.atan2(Math.sin(a2), -Math.cos(a2)) + Math.PI / 2, 0); tyre.rotateZ(-t * 9);
    const cyc = (t * .045) % 1, k = cyc < .5 ? cyc * 2 : 2 - cyc * 2; carrier.position.set(lerp(312.6, 314.5, k), .02, lerp(.6, -13, k)); carrier.rotation.y = cyc < .5 ? Math.PI - .12 : -.12; walkCycle(carrier.userData, t * 5.5, .4); carrier.userData.armL.rotation.set(-2.9, 0, .25);
    kites.forEach((kt, i) => { const u = t * .5 + kt.o, x = 306 + i * 9 + Math.sin(u) * 3, y = 15 + i * 2.5 + Math.sin(u * 1.7) * 1.2, z = -30 - i * 4 + Math.cos(u * .8) * 2.5; kt.km.position.set(x, y, z); kt.km.rotation.set(-.5, .4, Math.sin(u * 2.3) * .3); const p = kt.line.geometry.attributes.position, h = kt.kd.position; p.setXYZ(0, h.x, h.y + 1.2, h.z + .2); p.setXYZ(1, lerp(h.x, x, .55), lerp(h.y + 1.2, y, .42), lerp(h.z, z, .55)); p.setXYZ(2, x, y - .7, z); p.needsUpdate = true; });
    goats1.forEach((g, i) => { g.userData.head.rotation.z = -.9 + Math.sin(t * 2.4 + i * 2) * .18; });
    hens1.forEach((c, i) => { c.rotation.z = -Math.max(0, Math.sin(t * 4 + i * 1.7)) * .55; });
  }, [keeper, father, girl, boyPeek, ...elders, tyreBoy, tyre, carrier, ...roofKids, ...goats1, ...hens1, ...kites.map(k => k.km), ...kites.map(k => k.line)]);
  tag(.49, .528, P1.x + .55, 2.0, P1.z + 3.0, 'One card, one term'); tag(.49, .528, P1.x - 1.1, 1.62, P1.z + 1.3, 'Scratch voucher, one SMS');

  /* second village: buffalo in the pond */
  const bk = new Kit();
  for (const [x, z, ry] of [[POND.x - 3, POND.z + 1, .4], [POND.x + 2.5, POND.z - 2.5, 2.6], [POND.x + 1, POND.z + 4, 4.4]]) bk.at(x, -.86, z, ry, () => { bk.ico(0, .25, 0, 1.25, .58, .68, '#33403b', { d: 1 }); bk.ico(1.2, .5, 0, .46, .36, .34, '#2b3632', { d: 1 }); bk.cyl(1.2, .74, .18, .04, .07, .62, '#c9cdbd', { seg: 5, rx: 1.0, rz: .5 }); bk.cyl(1.2, .74, -.18, .04, .07, .62, '#c9cdbd', { seg: 5, rx: -1.0, rz: .5 }); bk.ico(1.6, .46, 0, .2, .17, .2, '#1f2926'); });
  for (const [x, z] of [[POND.x - 9, POND.z + 8], [POND.x + 10, POND.z + 6], [POND.x - 3.4, POND.z + .8], [158, 12], [205, -40], [207, 6]]) { const y = Math.max(H(x, z), x === POND.x - 3.4 ? -.4 : -1.05); bk.at(x, y, z, R(TAU), () => { bk.cyl(0, 0, .04, .012, .012, .5, PAL.dark, { seg: 3 }); bk.cyl(0, 0, -.04, .012, .012, .5, PAL.dark, { seg: 3 }); bk.ico(0, .62, 0, .22, .14, .12, PAL.white, { d: 1 }); bk.cyl(.16, .66, 0, .025, .035, .34, PAL.white, { seg: 4, rz: -.35 }); bk.ico(.3, 1.0, 0, .07, .05, .05, PAL.white); bk.cone(.36, 1.0, 0, .018, .16, PAL.amber, { seg: 3, rz: -Math.PI / 2 }); }); }
  scene.add(bk.mesh(M.world));

  /* the four children who meet the van, then sit down to study */
  const C = SPOT.court, Ph = SPOT.phone;
  const kids = [KID.girlA, KID.boyA, KID.girlB, KID.boyB].map((def, i) => {
    const kd = add(person(Object.assign({}, def)));
    const ang = (-46 + i * 30) * Math.PI / 180, r = 1.75 + (i % 2) * .3;
    kd.userData.mat = new THREE.Vector3(Ph.x + Math.cos(ang) * r, .06, Ph.z + Math.sin(ang) * r);
    kd.userData.greet = new THREE.Vector3([549.6, 551.2, 548.2, 552.4][i], .03, [-31.6, -30.8, -33.0, -33.4][i]);
    kd.userData.home = new THREE.Vector3([556.5, 555, 557.6, 554][i], .03, [-38.5, -37.6, -37.2, -39][i]);
    const nb = new THREE.Mesh(new THREE.BoxGeometry(.24, .02, .3), mat('#fbfaf2')); nb.position.set(0, -.52, .5); nb.visible = false; kd.userData.hips.add(nb); kd.userData.nb = nb;
    return kd;
  });
  const mother = add(person({ kameez: '#3c8f86', shalwar: '#e9dfc0', girl: true, dupatta: '#f2c66f', scale: 1.1, at: [552.6, 0, -46.6], ry: 1.25 })); sitDown(mother, .56, false); mother.userData.armL.rotation.x = mother.userData.armR.rotation.x = -.8;
  const tmpV = new THREE.Vector3();
  anim(.5, .86, (t, dt, p) => {
    const arrive = sstep(.635, .668, p), goIn = sstep(.686, .712, p);
    kids.forEach((kd, i) => {
      const u = kd.userData;
      if (goIn >= 1) {
        kd.position.copy(u.mat); face(kd, Ph.x, Ph.z); if (u.hipY !== .1) sitDown(kd, .1, true); u.nb.visible = true;
        u.head.rotation.x = .18 + Math.sin(t * .8 + i) * .05; u.head.rotation.y = Math.sin(t * .4 + i * 2) * .12; u.hips.rotation.x = .12;
        u.armL.rotation.set(-.75, 0, .2); u.armR.rotation.set(i === 1 ? -2.7 + Math.sin(t * 2) * .15 * (Math.sin(t * .35) > .2 ? 1 : 0) : -.8 + Math.sin(t * 9 + i) * .06 * (i === 2 ? 1 : 0), 0, -.2);
        if (i === 1 && Math.sin(t * .35) <= .2) u.armR.rotation.x = -.8;
      } else {
        if (u.hipY !== .6) stand(kd); u.nb.visible = false; u.hips.rotation.x = 0; u.head.rotation.set(0, 0, 0);
        if (goIn > 0) { tmpV.copy(u.greet).lerp(u.mat, goIn); kd.position.copy(tmpV); face(kd, u.mat.x, u.mat.z); walkCycle(u, t * 9 + i, .6); }
        else { tmpV.copy(u.home).lerp(u.greet, arrive); kd.position.copy(tmpV); if (arrive > 0 && arrive < 1) { face(kd, u.greet.x, u.greet.z); walkCycle(u, t * 12 + i, .8); } else { face(kd, van.pos.x, van.pos.z); u.legL.rotation.x = u.legR.rotation.x = 0; u.armR.rotation.x = 0; u.armL.rotation.set(arrive ? -2.7 : 0, 0, arrive ? .5 + Math.sin(t * 7 + i) * .4 : .12); u.hips.position.y = u.hipY + (arrive ? Math.abs(Math.sin(t * 5 + i * 1.3)) * .1 : 0); } }
      }
    });
    mother.userData.head.rotation.y = -.2 + Math.sin(t * .5) * .2; mother.userData.armL.rotation.x = -.8 + Math.sin(t * 2.6) * .12;
    const vis = p < .838; kids.forEach(kd => kd.visible = vis); mother.visible = vis;
  });
  tag(.652, .684, 546.4, 2.9, -28.6, 'Homework goes back with the van');
  tag(.797, .824, Ph.x, 1.3, Ph.z, 'The lecture plays with no internet');

  /* phone, lantern, fire */
  const phone = new THREE.Group(); phone.position.copy(Ph).setY(.46); phone.rotation.set(0, Math.PI / 2, 0); phone.rotateX(-.22);
  const pb = new THREE.Mesh(new THREE.BoxGeometry(.5, .3, .022), mat('#1d2a25')); pb.position.y = .15; phone.add(pb);
  const screen = new THREE.Mesh(new THREE.PlaneGeometry(.46, .26), new THREE.MeshBasicMaterial({ map: texPhone() })); screen.position.set(0, .15, .013); phone.add(screen); scene.add(phone);
  const phoneGlow = glowSprite('#d9ffe9', 1.5, 0); phoneGlow.position.copy(Ph).setY(.4); phoneGlow.position.x -= .25; scene.add(phoneGlow);
  const lk2 = new Kit(), ll = new Kit(), LP = new THREE.Vector3(555.48, 1.32, -45.6);
  lk2.cyl(LP.x, LP.y - .2, LP.z, .09, .1, .05, PAL.iron, { seg: 8 }); lk2.cyl(LP.x, LP.y + .06, LP.z, .05, .09, .07, PAL.iron, { seg: 8 }); lk2.box(LP.x, LP.y + .13, LP.z, .015, .36, .015, PAL.iron);
  ll.cyl(LP.x, LP.y - .15, LP.z, .07, .085, .21, '#ffc978', { seg: 8 }); scene.add(lk2.mesh(M.world)); scene.add(ll.mesh(M.lit, false, false));
  const lampGlow = glowSprite('#ffb85e', 3.2, 0); lampGlow.position.copy(LP); scene.add(lampGlow);
  const fireGlow = glowSprite('#ff8a3c', 1.6, 0); fireGlow.position.set(550.3, .5, -44.6); scene.add(fireGlow);
  const doorGlow = glowSprite('#ffc978', 4.5, 0); doorGlow.position.set(559.7, 1.8, -49.7); scene.add(doorGlow);
  const smoke = []; for (let i = 0; i < 9; i++) { const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: glowTex, color: col('#cfe3d6'), transparent: true, opacity: 0, depthWrite: false })); s.userData.o = i / 9; scene.add(s); smoke.push(s); }
  const ffN = 46, ffP = new Float32Array(ffN * 3), ffS = []; for (let i = 0; i < ffN; i++) ffS.push([R(546, 568), R(.5, 4.5), R(-52, -34), R(TAU), R(.4, 1)]);
  const ffG = new THREE.BufferGeometry(); ffG.setAttribute('position', new THREE.BufferAttribute(ffP, 3));
  const ff = new THREE.Points(ffG, new THREE.PointsMaterial({ map: glowTex, color: col('#e8ff9a'), size: .34, transparent: true, opacity: 0, depthWrite: false, blending: THREE.AdditiveBlending, fog: false })); ff.frustumCulled = false; scene.add(ff);
  const goatN = goat('#f1ead6', '#8a6a4b', .95); goatN.position.set(551.2, 0, -38.2); goatN.rotation.y = .6; scene.add(goatN);
  SPOT.lamp = LP;
  anim(.6, .9, (t, dt, p, env) => {
    const n = env.night; phoneGlow.material.opacity = n * (.3 + Math.sin(t * 3.1) * .04); lampGlow.material.opacity = n * (.75 + Math.sin(t * 9) * .05 + Math.sin(t * 23) * .03); fireGlow.material.opacity = (.3 + n * .5) * (.8 + Math.sin(t * 12) * .2); doorGlow.material.opacity = n * .35;
    smoke.forEach(s => { const k = (t * .12 + s.userData.o) % 1; s.position.set(550.3 + Math.sin(k * 5 + s.userData.o * 9) * .3 + k * .8, .7 + k * 4.2, -44.6 + k * .5); s.scale.setScalar(.5 + k * 2.2); s.material.opacity = Math.sin(k * Math.PI) * .22; });
    for (let i = 0; i < ffN; i++) { const s = ffS[i]; ffP[i * 3] = s[0] + Math.sin(t * .4 * s[4] + s[3]) * 1.6; ffP[i * 3 + 1] = s[1] + Math.sin(t * .7 * s[4] + s[3] * 2) * .7; ffP[i * 3 + 2] = s[2] + Math.cos(t * .33 * s[4] + s[3]) * 1.6; }
    ffG.attributes.position.needsUpdate = true; ff.material.opacity = n * (.75 + Math.sin(t * 2) * .2);
    goatN.userData.head.rotation.z = -.2 + Math.sin(t * .8) * .1;
  });

  /* the next morning: good deeds in the lane */
  const mornA = [];
  const water = add(person(Object.assign({}, KID.girlA, { at: [573.55, .03, -35.0], ry: 0 }))); face(water, 572.7, -36); mornA.push(water);
  const wk = new Kit(); wk.cyl(0, 0, 0, .1, .12, .22, PAL.teal, { seg: 7 }); wk.cyl(.1, .1, 0, .02, .03, .26, PAL.teal, { seg: 4, rz: -1.0 }); wk.ico(.33, .25, 0, .045, .02, .045, PAL.teal); const can = wk.mesh(M.world); can.matrixAutoUpdate = true; can.position.set(0, -.56, .0); can.rotation.y = -Math.PI / 2; water.userData.armR.add(can);
  const drops = []; for (let i = 0; i < 6; i++) { const d = new THREE.Mesh(new THREE.SphereGeometry(.022, 5, 4), new THREE.MeshBasicMaterial({ color: col('#dff6ff') })); scene.add(d); drops.push(d); }
  const pumpBoy = add(person(Object.assign({}, KID.boyA, { at: [582.05, .12, -40], ry: Math.PI / 2 }))); mornA.push(pumpBoy);
  const dadi = add(person({ kameez: '#e9dfc0', shalwar: '#e9dfc0', girl: true, dupatta: '#f7f5ea', hairC: '#d9d6cc', scale: 1.02, at: [584.25, .03, -39.75], ry: -Math.PI / 2 })); mornA.push(dadi); dadi.userData.hips.rotation.x = .2; dadi.userData.armL.rotation.x = dadi.userData.armR.rotation.x = -.9;
  const hk = new Kit(); hk.box(-.5, 0, 0, 1.0, .06, .06, PAL.iron); const handle = hk.mesh(M.world); handle.matrixAutoUpdate = true; handle.position.set(583, 1.3, -40); scene.add(handle);
  const stream = new THREE.Mesh(new THREE.CylinderGeometry(.025, .035, .62, 5), new THREE.MeshBasicMaterial({ color: col('#dff6ff'), transparent: true, opacity: .85 })); stream.position.set(583.55, .5, -40); scene.add(stream);
  const sweep = add(person(Object.assign({}, KID.girlB, { at: [592.2, .03, -41.4], ry: .5 }))); mornA.push(sweep);
  const brk = new Kit(); brk.cyl(0, 0, 0, .018, .018, 1.0, PAL.barkL, { seg: 4 }); brk.cone(0, -.34, 0, .16, .38, PAL.straw, { seg: 6 }); const broom = brk.mesh(M.world); broom.matrixAutoUpdate = true; broom.position.set(0, -.42, 0); broom.rotation.x = Math.PI - .5; sweep.userData.armR.add(broom);
  const feeder = add(person(Object.assign({}, KID.boyB, { at: [601.25, .03, -39.2], ry: Math.PI / 2 }))); mornA.push(feeder);
  const fk = new Kit(); fk.ico(0, 0, 0, .09, .05, .07, '#7cc083'); const leaves = fk.mesh(M.world); leaves.matrixAutoUpdate = true; leaves.position.set(0, -.47, .03); feeder.userData.armL.add(leaves);
  const goats2 = [[602.55, -39.2, Math.PI, '#f1ead6', '#8a6a4b', 1], [603.6, -40.3, 2.5, '#8a6a4b', '#f1ead6', .62], [602.2, -41.0, 3.6, '#f1ead6', '#3a332d', .58]].map(([x, z, ry, a, b, s]) => { const g = goat(a, b, s); g.position.set(x, 0, z); g.rotation.y = ry; scene.add(g); mornA.push(g); return g; });
  const hens2 = [[599.2, -37.3], [598.4, -38.2], [600, -36.6], [598.9, -36.2], [597.6, -37]].map(([x, z], i) => { const c = chicken(i % 2 ? '#f1ead6' : '#b9743f'); c.position.set(x, 0, z); c.rotation.y = R(TAU); scene.add(c); mornA.push(c); return c; });
  const baba = add(person({ kameez: '#f3ecd2', shalwar: '#f3ecd2', turban: true, turbanC: '#cfe1c5', beard: true, scale: 1.08 })); mornA.push(baba);
  const stick = new THREE.Mesh(new THREE.CylinderGeometry(.015, .018, 1.0, 5), mat(PAL.wood)); stick.position.set(0, -.42, .12); stick.rotation.x = .25; baba.userData.armR.add(stick);
  const helper = add(person(Object.assign({}, KID.boyC))); mornA.push(helper);
  const runners = [add(person(Object.assign({}, KID.girlC))), add(person(Object.assign({}, KID.boyA, { kameez: '#d9b24a' })))]; runners.forEach(r => mornA.push(r));
  anim(.82, 1.01, (t, dt, p) => {
    const vis = p > .838; for (const o of mornA) o.visible = vis; handle.visible = true; stream.visible = vis; drops.forEach(d => d.visible = vis); if (!vis) return;
    const tilt = Math.max(0, Math.sin(t * .9)); water.userData.armR.rotation.set(-1.0 - tilt * .3, 0, -.1); can.rotation.z = -tilt * .7; water.userData.head.rotation.x = .3;
    can.updateWorldMatrix(true, false); tmpV.set(.33, .25, 0).applyMatrix4(can.matrixWorld);
    drops.forEach((d, i) => { const k = (t * 1.6 + i / 6) % 1; d.position.set(tmpV.x + (572.75 - tmpV.x) * k * .7, tmpV.y - k * k * tmpV.y, tmpV.z + (-36 - tmpV.z) * k * .7); d.visible = tilt > .25; });
    const ph = Math.sin(t * 3.2); handle.rotation.z = -.05 + ph * .38; const hy = 1.3 + Math.sin(handle.rotation.z) * -.95;
    const pu = pumpBoy.userData, reach = clamp((hy - .9) / .7); pu.armL.rotation.x = pu.armR.rotation.x = -1.25 - reach * 1.2; pu.hips.rotation.x = .28 - reach * .22; pu.hips.position.y = pu.hipY - (1 - reach) * .05;
    stream.material.opacity = ph < 0 ? .85 : .15; stream.scale.y = ph < 0 ? 1 : .5; dadi.userData.head.rotation.x = .25 + Math.sin(t * .6) * .05;
    const sw = Math.sin(t * 3.6); sweep.rotation.y = .5 + sw * .35; sweep.userData.armR.rotation.set(-.9, 0, -.2 + sw * .3); sweep.userData.armL.rotation.set(-1.0, 0, -.5); sweep.userData.hips.rotation.x = .3; sweep.position.x = 592.2 + Math.sin(t * .3) * .8;
    feeder.userData.armL.rotation.x = -1.35 + Math.sin(t * 1.4) * .12; feeder.userData.head.rotation.x = .2; goats2[0].userData.head.rotation.z = .1 + Math.sin(t * 5) * .1; goats2[1].position.y = Math.abs(Math.sin(t * 3)) * .12; goats2[2].userData.head.rotation.z = -.8 + Math.sin(t * 2) * .2;
    hens2.forEach((c, i) => { c.rotation.z = -Math.max(0, Math.sin(t * 4 + i * 1.7)) * .55; });
    const span = 13, cyc = (t * .55) % (span * 2), fwd = cyc < span, x = 574.5 + (fwd ? cyc : span * 2 - cyc);
    baba.position.set(x, .03, -44.8); baba.rotation.y = fwd ? Math.PI / 2 : -Math.PI / 2; walkCycle(baba.userData, t * 3.4, .28); baba.userData.hips.rotation.x = .16; baba.userData.armR.rotation.x = -.5 + Math.sin(t * 3.4) * .2;
    helper.position.set(x, .03, -44.8 + (fwd ? .52 : -.52)); helper.rotation.y = baba.rotation.y; walkCycle(helper.userData, t * 5.2, .36); helper.userData.armR.rotation.set(0, 0, 0); helper.userData.armL.rotation.set(0, 0, 0); (fwd ? helper.userData.armR : helper.userData.armL).rotation.set(-.5, 0, fwd ? -.9 : .9);
    runners.forEach((r, i) => { const a = t * .9 + i * .9, rr = 5.2; r.position.set(588 + Math.cos(a) * rr, .03, -36.4 + Math.sin(a) * rr * .3); r.rotation.y = Math.atan2(-Math.sin(a), Math.cos(a) * .3); walkCycle(r.userData, t * 12 + i, .85); });
  });
  tag(.858, .884, 573.3, 1.75, -35.2, 'Watering the new trees'); tag(.872, .905, 583.2, 2.0, -40, 'Water for dadi'); tag(.9, .93, 592.2, 1.7, -41.4, 'Sweeping the yard'); tag(.924, .945, 601.8, 1.6, -39.4, 'Feeding the goats'); tag(.884, .92, 581, 2.1, -44.8, 'Walking with baba');
  addFlock(scene, 560, 30, -30, 14, 34, .9, 1.01);
}
/* ---------- sky, light and the day that passes during the journey ---------- */
const ENV_KEYS = [
  // p, sky top, horizon, fog, sun colour, sun strength, hemi sky, hemi ground, hemi strength, sun direction, night, fog near/far
  { p: 0.00, top: '#5fb39a', mid: '#d6eecb', fog: '#c4e3c6', sun: '#fff0cf', si: 1.22, hs: '#cfeedd', hg: '#4f8560', hi: 0.37, dir: [-.62, .50, .60], night: 0, fn: 120, ff: 640 },
  { p: 0.20, top: '#56ad94', mid: '#d2ecce', fog: '#bfe0c8', sun: '#fff6dc', si: 1.26, hs: '#cceedd', hg: '#4f8560', hi: 0.38, dir: [-.42, .78, .46], night: 0, fn: 120, ff: 640 },
  { p: 0.36, top: '#4fa78e', mid: '#cfebcf', fog: '#bcdfc7', sun: '#fffbe8', si: 1.31, hs: '#c9ecdc', hg: '#4f8560', hi: 0.40, dir: [-.1, .92, .38], night: 0, fn: 130, ff: 660 },
  { p: 0.50, top: '#4f9f84', mid: '#e6ecb8', fog: '#cbdcb0', sun: '#fff0c0', si: 1.29, hs: '#cfe8cc', hg: '#58875a', hi: 0.38, dir: [.42, .62, .42], night: 0, fn: 110, ff: 600 },
  { p: 0.60, top: '#43856f', mid: '#f1dc96', fog: '#bcc78e', sun: '#ffd28a', si: 1.26, hs: '#c4d8ac', hg: '#627f50', hi: 0.37, dir: [.74, .30, .36], night: .05, fn: 80, ff: 520 },
  { p: 0.672, top: '#28574b', mid: '#dcb16a', fog: '#7d9a73', sun: '#ffac62', si: 1.04, hs: '#93b697', hg: '#46654d', hi: 0.37, dir: [.84, .12, .30], night: .35, fn: 60, ff: 440 },
  { p: 0.712, top: '#06201b', mid: '#15433a', fog: '#0f2e27', sun: '#a6e0cd', si: .36, hs: '#2f6e60', hg: '#0d231d', hi: .52, dir: [-.36, .62, .44], night: 1, fn: 34, ff: 320 },
  { p: 0.828, top: '#06201b', mid: '#17483d', fog: '#10312a', sun: '#a6e0cd', si: .36, hs: '#2f6e60', hg: '#0d231d', hi: .52, dir: [-.30, .66, .40], night: 1, fn: 34, ff: 320 },
  { p: 0.856, top: '#5fb09a', mid: '#f8e6b4', fog: '#dbe5c0', sun: '#ffdca4', si: 1.24, hs: '#d2e8d0', hg: '#58875a', hi: 0.36, dir: [-.80, .26, .34], night: 0, fn: 80, ff: 520 },
  { p: 0.95, top: '#5fb39a', mid: '#f6ecbd', fog: '#d6eac6', sun: '#ffeabf', si: 1.26, hs: '#cfeedd', hg: '#4f8560', hi: 0.37, dir: [-.74, .36, .40], night: 0, fn: 110, ff: 620 },
  { p: 1.00, top: '#58b39a', mid: '#fbe9b0', fog: '#dcecc6', sun: '#ffe0a8', si: 1.29, hs: '#cfeedd', hg: '#4f8560', hi: 0.38, dir: [-.9, .14, .2], night: 0, fn: 140, ff: 900 }
];
ENV_KEYS.forEach(k => { for (const n of ['top', 'mid', 'fog', 'sun', 'hs', 'hg']) k['_' + n] = new THREE.Color(k[n]).convertSRGBToLinear(); k._dir = new THREE.Vector3(...k.dir).normalize(); k._srgbFog = new THREE.Color(k.fog); });
function buildSky(scene, LOW) {
  const env = { top: new THREE.Color(), mid: new THREE.Color(), fog: new THREE.Color(), sun: new THREE.Color(), hs: new THREE.Color(), hg: new THREE.Color(), dir: new THREE.Vector3(), si: 1, hi: 1, night: 0, fn: 70, ff: 500, fogS: new THREE.Color() };
  const skyMat = new THREE.ShaderMaterial({
    side: THREE.BackSide, depthWrite: false, fog: false,
    uniforms: { top: { value: env.top }, mid: { value: env.mid }, sunDir: { value: new THREE.Vector3(0, 1, 0) }, sunCol: { value: env.sun }, sunAmt: { value: 1 }, moonDir: { value: new THREE.Vector3(-.5, .55, -.67).normalize() }, night: { value: 0 } },
    vertexShader: 'varying vec3 vP;void main(){vP=position;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.);}',
    fragmentShader: `uniform vec3 top,mid,sunDir,sunCol,moonDir;uniform float sunAmt,night;varying vec3 vP;
      void main(){vec3 d=normalize(vP);float h=d.y;vec3 c=mix(mid,top,pow(clamp(h*1.15+.02,0.,1.),.6));
      float s=max(dot(d,normalize(sunDir)),0.);c+=sunCol*(pow(s,3.)*.2+pow(s,12.)*.3+pow(s,64.)*.6+smoothstep(.99925,.9996,s)*2.4)*sunAmt;
      float m=dot(d,moonDir);float disc=smoothstep(.99905,.9992,m);vec3 md2=normalize(moonDir+vec3(.012,.006,.0));float cut=smoothstep(.99895,.9991,dot(d,md2));
      c+=vec3(.95,1.,.9)*(disc*(1.-cut)*1.5+pow(max(m,0.),300.)*.25)*night;
      gl_FragColor=vec4(c,1.);
      #include <tonemapping_fragment>
      #include <encodings_fragment>
      }`
  });
  const sky = new THREE.Mesh(new THREE.SphereGeometry(1100, 24, 14), skyMat); sky.frustumCulled = false; sky.renderOrder = -10; scene.add(sky);
  // stars, in two layers that breathe out of phase
  const stars = [0, 1].map(j => {
    const n = LOW ? 260 : 520, P = new Float32Array(n * 3); for (let i = 0; i < n; i++) { const a = R(TAU), y = R(.06, 1), r = Math.sqrt(1 - y * y); P[i * 3] = Math.cos(a) * r * 1000; P[i * 3 + 1] = y * 1000; P[i * 3 + 2] = Math.sin(a) * r * 1000; }
    const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.BufferAttribute(P, 3));
    const pts = new THREE.Points(g, new THREE.PointsMaterial({ color: col(j ? '#e9fff2' : '#fff6d8'), size: j ? 2.2 : 1.5, sizeAttenuation: false, transparent: true, opacity: 0, depthWrite: false, fog: false })); pts.frustumCulled = false; pts.renderOrder = -9; scene.add(pts); return pts;
  });
  // far ridge to the west: the Sulaiman range that sits on the horizon past Muzaffargarh
  const ridges = [0, 1, 2].map(j => {
    const P = [], x = 860 + j * 70, z0 = -900, z1 = 900, n = 70; let prev = null;
    for (let i = 0; i <= n; i++) { const z = lerp(z0, z1, i / n), hgt = (34 + j * 26) * (.35 + fbm(i * .17 + j * 9, j * 3.1, 3) * 1.25) * (1 - Math.pow(Math.abs(i / n - .5) * 2, 3) * .6); if (prev) P.push(x, -8, prev.z, x, -8, z, x, prev.h, prev.z, x, prev.h, prev.z, x, -8, z, x, hgt, z); prev = { z, h: hgt }; }
    const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(P, 3));
    const m = new THREE.Mesh(g, new THREE.MeshBasicMaterial({ color: 0xffffff, fog: false, side: THREE.DoubleSide })); m.frustumCulled = false; m.renderOrder = -8 + j * -.1; m.material.depthWrite = false; scene.add(m); return m;
  });
  ridges.reverse().forEach((m, i) => m.renderOrder = -8 + i * .1);
  // clouds
  const ck = new Kit(); ck.ico(0, 0, 0, 1.3, .55, 1, '#ffffff', { c2: '#ffffff', d: 1 }); ck.ico(1.1, -.05, .2, .9, .42, .8, '#ffffff', { d: 1 }); ck.ico(-1.1, -.08, -.1, 1, .4, .8, '#ffffff', { d: 1 }); ck.ico(.3, .28, -.3, .8, .42, .7, '#ffffff', { d: 1 });
  const cg = ck.geometry(), cloudMat = new THREE.MeshLambertMaterial({ color: 0xffffff, transparent: true, opacity: .95 });
  const clouds = []; for (let i = 0; i < (LOW ? 12 : 20); i++) { const m = new THREE.Mesh(cg, cloudMat); m.position.set(R(-260, 860), R(118, 176), R(-380, 340)); m.scale.set(R(14, 30), R(9, 15), R(12, 22)); m.rotation.y = R(-.3, .3); m.userData.v = R(.8, 2.2); scene.add(m); clouds.push(m); }
  const hemi = new THREE.HemisphereLight(0xffffff, 0xffffff, 1); scene.add(hemi);
  const sun = new THREE.DirectionalLight(0xffffff, 1); sun.castShadow = true;
  const sm = LOW ? 1024 : 2048; sun.shadow.mapSize.set(sm, sm); const sc = sun.shadow.camera; sc.near = 20; sc.far = 420; sc.left = -62; sc.right = 62; sc.top = 62; sc.bottom = -62; sun.shadow.bias = -.0004; sun.shadow.normalBias = .32;
  scene.add(sun); scene.add(sun.target);
  const lampA = new THREE.PointLight(0xffffff, 0, 16, 1.6), lampB = new THREE.PointLight(0xffffff, 0, 9, 1.6); scene.add(lampA, lampB);
  scene.fog = new THREE.Fog(0xffffff, 70, 500);
  const cT = new THREE.Color();
  function update(p, t, dt, focus, camPos) {
    let i = 0; while (i < ENV_KEYS.length - 2 && p > ENV_KEYS[i + 1].p) i++;
    const a = ENV_KEYS[i], b = ENV_KEYS[i + 1], u = ease(clamp((p - a.p) / (b.p - a.p)));
    for (const n of ['top', 'mid', 'fog', 'sun', 'hs', 'hg']) env[n].copy(a['_' + n]).lerp(b['_' + n], u);
    env.fogS.copy(a._srgbFog).lerp(b._srgbFog, u);
    env.si = lerp(a.si, b.si, u); env.hi = lerp(a.hi, b.hi, u); env.night = lerp(a.night, b.night, u); env.fn = lerp(a.fn, b.fn, u); env.ff = lerp(a.ff, b.ff, u);
    env.dir.copy(a._dir).lerp(b._dir, u).normalize();
    scene.fog.color.copy(env.fog); scene.fog.near = env.fn; scene.fog.far = env.ff;
    hemi.color.copy(env.hs); hemi.groundColor.copy(env.hg); hemi.intensity = env.hi;
    sun.color.copy(env.sun); sun.intensity = env.si;
    const tex = 124 / sm * 2, fx = Math.round(focus.x / tex) * tex, fz = Math.round(focus.z / tex) * tex;
    sun.target.position.set(fx, 0, fz); sun.position.set(fx + env.dir.x * 200, env.dir.y * 200, fz + env.dir.z * 200);
    sky.position.copy(camPos); stars.forEach((s, j) => { s.position.copy(camPos); s.material.opacity = env.night * (.72 + Math.sin(t * (1.3 + j) + j * 2) * .26); s.visible = env.night > .02; });
    skyMat.uniforms.sunDir.value.copy(env.dir); skyMat.uniforms.sunAmt.value = 1 - sstep(.3, .95, env.night); skyMat.uniforms.night.value = sstep(.6, 1, env.night);
    ridges.forEach((m, j) => { m.material.color.copy(env.mid).lerp(env.top, .34 + j * .2).multiplyScalar(1 - env.night * .25); });
    cloudMat.color.copy(cT.setRGB(1, 1, 1).lerp(env.mid, .25)); cloudMat.emissive.copy(env.mid).multiplyScalar(.42 * (1 - env.night * .7)); cloudMat.opacity = .95 - env.night * .5;
    for (const c of clouds) { c.position.x += c.userData.v * dt; if (c.position.x > 900) c.position.x = -280; }
    M.glow.color.copy(cT.copy(col('#1d3f36')).lerp(col('#ffc56e'), sstep(.25, .8, env.night)));
    M.water.color.copy(cT.copy(col(PAL.water)).lerp(env.mid, .28));
    waterTex.offset.y = -t * .012; waterTex.offset.x = Math.sin(t * .1) * .02;
    return env;
  }
  return { env, update, sun, hemi, lampA, lampB, skyMat };
}
/* ---------- the journey: chapters, camera, loop ---------- */
const CH = [
  { a: 0.000, b: 0.085, go: 0 },
  { a: 0.105, b: 0.235 },
  { a: 0.265, b: 0.385 },
  { a: 0.410, b: 0.530 },
  { a: 0.560, b: 0.685 },
  { a: 0.716, b: 0.825 },
  { a: 0.853, b: 0.945 },
  { a: 0.966, b: 1.01, go: 1 }
];
const CAM = [
  { p: 0.000, pos: [-96, 52, 80], look: [40, 4, -14] },
  { p: 0.085, pos: [-40, 24, 58], look: [6, 3, -10] },
  { p: 0.125, pos: [-7, 5.6, 25], look: [1.5, 4.0, -11] },
  { p: 0.175, pos: [2.6, 3.0, -1.2], look: [-1.6, 2.3, -16.5] },
  { p: 0.218, pos: [3.5, 3.4, 18.5], look: [12.2, 1.4, 3.5] },
  { p: 0.270, van: 1, pos: [-13, 6.2, 15.5], look: [3.5, 1.2, 0] },
  { p: 0.320, van: 1, pos: [-6, 22, 36], look: [8, 0, -3] },
  { p: 0.375, van: 1, pos: [-17, 5.4, 13.5], look: [5, 1.4, 0] },
  { p: 0.415, pos: [262, 23, 50], look: [297, 2, -6] },
  { p: 0.465, pos: [287, 6.5, 29], look: [298, 2.3, -1] },
  { p: 0.525, pos: [296.8, 2.2, 11.6], look: [300.4, 1.45, 2.2] },
  { p: 0.575, van: 1, pos: [-14, 6.5, 16], look: [5, 1.2, 0] },
  { p: 0.625, van: 1, pos: [-22, 10, 7], look: [16, 2.5, -3] },
  { p: 0.675, pos: [526, 8.5, -4], look: [551, 1.4, -34] },
  { p: 0.716, pos: [547, 7, -24], look: [556, 1, -43] },
  { p: 0.752, pos: [551.4, 1.75, -41.2], look: [556.8, .75, -43.7] },
  { p: 0.790, pos: [555.4, 2.5, -38.0], look: [556.4, .6, -43.6] },
  { p: 0.825, pos: [561.0, 2.05, -41.0], look: [555.4, .7, -43.7] },
  { p: 0.856, pos: [567, 2.8, -26.5], look: [572.5, 1.1, -37] },
  { p: 0.885, pos: [577.5, 2.6, -28], look: [582.5, 1.1, -40] },
  { p: 0.915, pos: [588, 2.6, -29], look: [592, 1.1, -41] },
  { p: 0.945, pos: [598, 2.8, -28], look: [601.5, 1, -40] },
  { p: 0.972, pos: [616, 30, -2], look: [575, 2, -40] },
  { p: 1.000, pos: [640, 74, 34], look: [300, 36, -22] }
];
const _k = [0, 1, 2, 3].map(() => new THREE.Vector3());
function hermite(out, key, i, p, vanPos) {
  const n = CAM.length, ks = [CAM[Math.max(0, i - 1)], CAM[i], CAM[i + 1], CAM[Math.min(n - 1, i + 2)]];
  ks.forEach((k, j) => { _k[j].fromArray(k[key]); if (k.van) _k[j].add(vanPos); });
  const h = ks[2].p - ks[1].p, u = clamp((p - ks[1].p) / h), u2 = u * u, u3 = u2 * u, T = .9;
  const d1 = (ks[2].p - ks[0].p) || 1, d2 = (ks[3].p - ks[1].p) || 1;
  const h00 = 2 * u3 - 3 * u2 + 1, h10 = u3 - 2 * u2 + u, h01 = -2 * u3 + 3 * u2, h11 = u3 - u2;
  for (const c of ['x', 'y', 'z']) { const m1 = (_k[2][c] - _k[0][c]) / d1 * T, m2 = (_k[3][c] - _k[1][c]) / d2 * T; out[c] = h00 * _k[1][c] + h10 * h * m1 + h01 * _k[2][c] + h11 * h * m2; }
  out.y = clamp(out.y, Math.min(_k[1].y, _k[2].y), Math.max(_k[1].y, _k[2].y));     // no dips or hops between two shots
}

const VAN_X = [14, 304.5, 546];
const VAN_U = VAN_X.map(roadUAtX);
const smoother = t => t * t * t * (t * (t * 6 - 15) + 10);
const vanU = pp => pp < .228 ? VAN_U[0] : pp < .405 ? lerp(VAN_U[0], VAN_U[1], smoother((pp - .228) / .177)) : pp < .535 ? VAN_U[1] : pp < .668 ? lerp(VAN_U[1], VAN_U[2], smoother((pp - .535) / .133)) : VAN_U[2];
// sample the camera's flight so trees are not planted in its way
(function () {
  const vp = new THREE.Vector3(), cp = new THREE.Vector3(), lk = new THREE.Vector3();
  for (let pp = 0; pp <= 1.0001; pp += .0025) {
    roadCurve.getPointAt(vanU(pp), vp); let i = 0; while (i < CAM.length - 2 && pp > CAM[i + 1].p) i++;
    hermite(cp, 'pos', i, pp, vp); hermite(lk, 'look', i, pp, vp); if (cp.y > 28) continue;
    CAMPTS.push({ x: cp.x, y: cp.y, z: cp.z, p: pp });
    for (const f of [.14, .28, .42, .56, .7, .84]) CAMPTS.push({ x: lerp(cp.x, lk.x, f), y: lerp(cp.y, lk.y, f), z: lerp(cp.z, lk.z, f), p: pp, sight: 1 });   // and its line of sight
  }
})();

function start() {
  const stage = document.getElementById('stage'), canvas = document.getElementById('scene');
  const RM = matchMedia('(prefers-reduced-motion: reduce)').matches;
  const TEST = !!window.__ILM_TEST;
  const chapters = [...document.querySelectorAll('.chapter')], stops = [...document.querySelectorAll('.route button')];
  const hint = document.getElementById('hint'), playBtn = document.getElementById('play'), routeFill = document.getElementById('routeFill'), tagBox = document.getElementById('tags');
  let W = 1, Hh = 1, wide = true;
  const track = document.getElementById('top');
  const scrollMax = () => Math.max(1, track.offsetHeight - window.innerHeight);      // the journey ends where the track ends; the facts section follows it
  const scrollP = () => clamp((window.scrollY || document.documentElement.scrollTop || 0) / scrollMax());
  let pT = scrollP(), p = pT, lastTone = '', lastVeil = '', lastActive = -1, frameNo = 0, lastVa = '', lastNear = -1, lastP = '', lastHint = null;

  /* ----- page controls (these work with or without WebGL) ----- */
  function go(i) { const c = CH[i], t = c.go !== undefined ? c.go : c.a + (c.b - c.a) * .42; stopPlay(); window.scrollTo({ top: t * scrollMax(), behavior: RM ? 'auto' : 'smooth' }); }
  stops.forEach((b, i) => b.addEventListener('click', () => go(i)));
  document.querySelectorAll('[data-go]').forEach(el => el.addEventListener('click', e => { e.preventDefault(); go(+el.dataset.go); }));
  document.querySelectorAll('[data-info]').forEach(el => el.addEventListener('click', e => { e.preventDefault(); stopPlay(); window.scrollTo({ top: track.offsetHeight, behavior: RM ? 'auto' : 'smooth' }); }));
  let playing = false, playY = 0;
  function stopPlay() { if (!playing) return; playing = false; playBtn.setAttribute('aria-pressed', 'false'); playBtn.querySelector('span').textContent = 'Play journey'; stage.classList.remove('is-playing'); }
  playBtn.addEventListener('click', () => {
    if (playing) return stopPlay();
    if (scrollP() > .985) window.scrollTo(0, 0);
    playing = true; playY = window.scrollY; playBtn.setAttribute('aria-pressed', 'true'); playBtn.querySelector('span').textContent = 'Pause'; stage.classList.add('is-playing');
  });
  for (const ev of ['wheel', 'touchstart', 'keydown']) window.addEventListener(ev, e => { if (ev === 'keydown' && (e.key === 'Tab' || e.key === 'Shift' || (e.target === playBtn && (e.key === 'Enter' || e.key === ' ')))) return; stopPlay(); }, { passive: true });
  const ptr = { x: 0, y: 0, sx: 0, sy: 0 };
  window.addEventListener('pointermove', e => { if (e.pointerType === 'touch') return; ptr.x = (e.clientX / window.innerWidth) * 2 - 1; ptr.y = (e.clientY / window.innerHeight) * 2 - 1; }, { passive: true });
  // film grain
  try { const c = document.createElement('canvas'); c.width = c.height = 140; const x = c.getContext('2d'), d = x.createImageData(140, 140); for (let i = 0; i < d.data.length; i += 4) { const v = 110 + Math.random() * 145; d.data[i] = d.data[i + 1] = d.data[i + 2] = v; d.data[i + 3] = 255; } x.putImageData(d, 0, 0); document.getElementById('grain').style.backgroundImage = 'url(' + c.toDataURL() + ')'; } catch (e) { }

  const tagEls = [];
  function ui(pp, fogS, dt) {
    let active = -1, maxO = 0;
    chapters.forEach((el, i) => {
      const c = CH[i], f = .016;
      let o = Math.min(i === 0 ? 1 : sstep(c.a, c.a + f, pp), i === CH.length - 1 ? 1 : 1 - sstep(c.b - f, c.b, pp));
      if (o > .5) active = i; maxO = Math.max(maxO, o);
      if (el._o !== o) {
        el._o = o; el.style.opacity = o; el.style.visibility = o > 0.001 ? 'visible' : 'hidden';
        const y = (1 - o) * (pp < (c.a + c.b) / 2 ? 26 : -26);
        el.style.transform = el.classList.contains('chapter--finale') ? `translate3d(-50%, calc(-50% + ${y.toFixed(1)}px), 0)` : `translate3d(0, ${y.toFixed(1)}px, 0)`;
        if (o > .5) el.removeAttribute('inert'); else el.setAttribute('inert', '');
      }
    });
    const va = (.12 + maxO * .88).toFixed(2); if (va !== lastVa) { lastVa = va; stage.style.setProperty('--veil-a', va); }
    if (active !== lastActive) {
      lastActive = active; stops.forEach((b, i) => { b.classList.toggle('is-on', i === active); if (i === active) b.setAttribute('aria-current', 'step'); else b.removeAttribute('aria-current'); });
      stage.classList.toggle('is-finale', active === CH.length - 1);
    }
    let near = 0; CH.forEach((c, i) => { if (pp >= c.a - .02) near = i; });
    if (near !== lastNear) { lastNear = near; stops.forEach((b, i) => b.classList.toggle('is-past', i <= near)); routeFill.style.transform = `scaleY(${(near / (CH.length - 1)).toFixed(3)})`; }
    const ps = pp.toFixed(3); if (ps !== lastP) { lastP = ps; stage.style.setProperty('--p', ps); }
    const off = pp > .012 || playing; if (off !== lastHint) { lastHint = off; hint.classList.toggle('is-off', off); }
    if (fogS) {
      const L = .2126 * fogS.r + .7152 * fogS.g + .0722 * fogS.b, tone = L > .46 ? 'light' : 'dark';
      const m = tone === 'light' ? .34 : .42, t = tone === 'light' ? [255, 255, 246] : [5, 18, 14];
      const v = [fogS.r * 255, fogS.g * 255, fogS.b * 255].map((c, i) => Math.round(lerp(c, t[i], m))).join(' ');
      if (v !== lastVeil) { lastVeil = v; stage.style.setProperty('--veil', v); }
      if (tone !== lastTone) { lastTone = tone; stage.dataset.tone = tone; }
    }
  }
  function tickPlay(dt) { if (!playing) return; playY += scrollMax() / 84 * dt; if (playY >= scrollMax()) { playY = scrollMax(); window.scrollTo(0, playY); stopPlay(); return; } window.scrollTo(0, playY); }

  let renderer;
  try { renderer = new THREE.WebGLRenderer({ canvas, antialias: (window.devicePixelRatio || 1) < 2, powerPreference: 'high-performance' }); } catch (e) { return plain(e); }

  const LOW = window.__ILM_Q ? window.__ILM_Q === 'low' : (Math.min(window.innerWidth, window.innerHeight) < 620 || (navigator.hardwareConcurrency || 8) <= 4);
  let dpr = Math.min(window.devicePixelRatio || 1, LOW ? 1.5 : 2);
  renderer.setPixelRatio(dpr); renderer.outputEncoding = THREE.sRGBEncoding; renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = .84;
  renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  const scene = new THREE.Scene(), camera = new THREE.PerspectiveCamera(40, 1, 1, 2600);

  /* ----- build the world ----- */
  const k = new Kit(), G = new Kit(), L = new Kit();
  buildTown(scene, k, G, L); buildBridge(k, L); buildVillage1(scene, k, G, L); buildVillage2(scene, k, G, L);
  scene.add(k.mesh(M.world)); scene.add(G.mesh(M.glow, false, false)); scene.add(L.mesh(M.lit, false, false));
  buildTerrain(scene, LOW); buildRoad(scene); buildWater(scene);
  const van = buildVan(scene);
  van.pos.copy(roadCurve.getPointAt(VAN_U[0]));
  buildActors(scene, van); buildPlants(scene, LOW);
  const sky = buildSky(scene, LOW);
  // signal rings on the last tower before the river
  const rings = [0, 1, 2].map(i => { const m = new THREE.Mesh(new THREE.RingGeometry(.92, 1, 40), new THREE.MeshBasicMaterial({ color: col('#f7f4e6'), transparent: true, opacity: 0, side: THREE.DoubleSide, depthWrite: false, fog: false })); m.position.copy(SPOT.tower); scene.add(m); return m; });
  const motes = (function () { const n = LOW ? 60 : 130, P = new Float32Array(n * 3), S = []; for (let i = 0; i < n; i++) S.push([R(-1, 1), R(-1, 1), R(-1, 1), R(TAU)]); const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.BufferAttribute(P, 3)); const m = new THREE.Points(g, new THREE.PointsMaterial({ map: glowTex, color: col('#fffbe0'), size: .16, transparent: true, opacity: .5, depthWrite: false, blending: THREE.AdditiveBlending, fog: false })); m.frustumCulled = false; scene.add(m); return { m, P, S, n }; })();
  TAGS.forEach(tg => { const el = document.createElement('span'); el.className = 'tag'; el.textContent = tg.text; tagBox.appendChild(el); tagEls.push(el); });
  if (document.fonts && document.fonts.ready) { try { document.fonts.load('600 60px Fraunces'); document.fonts.load('600 40px Figtree'); } catch (e) { } document.fonts.ready.then(() => setTimeout(redrawTextures, 60)); }

  const camPos = new THREE.Vector3(), camLook = new THREE.Vector3(), right = new THREE.Vector3(), up = new THREE.Vector3(), tmp = new THREE.Vector3(), prevVan = new THREE.Vector3().copy(van.pos);
  let fx = .62, fy = .5, intro = (RM || TEST || pT > .02) ? 0 : 1, introT = 0;
  function resize() {
    W = stage.clientWidth || window.innerWidth; Hh = stage.clientHeight || window.innerHeight; wide = !matchMedia('(max-width:820px) and (max-aspect-ratio:5/4),(max-aspect-ratio:1/1)').matches;
    renderer.setSize(W, Hh, false); camera.fov = wide ? 40 : (W / Hh < .7 ? 58 : 50);
  }
  function project() {
    const FW = W * (1 + 2 * Math.abs(fx - .5)), FH = Hh * (1 + 2 * Math.abs(fy - .5));
    camera.aspect = FW / FH; camera.setViewOffset(FW, FH, FW / 2 - fx * W, FH / 2 - fy * Hh, W, Hh); camera.updateProjectionMatrix();
  }
  window.addEventListener('resize', resize); resize();
  ANIMS.forEach(a => { a.was = false; a.fn(0, 0, p, sky.env); if (a.objs) for (const o of a.objs) o.visible = false; });

  let last = performance.now(), lastRaw = last, time = 0, acc = 0, accN = 0, tier = 0, settle = 0;
  function frame(now) {
    const dt = Math.min(.05, (now - last) / 1000); last = now; time += dt; frameNo++; uTime.value = time;
    const rawDt = Math.min(.25, (now - lastRaw) / 1000); lastRaw = now; tickPlay(rawDt); pT = scrollP();
    if (window.__ilmFixed === undefined && (window.scrollY || 0) > scrollMax() + window.innerHeight * 1.02) { requestAnimationFrame(frame); return; }      // the facts section covers the stage: rest the GPU
    if (window.__ilmFixed !== undefined) p = pT = window.__ilmFixed; else p += (pT - p) * ((RM || TEST) ? 1 : 1 - Math.exp(-dt * 4.2));
    if (Math.abs(pT - p) < .00002) p = pT;

    // van
    const u = vanU(p); roadCurve.getPointAt(u, van.pos); roadCurve.getTangentAt(u, van.tan); van.pos.y = .09;
    const moved = van.pos.distanceTo(prevVan), dir = Math.sign(van.tan.dot(tmp.subVectors(van.pos, prevVan))) || 1; prevVan.copy(van.pos);
    van.g.position.copy(van.pos); van.g.position.y += moved > .001 ? Math.sin(time * 17) * .012 : 0; van.g.rotation.y = Math.atan2(-van.tan.z, van.tan.x);
    for (const w of van.wheels) w.rotation.z -= moved * dir / .31;
    van.dAcc += moved; const dusty = van.pos.x > 104 && Math.abs(van.pos.x - 181) > 42;
    if (van.dAcc > 1.1 && dusty) { van.dAcc = 0; const s = van.dust[van.di++ % van.dust.length]; s.position.set(van.pos.x - van.tan.x * 1.9 + R(-.3, .3), .35, van.pos.z - van.tan.z * 1.9 + R(-.5, .5)); s.userData.life = 0; }
    for (const s of van.dust) { const l = s.userData.life; if (l < 1) { s.userData.life = l + dt * .7; s.material.opacity = Math.sin(l * Math.PI) * .32; s.scale.setScalar(.8 + l * 3.2); s.position.y += dt * .5; } else s.material.opacity = 0; }

    // camera
    let i = 0; while (i < CAM.length - 2 && p > CAM[i + 1].p) i++;
    hermite(camPos, 'pos', i, p, van.pos); hermite(camLook, 'look', i, p, van.pos);
    if (intro > 0) { introT += rawDt; intro = 1 - clamp(introT / 3.2); const e = intro * intro * intro; camPos.x -= 60 * e; camPos.y += 70 * e; camPos.z += 70 * e; }
    const dist = camPos.distanceTo(camLook);
    if (!RM) {
      ptr.sx += (ptr.x - ptr.sx) * (1 - Math.exp(-dt * 3)); ptr.sy += (ptr.y - ptr.sy) * (1 - Math.exp(-dt * 3));
      tmp.subVectors(camLook, camPos).normalize(); right.crossVectors(tmp, YAX).normalize(); up.crossVectors(right, tmp);
      const amt = Math.min(dist * .05, 2.2);
      camPos.addScaledVector(right, (ptr.sx + Math.sin(time * .23) * .35) * amt).addScaledVector(up, (-ptr.sy * .5 + Math.sin(time * .31) * .2) * amt);
    }
    const floor = H(camPos.x, camPos.z) + 1.15; if (camPos.y < floor) camPos.y = floor;
    camera.position.copy(camPos); camera.lookAt(camLook);
    const fin = sstep(.948, .972, p), tfx = wide ? lerp(p < .09 ? .6 : .64, .5, fin) : .5, tfy = wide ? lerp(.5, .58, fin) : lerp(.36, .6, fin);
    const e2 = 1 - Math.exp(-dt * 3); fx += (tfx - fx) * e2; fy += (tfy - fy) * e2; if (frameNo < 3 || TEST) { fx = tfx; fy = tfy; }
    project();

    // light and sky
    const env = sky.update(p, time, dt, camLook, camPos);
    const st = sstep(.3, .22, p), lan = sstep(.6, .7, p) * env.night;
    if (p < .45) { sky.lampA.position.set(0, 3.3, -12.4); sky.lampA.color.copy(col('#fff1d0')); sky.lampA.intensity = 1.25 * st; sky.lampA.distance = 17; }
    else { sky.lampA.position.copy(SPOT.lamp); sky.lampA.color.copy(col('#ffb45c')); sky.lampA.intensity = lan * (2.1 + Math.sin(time * 9) * .12 + Math.sin(time * 23) * .08); sky.lampA.distance = 15; }
    if (p < .6) { sky.lampB.position.set(299.6, 2.5, .6); sky.lampB.color.copy(col('#ffe6b0')); sky.lampB.intensity = .7 * sstep(.36, .4, p) * (1 - sstep(.54, .58, p)); sky.lampB.distance = 9; }
    else { sky.lampB.position.set(SPOT.phone.x + .35, .7, SPOT.phone.z); sky.lampB.color.copy(col('#c9ffe4')); sky.lampB.intensity = lan * (1.25 + Math.sin(time * 3.1) * .1); sky.lampB.distance = 6; }
    van.beams.forEach(b => b.material.opacity = sstep(.15, .5, env.night) * (p < .7 ? .85 : 0));
    const ringOn = sstep(.02, .06, p) * (1 - sstep(.36, .4, p)); rings.forEach((r, j) => { const kk = ((time * .32 + j / 3) % 1); r.scale.setScalar(1 + kk * 9); r.material.opacity = ringOn * (1 - kk) * .7; r.quaternion.copy(camera.quaternion); r.visible = ringOn > 0; });
    const mp = motes.m.geometry.attributes.position; for (let j = 0; j < motes.n; j++) { const s = motes.S[j]; motes.P[j * 3] = camLook.x + s[0] * 14 + Math.sin(time * .2 + s[3]) * 1.5; motes.P[j * 3 + 1] = Math.max(.3, camLook.y + 2.5 + s[1] * 3.5 + Math.sin(time * .3 + s[3] * 2) * .6); motes.P[j * 3 + 2] = camLook.z + s[2] * 14 + Math.cos(time * .17 + s[3]) * 1.5; } mp.needsUpdate = true; motes.m.material.opacity = (dist < 45 ? .5 : .5 * clamp(1 - (dist - 45) / 30)) * (1 - env.night * .6);

    for (const a of ANIMS) { const on = p > a.a - .035 && p < a.b + .035; if (on || a.was) a.fn(time, dt, p, env); if (a.objs && on !== a.was) for (const o of a.objs) o.visible = on; a.was = on; }

    // labels pinned to things in the scene
    TAGS.forEach((tg, j) => {
      const el = tagEls[j]; let show = p > tg.a && p < tg.b;
      if (show) { tmp.copy(tg.pos).project(camera); const x = (tmp.x * .5 + .5) * W, y = (-tmp.y * .5 + .5) * Hh; show = tmp.z < 1 && x > (wide ? W * .42 : 70) && x < W - (wide ? 170 : 70) && y > 96 && y < Hh * (wide ? .9 : .5); if (show) el.style.transform = `translate3d(${x.toFixed(1)}px, ${y.toFixed(1)}px, 0) translate(-50%, -100%)`; }
      if (el._on !== show) { el._on = show; el.classList.toggle('is-on', show); }
    });
    ui(p, env.fogS, dt);
    renderer.render(scene, camera);
    if (frameNo === 2) stage.classList.add('is-ready');

    // keep it smooth: drop resolution, then shadows, if frames run long
    if (!TEST && frameNo > 40) {
      acc += dt; accN++;
      if (accN >= 50) { const ms = acc / accN * 1000; acc = 0; accN = 0; if (ms > 27 && settle <= 0) { if (dpr > 1.01) { dpr = Math.max(1, dpr - .34); renderer.setPixelRatio(dpr); renderer.setSize(W, Hh, false); } else if (tier === 0) { tier = 1; sky.sun.shadow.mapSize.set(1024, 1024); if (sky.sun.shadow.map) { sky.sun.shadow.map.dispose(); sky.sun.shadow.map = null; } } else if (tier === 1 && ms > 36) { tier = 2; stage.classList.add('is-lite'); renderer.shadowMap.enabled = false; scene.traverse(o => { if (o.material) o.material.needsUpdate = true; }); } else if (tier === 2 && ms > 40) { tier = 3; GRASS.forEach(g => g.visible = false); } settle = 1; } else settle--; }
    }
    requestAnimationFrame(frame);
  }
  window.__ilm = { OCC, CAMPTS, TREES, jump(v) { window.__ilmFixed = v; }, release() { delete window.__ilmFixed; }, info: () => ({ p, dpr, tier, calls: renderer.info.render.calls, tris: renderer.info.render.triangles, LOW }), renderer, scene, camera };
  requestAnimationFrame(frame);
}

start();
}
/* ---------- boot: three.js from the CDN, with fallbacks; a plain readable page if 3D cannot run ---------- */
/* contact details come from one small config object, so they can be changed without touching anything else */
(function () {
  const c = window.ILM_CONFIG || {};
  document.querySelectorAll('[data-fill]').forEach(el => { const v = c[el.dataset.fill]; if (v) { el.textContent = v; el.classList.remove('is-empty'); } });
  document.querySelectorAll('[data-copy]').forEach(b => {
    const v = c[b.dataset.copy]; if (!v) { b.hidden = true; return; }
    b.addEventListener('click', () => { const done = () => { b.textContent = 'Copied'; setTimeout(() => b.textContent = 'Copy', 1600); }; try { navigator.clipboard.writeText(v).then(done, () => sel(b)); } catch (e) { sel(b); } });
  });
  function sel(b) { const t = b.parentNode.querySelector('[data-fill]'), r = document.createRange(); r.selectNodeContents(t); const g = getSelection(); g.removeAllRanges(); g.addRange(r); }
  const y = document.getElementById('year'); if (y) y.textContent = new Date().getFullYear();
})();
function plain(err) { if (err) console.warn('3D scene unavailable:', err); document.body.classList.add('plain'); }
(function boot() {
  const srcs = ['js/three.min.js'];
  const run = () => { try { const t0 = performance.now(); main(); window.__ilmBuildMs = Math.round(performance.now() - t0); } catch (e) { console.error(e); plain(e); } };
  const next = () => { if (window.THREE) return run(); const src = srcs.shift(); if (!src) return plain('three.js did not load'); const s = document.createElement('script'); s.src = src; s.onload = next; s.onerror = next; document.head.appendChild(s); };
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', next); else next();
})();
})();
