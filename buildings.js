// ============================================================================
// Building loader + procedural interior generator.
//  - getBuildings()      -> [{id, name, type, real}]  (real = Hekman only)
//  - loadFloors(id)      -> { floors, real, name, cellM }
// Hekman returns the real digitized interior; every other Calvin building gets a
// plausible interior generated to fit its REAL OSM footprint polygon. Same data
// shape the engine consumes: floors = array of arrays of row strings, chars
// '#'=wall 'o'=exterior '.'=floor 'S'=stair/exit 'E'=elevator. Deterministic per id.
// ============================================================================
(function (root) {
  const inNode = (typeof require !== 'undefined' && typeof module !== 'undefined');
  const CAMPUS = inNode ? require('./campus-data.js').CAMPUS : root.CAMPUS;
  const HEK = inNode ? require('./hekman-floor.js').HEKMAN_FLOORS : root.HEKMAN_FLOORS;

  const isHekman = b => /hekman/i.test(b.name || '');
  const M2FT = 3.28084, M2FT2 = 10.7639;
  const floorsFor = h => Math.max(1, Math.min(5, Math.round((h || 9) / 4)));

  // real dimensions from the OSM footprint (area, footprint span, height, floors)
  function dimsOf(b) {
    const r = b.ring; let a = 0, x0 = 1e9, y0 = 1e9, x1 = -1e9, y1 = -1e9;
    for (let i = 0; i < r.length; i++) {
      const [x, y] = r[i], [xn, yn] = r[(i + 1) % r.length];
      a += x * yn - xn * y; x0 = Math.min(x0, x); y0 = Math.min(y0, y); x1 = Math.max(x1, x); y1 = Math.max(y1, y);
    }
    const m2 = Math.abs(a) / 2;
    return {
      areaFt2: Math.round(m2 * M2FT2), wFt: Math.round((x1 - x0) * M2FT), dFt: Math.round((y1 - y0) * M2FT),
      htFt: Math.round((b.h || 9) * M2FT), floors: isHekman(b) ? HEK.length : floorsFor(b.h),
    };
  }

  function getBuildings() {
    return CAMPUS.buildings.map((b, i) => ({
      id: i, name: b.name || ('Unnamed #' + i), type: b.type || 'building', real: isHekman(b), dims: dimsOf(b),
    })).sort((a, b) => (b.real - a.real) || a.name.localeCompare(b.name));
  }

  function loadFloors(id) {
    const b = CAMPUS.buildings[id];
    if (isHekman(b)) return { floors: HEK, real: true, name: b.name, cellM: 1, dims: dimsOf(b) };
    const g = generate(b.ring, b.h || 9, id);
    return { floors: g.floors, real: false, name: b.name || ('Unnamed #' + id), cellM: g.cellM, dims: dimsOf(b) };
  }

  // ---- helpers ----
  function mulberry32(a) { return function () { a|=0; a=a+0x6D2B79F5|0; let t=Math.imul(a^a>>>15,1|a); t=t+Math.imul(t^t>>>7,61|t)^t; return ((t^t>>>14)>>>0)/4294967296; }; }
  function bbox(ring){let x0=1e9,y0=1e9,x1=-1e9,y1=-1e9;for(const [x,y] of ring){x0=Math.min(x0,x);y0=Math.min(y0,y);x1=Math.max(x1,x);y1=Math.max(y1,y);}return {x0,y0,x1,y1};}
  function pip(ring,x,y){let inside=false;for(let i=0,j=ring.length-1;i<ring.length;j=i++){const xi=ring[i][0],yi=ring[i][1],xj=ring[j][0],yj=ring[j][1];if(((yi>y)!==(yj>y))&&(x<(xj-xi)*(y-yi)/(yj-yi)+xi))inside=!inside;}return inside;}

  function generate(ring, h, seed) {
    const rnd = mulberry32((seed + 1) * 2654435761);
    const bb = bbox(ring);
    let W = Math.ceil(bb.x1 - bb.x0) + 3, H = Math.ceil(bb.y1 - bb.y0) + 3;
    let cellM = 1; const MAX = 150;
    if (W > MAX || H > MAX) { cellM = Math.max(W, H) / MAX; W = Math.ceil(W / cellM); H = Math.ceil(H / cellM); }
    const nFloors = floorsFor(h);
    const ox = bb.x0 - 1, oy = bb.y0 - 1;
    const idx = (c, r) => r * W + c;

    // interior mask from the real footprint
    const inside = new Uint8Array(W * H);
    const cells = [];
    for (let r = 0; r < H; r++) for (let c = 0; c < W; c++) {
      if (pip(ring, ox + (c + 0.5) * cellM, oy + (r + 0.5) * cellM)) { inside[idx(c, r)] = 1; cells.push([c, r]); }
    }
    if (cells.length < 12) { // tiny/degenerate: one open room the whole bbox
      for (let r = 1; r < H - 1; r++) for (let c = 1; c < W - 1; c++) inside[idx(c, r)] = 1;
      cells.length = 0; for (let r = 0; r < H; r++) for (let c = 0; c < W; c++) if (inside[idx(c, r)]) cells.push([c, r]);
    }
    let cx = 0, cy = 0; for (const [c, r] of cells) { cx += c; cy += r; } cx = Math.round(cx / cells.length); cy = Math.round(cy / cells.length);

    // stair columns (aligned across floors), kept clear of the perimeter
    const inner = cells.filter(([c, r]) => c > 3 && c < W - 4 && r > 3 && r < H - 4);
    const pool = inner.length ? inner : cells;
    const stairs = [pool[(rnd() * pool.length) | 0]];
    if (cells.length > 500) stairs.push(pool[(rnd() * pool.length) | 0]);

    // exit doors: interior-boundary cells spread by angle around the centroid
    const boundary = cells.filter(([c, r]) => {
      for (const [dc, dr] of [[-1,0],[1,0],[0,-1],[0,1]]) { const cc=c+dc, rr=r+dr; if (cc<0||rr<0||cc>=W||rr>=H||!inside[idx(cc,rr)]) return true; } return false;
    });
    boundary.sort((a, b) => Math.atan2(a[1]-cy, a[0]-cx) - Math.atan2(b[1]-cy, b[0]-cx));
    const nExits = Math.max(2, Math.min(4, Math.round(cells.length / 1500) + 2));
    const exits = []; for (let k = 0; k < nExits && boundary.length; k++) exits.push(boundary[Math.floor(k * boundary.length / nExits)]);

    const inCorridor = (c, r) => Math.abs(r - cy) <= 1 || Math.abs(c - cx) <= 1; // central cross corridor
    const nearEdge = (c, r) => {
      for (let dr=-2; dr<=2; dr++) for (let dc=-2; dc<=2; dc++) { const cc=c+dc, rr=r+dr; if (cc<0||rr<0||cc>=W||rr>=H||!inside[idx(cc,rr)]) return true; } return false;
    };

    const P = 9, mid = P>>1, floors = [];   // room pitch (rich grid of rooms with single-cell doors)
    for (let f = 0; f < nFloors; f++) {
      const g = []; for (let r = 0; r < H; r++) g.push(new Array(W).fill('o'));
      for (const [c, r] of cells) g[r][c] = '.';
      for (const [c, r] of boundary) g[r][c] = '#';
      // room lattice: walls on every P-th row/col, leaving a 1-cell perimeter corridor
      for (const [c, r] of cells) {
        if (g[r][c] !== '.') continue;
        if ((c % P === 0 || r % P === 0) && !nearEdge(c, r)) g[r][c] = '#';
      }
      // one 1-cell doorway at the midpoint of every wall segment → rooms connect, fire must channel through doors
      for (const [c, r] of cells) {
        if (g[r][c] !== '#' || nearEdge(c, r)) continue;
        const onV = (c % P === 0), onH = (r % P === 0);
        if (onV && !onH && (r % P) === mid) g[r][c] = '.';        // door through a vertical wall
        else if (onH && !onV && (c % P) === mid) g[r][c] = '.';   // door through a horizontal wall
      }
      // stairwells: clear a 3x3 landing, mark S on upper floors (aligned); ground floor keeps '.' landing
      for (const [sc, sr] of stairs) {
        for (let dr=-1; dr<=1; dr++) for (let dc=-1; dc<=1; dc++) { const cc=sc+dc, rr=sr+dr; if (cc>=0&&rr>=0&&cc<W&&rr<H&&inside[idx(cc,rr)]) g[rr][cc] = '.'; }
        if (f > 0 && inside[idx(sc, sr)]) g[sr][sc] = 'S';
      }
      // exits: only on the ground floor, on the perimeter, with an open cell just inside
      if (f === 0) for (const [ec, er] of exits) {
        g[er][ec] = 'S';
        for (const [dc, dr] of [[-1,0],[1,0],[0,-1],[0,1]]) { const cc=ec+dc, rr=er+dr; if (cc>=0&&rr>=0&&cc<W&&rr<H&&inside[idx(cc,rr)]) g[rr][cc] = '.'; }
      }
      floors.push(g.map(row => row.join('')));
    }
    return { floors, cellM };
  }

  const api = { getBuildings, loadFloors };
  if (typeof module !== 'undefined') module.exports = api;
  root.Buildings = api;
})(typeof window !== 'undefined' ? window : globalThis);
