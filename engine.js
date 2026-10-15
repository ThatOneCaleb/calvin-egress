// ===========================================================================
// Calvin Egress — evacuation engine
//
// This is an agent-based model, and it's deliberately written to read like a
// NetLogo model so it's easy to follow if you've seen one before:
//
//     NetLogo                        here
//     -------                        ----
//     globals                        the consts below + this.params
//     patches-own (floor/wall/fire)  one typed array per floor: type, fire, smoke, door
//     turtles-own (a person's state) fields on each person object (speed, dose, ...)
//     to setup ... end               setup()      — build the world, scatter people
//     to go ... tick end             go()         — advance one tick
//     ask turtles [ ... ]            ask(people, p => { ... })
//
// Everything is in real units: one patch is 1 m, one tick is 0.25 s. Floor 0 is
// the ground floor (its stairs are the actual exits); higher floors stack above
// it and drain downward through the stairwells.
//
// Where the numbers come from, so they can be checked:
//   walking speeds     Weidmann / Fruin
//   pre-movement time  SFPE (voice evacuation beats a bell)
//   smoke tenability    an FED-style dose
// It is a routing + tenability model, not CFD fire. See validation.html.
// ===========================================================================

'use strict';

// ---- globals --------------------------------------------------------------
const DT = 0.25;        // seconds per tick (small enough that walking reads smoothly)
const CELL_M = 1.0;     // metres per patch
const V_FREE = 1.34;    // free-flow walking speed, m/s — healthy adult (Weidmann)
const STAIR_TICKS = 4;  // ticks spent on a landing before dropping to the floor below

// patch types. kept as small ints because a whole floor lives in one typed array.
const WALL = 0, FLOOR = 1, STAIR = 2, ELEV = 3;
const isNav = t => t === FLOOR || t === STAIR || t === ELEV;   // can a person stand here?

// Four mobility groups. `speed` scales V_FREE; `size` is only for drawing.
// Ranges are the usual Fruin/SFPE figures for mixed populations.
const GROUPS = {
  able:     { speed: 1.00, size: 1.00 },
  older:    { speed: 0.72, size: 0.95 },
  child:    { speed: 0.66, size: 0.66 },
  impaired: { speed: 0.42, size: 1.15 },   // assisted / wheelchair
};
const DEFAULT_MIX = { able: 0.82, older: 0.10, child: 0.03, impaired: 0.05 };

// draw one group at random from the mix (roulette wheel over the four shares)
function pickGroup(mix) {
  const m = mix || DEFAULT_MIX;
  let x = Math.random(), acc = 0;
  for (const k of ['able', 'older', 'child', 'impaired']) {
    acc += m[k] || 0;
    if (x <= acc) return k;
  }
  return 'able';
}

// NetLogo's `ask`: run a block once for every member of an agentset.
function ask(agentset, block) {
  for (const a of agentset) block(a);
}

const clamp01 = x => Math.max(0, Math.min(1, x));

// one draw from a standard normal (Box–Muller) — handy for giving each person
// slightly different traits instead of cloning everyone.
function randn() {
  let u = 0, v = 0;
  while (u === 0) u = Math.random();
  while (v === 0) v = Math.random();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}

class EvacSim {
  // The constructor builds the *world* — everything static about the building.
  // People are created later in setup(), because you re-scatter them every run.
  constructor(floors) {
    this.floors = floors;              // array of floors; each floor is an array of row strings
    this.F = floors.length;
    this.H = floors[0].length;
    this.W = floors[0].reduce((m, row) => Math.max(m, row.length), 0);
    const N = this.W * this.H;

    // --- patch variables, one typed array per floor ---
    this.type  = [];   // FLOOR / WALL / STAIR / ELEV
    this.field = [];    // distance-to-exit (the floor field); -1 = unreachable
    this.fire  = [];    // 1 = on fire
    this.smoke = [];    // 0..1 smoke concentration
    this.occ   = [];    // index of the person standing here, or -1 (one per patch)
    for (let f = 0; f < this.F; f++) {
      const t = new Uint8Array(N);
      for (let r = 0; r < this.H; r++) {
        const row = floors[f][r];
        for (let c = 0; c < this.W; c++) {
          const ch = c < row.length ? row[c] : 'o';
          t[r * this.W + c] = ch === '.' ? FLOOR : ch === 'S' ? STAIR : ch === 'E' ? ELEV : WALL;
        }
      }
      this.type.push(t);
      this.field.push(new Int32Array(N));
      this.fire.push(new Uint8Array(N));
      this.smoke.push(new Float32Array(N));
      this.occ.push(new Int32Array(N).fill(-1));
    }

    // --- infer rooms and doors from the wall grid ---
    // A door is a one-patch gap in a wall line (an opening between two rooms).
    // We care because fire and smoke get throttled crossing a door, so they tear
    // through open rooms but stall at the doorways. A room is just a connected
    // blob of navigable patches (flood fill).
    this.door = [];
    this.room = [];
    const navAt = (f, i) => isNav(this.type[f][i]);
    const solidAt = (f, c, r) =>
      (c < 0 || r < 0 || c >= this.W || r >= this.H) ? true : this.type[f][r * this.W + c] === WALL;

    for (let f = 0; f < this.F; f++) {
      const door = new Uint8Array(N);
      for (let r = 0; r < this.H; r++) for (let c = 0; c < this.W; c++) {
        const i = r * this.W + c;
        if (!navAt(f, i)) continue;
        const L = solidAt(f, c - 1, r), R = solidAt(f, c + 1, r);
        const U = solidAt(f, c, r - 1), D = solidAt(f, c, r + 1);
        // walls on two opposite sides and open on the other two => it's a doorway
        if ((L && R && !U && !D) || (U && D && !L && !R)) door[i] = 1;
      }
      this.door.push(door);

      const room = new Int32Array(N).fill(-1);
      let rid = 0;
      for (let s = 0; s < N; s++) {
        if (!navAt(f, s) || room[s] !== -1) continue;
        const stack = [s]; room[s] = rid;
        while (stack.length) {
          const j = stack.pop(), jc = j % this.W;
          for (const off of [-1, 1, -this.W, this.W]) {
            const k = j + off;
            if (off === -1 && jc === 0) continue;             // don't wrap across the left edge
            if (off === 1 && jc === this.W - 1) continue;     // ...or the right edge
            if (k < 0 || k >= N || room[k] !== -1 || !navAt(f, k)) continue;
            room[k] = rid; stack.push(k);
          }
        }
        rid++;
      }
      this.room.push(room);
    }

    // Which stairwells actually go somewhere? Ground-floor stairs are exits, so
    // they're always valid. An upstairs stair only counts if there's a walkable
    // patch roughly below it — otherwise it's a dead end and nobody should route
    // to it. Precomputed once because the building doesn't move.
    this.DESC_R = 12;
    this.stairOK = [];
    for (let f = 0; f < this.F; f++) {
      const ok = new Uint8Array(N);
      for (let i = 0; i < N; i++) {
        if (this.type[f][i] !== STAIR) continue;
        if (f === 0) { ok[i] = 1; continue; }
        const c = i % this.W, r = (i / this.W) | 0;
        outer:
        for (let rad = 0; rad <= this.DESC_R; rad++)
          for (let dr = -rad; dr <= rad; dr++) for (let dc = -rad; dc <= rad; dc++) {
            if (Math.max(Math.abs(dr), Math.abs(dc)) !== rad) continue;   // ring at this radius
            const cc = c + dc, rr = r + dr;
            if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
            if (this.passable(f - 1, this.idx(cc, rr))) { ok[i] = 1; break outer; }
          }
      }
      this.stairOK.push(ok);
    }

    this.setup({});
  }

  idx(c, r) { return r * this.W + c; }

  // can a person enter this patch right now? walkable, not burning, not a locked exit.
  passable(f, i) {
    const t = this.type[f][i];
    return isNav(t) && !this.fire[f][i] && !(f === 0 && this.blockedExit && this.blockedExit.has(i));
  }

  // The floor field: a breadth-first wave out from every working exit/stair on a
  // floor, labelling each patch with its step-distance to safety. People then
  // just walk downhill on it. Recomputed when fire closes a route.
  buildFloorField(f) {
    const { W, H } = this, N = W * H, field = this.field[f];
    field.fill(-1);
    let frontier = [];
    for (let i = 0; i < N; i++)
      if (this.type[f][i] === STAIR && !this.fire[f][i] && this.stairOK[f][i] && !(f === 0 && this.blockedExit.has(i))) {
        field[i] = 0; frontier.push(i);
      }
    const nb = [-1, 1, -W, W];
    while (frontier.length) {
      const next = [];
      for (const i of frontier) {
        const d = field[i], c = i % W;
        for (const off of nb) {
          if (off === -1 && c === 0) continue;
          if (off === 1 && c === W - 1) continue;
          const j = i + off;
          if (j < 0 || j >= N || field[j] !== -1 || !this.passable(f, j)) continue;
          field[j] = d + 1; next.push(j);
        }
      }
      frontier = next;
    }
  }

  // ---- setup: (re)build a run -------------------------------------------
  // Clears the hazards, recomputes routes, and scatters `population` people over
  // the walkable floor area. Called once per run (reset() is kept as an alias so
  // existing callers don't break).
  setup(params) {
    const p = Object.assign({
      population: 200, medianPreMoveS: 20, cooperation: 0.5,
      vFree: V_FREE, fire: false, fireCell: null, fireSpread: 0.25,
      sprinklers: false, doorPolicy: 'closed', detectionTime: 30, alarmType: 'voice',
      blockedExits: 0, demographics: null,
      // levers a campus can actually turn (0 = off / no effect)
      wardens: 0, familiarity: 0, signage: 0, smartGuidance: 0, personalAlert: 0, smokeVents: 0,
      clutter: 0, herding: 0, stairPressurized: false, evacElevators: false, phased: false, night: false,
      // human factors that "shouldn't" matter — wire them in and let the model decide
      belongings: 0, phone: 0, cohesion: 0, attire: 0, noise: 0, urgency: 0, handrails: false,
      ceiling: 0, slip: 0, daylight: 0, exitConspicuity: 0,
    }, params);
    this.params = p;

    // Turn the levers into the handful of multipliers the model actually uses.
    this.alarmAt       = p.detectionTime * (1 - 0.7 * p.personalAlert) * (1 + 0.6 * p.noise); // alerts speed detection; background noise masks the alarm
    this.smokeVentFactor = 1 - 0.7 * p.smokeVents;                     // exhaust vents slow smoke build-up
    this.speedMul      = (1 - 0.4 * p.clutter) * (1 - 0.2 * p.attire) * (1 - 0.15 * p.slip);
    this.crushMul      = (1 + 0.8 * p.slip + 0.6 * p.urgency) * (p.handrails ? 0.6 : 1); // falls: slip/urgency up, handrails down
    this.smokeDoseMul  = 1 + 0.6 * p.ceiling;                          // low ceilings bring smoke to head height sooner
    this.wrongTurnMul  = Math.max(0, 1 - 0.8 * p.signage - 0.9 * p.smartGuidance - 0.5 * p.familiarity - 0.4 * p.daylight - 0.5 * p.exitConspicuity);
    this.sprinklerActive = false;
    this.ignitedAt = null;

    const N = this.W * this.H;

    // Doors hold the fire back for a burn-through time. Propped-open barely
    // resists; a self-closer buys ~45 s; a rated/auto-closing door holds for
    // ~10 min, which for a normal run means it just doesn't go.
    this.doorHeat = this.type.map(() => new Float32Array(N));
    this.burnThrough = ({ open: 3, closed: 45, auto: 600 })[p.doorPolicy] ?? 45;

    // Optionally lock some ground-floor exits so everyone funnels to the rest.
    // Always leave at least one open, or the field has nowhere to drain.
    this.blockedExit = new Set();
    if (p.blockedExits > 0) {
      const exits = [];
      for (let i = 0; i < N; i++) if (this.type[0][i] === STAIR) exits.push(i);
      for (let k = exits.length - 1; k > 0; k--) { const j = (Math.random() * (k + 1)) | 0; [exits[k], exits[j]] = [exits[j], exits[k]]; }
      for (let k = 0; k < Math.min(p.blockedExits, exits.length - 1); k++) this.blockedExit.add(exits[k]);
    }

    // wipe hazards and rebuild every floor's routes
    for (let f = 0; f < this.F; f++) {
      this.fire[f].fill(0); this.smoke[f].fill(0); this.occ[f].fill(-1);
      this.buildFloorField(f);
    }

    // Spawn spots per floor: any reachable walkable patch. Shuffle each floor's
    // list so we're not biased toward the top-left, then hand floors a share of
    // the population proportional to their walkable area.
    const cand = [], walk = [];
    let sum = 0;
    for (let f = 0; f < this.F; f++) {
      const list = [];
      for (let i = 0; i < N; i++)
        if ((this.type[f][i] === FLOOR || this.type[f][i] === ELEV) && this.field[f][i] > 0) list.push(i);
      for (let k = list.length - 1; k > 0; k--) { const j = (Math.random() * (k + 1)) | 0; [list[k], list[j]] = [list[j], list[k]]; }
      cand.push(list); walk.push(list.length); sum += list.length;
    }

    this.agents = [];
    for (let f = 0; f < this.F; f++) {
      const n = Math.min(cand[f].length, Math.round(p.population * walk[f] / sum));
      for (let k = 0; k < n; k++) {
        const i = cand[f][k];
        const person = this.spawnPerson(f, i % this.W, (i / this.W) | 0, p);
        this.occ[f][i] = this.agents.length;
        this.agents.push(person);
      }
    }

    this.hasFire = false; this.fireFloor = null;
    if (p.fire) this.ignite(p.fireCell);

    // run bookkeeping
    this.t = 0;
    this.evacuated = 0; this.crushDeaths = 0; this.smokeDeaths = 0;
    this.peakDensity = 0; this.done = false; this.rset = null;
    this.fireGrowing = this.hasFire;
    this._stall = 0; this._lastProg = 0; this.stalled = false;
  }

  reset(params) { return this.setup(params); }   // alias — the UI calls reset()

  // Make one person (a "turtle"). Each gets an OCEAN personality, which in turn
  // sets how fast they walk, how long they dawdle before moving, and how hard
  // they push in a crowd. Giving everyone slightly different numbers is the whole
  // point — a crowd of identical agents behaves nothing like a real one.
  spawnPerson(f, c, r, p) {
    const E = clamp01(0.5 + 0.15 * randn());         // extraversion
    const C = clamp01(0.5 + 0.15 * randn());         // conscientiousness
    const A = clamp01(p.cooperation + 0.15 * randn()); // agreeableness, centred on the cooperation lever
    const Nn = clamp01(0.5 + 0.15 * randn());        // neuroticism
    const assertiveness = 0.5 * E + 0.5 * (1 - A);
    const awareness = C;
    const fitness = clamp01(0.6 + 0.15 * randn());

    const g = pickGroup(p.demographics), G = GROUPS[g];
    const v = (p.vFree + 0.26 * randn()) * (0.9 + 0.15 * fitness + 0.05 * assertiveness) * G.speed;

    // pre-movement: how long before they actually start heading out. Voice evac
    // roughly halves it vs a bell (SFPE); then a pile of human factors nudge it.
    const alarmF = (p.alarmType === 'bell') ? 1.0 : 0.62;
    let preMove = Math.max(0, p.medianPreMoveS * alarmF * (1 - 0.5 * awareness) * Math.exp(0.5 * randn()));
    const warden = Math.random() < (p.wardens || 0);
    if (warden) preMove *= 0.1;                      // a warden is already moving
    preMove *= (1 - 0.5 * (p.wardens || 0));         // and gets the people around them moving too
    preMove *= (1 - 0.4 * (p.familiarity || 0));     // people who've drilled react faster
    if (p.night) preMove *= 3;                       // asleep: slow to wake and go
    preMove += (p.belongings || 0) * 40 * Math.random();  // stopping for coat/laptop
    preMove *= (1 + 0.5 * (p.phone || 0));           // heads-down on a phone
    preMove *= (1 + 0.3 * (p.cohesion || 0));        // won't leave without their group
    preMove *= (1 - 0.3 * (p.urgency || 0));         // an urgent tone gets them up sooner

    return {
      floor: f, c, r, cell: this.idx(c, r),
      composure: 1 - Nn, assertiveness, altruism: A, awareness,
      group: g, gsize: G.size, warden, herding: (p.herding || 0),
      vComfort: Math.max(0.35, Math.min(2.0, v)),   // their comfortable speed, clamped to something sane
      preMove, budget: 0, dose: 0,
      onStair: false, stairT: 0,
      state: 0,   // 0 waiting, 1 moving, 2 out, 3 crushed, 4 overcome by smoke
    };
  }

  // ---- fire ignition ----------------------------------------------------
  // Light a small patch, not a single cell — a real fire isn't 1 m wide, and a
  // one-cell flame is almost invisible in the 3D view.
  seedFire(f, i) {
    if (i < 0) return false;
    const c = i % this.W, r = (i / this.W) | 0, cells = [i];
    for (const [dc, dr] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
      const cc = c + dc, rr = r + dr;
      if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
      const j = this.idx(cc, rr), t = this.type[f][j];
      if (t === FLOOR || t === ELEV) cells.push(j);
    }
    for (const j of cells) { this.fire[f][j] = 1; this.smoke[f][j] = 1; }
    this.fireFloor = f; this.hasFire = true; this.fireGrowing = true;
    if (this.ignitedAt == null) this.ignitedAt = this.t;
    this.buildFloorField(f);
    return true;
  }

  ignite(cell) {
    let f, i;
    if (cell) { f = cell[2] || 0; i = this.idx(cell[0], cell[1]); }
    else { f = 0; i = this.nearestPassable(0, this.W >> 1, this.H >> 1, 60); }  // default: light the middle of the ground floor
    this.seedFire(f, i);
  }

  // click-to-place from the UI; returns true if the spot is a valid room patch
  placeFire(f, c, r) {
    const i = this.idx(c, r);
    if (this.type[f][i] !== FLOOR && this.type[f][i] !== ELEV) return false;
    return this.seedFire(f, i);
  }

  // fraction of the 8 neighbours that are occupied — a cheap local density
  crowdDensity(f, c, r) {
    let occupied = 0, cells = 0;
    for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) {
      if (!dc && !dr) continue;
      const cc = c + dc, rr = r + dr;
      if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
      const j = this.idx(cc, rr);
      if (this.type[f][j] === WALL) continue;
      cells++; if (this.occ[f][j] >= 0) occupied++;
    }
    return cells ? occupied / cells : 0;
  }

  // ---- the three ways a person picks their next patch -------------------

  // normal case: step to the free neighbour that's closest to an exit (downhill
  // on the floor field). Ground-floor exits "absorb" people, so they're allowed
  // even when occupied.
  stepDownhill(a) {
    const f = a.floor, field = this.field[f], here = field[a.cell];
    let best = -1, bestD = here;
    for (const [dc, dr] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
      const cc = a.c + dc, rr = a.r + dr;
      if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
      const j = this.idx(cc, rr);
      if (!this.passable(f, j) || field[j] === -1) continue;
      const exit = (this.type[f][j] === STAIR && f === 0);
      if (!exit && this.occ[f][j] >= 0) continue;   // someone's already there
      if (field[j] < bestD) { bestD = field[j]; best = j; }
    }
    return best;
  }

  // thick smoke: lose the thread and take any open patch, not necessarily toward safety
  stepRandom(a) {
    const f = a.floor, opts = [];
    for (const [dc, dr] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
      const cc = a.c + dc, rr = a.r + dr;
      if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
      const j = this.idx(cc, rr);
      if (!this.passable(f, j) || this.field[f][j] === -1) continue;
      const exit = (this.type[f][j] === STAIR && f === 0);
      if (!exit && this.occ[f][j] >= 0) continue;
      opts.push(j);
    }
    return opts.length ? opts[(Math.random() * opts.length) | 0] : -1;
  }

  // "follow the crowd": head for the open neighbour that has the most people
  // around it. Falls back to the sensible downhill move if nothing qualifies.
  stepWithCrowd(a) {
    const f = a.floor;
    let best = -1, bestOcc = -1;
    for (const [dc, dr] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
      const cc = a.c + dc, rr = a.r + dr;
      if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
      const j = this.idx(cc, rr);
      if (!this.passable(f, j) || this.field[f][j] === -1) continue;
      const exit = (this.type[f][j] === STAIR && f === 0);
      if (!exit && this.occ[f][j] >= 0) continue;
      let occ = 0; const jc = j % this.W, jr = (j / this.W) | 0;
      for (const [q, w] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
        const xc = jc + q, xr = jr + w;
        if (xc < 0 || xr < 0 || xc >= this.W || xr >= this.H) continue;
        if (this.occ[f][this.idx(xc, xr)] >= 0) occ++;
      }
      if (occ > bestOcc) { bestOcc = occ; best = j; }
    }
    return best !== -1 ? best : this.stepDownhill(a);
  }

  // Move person k down one floor via the stairwell they're sitting on. Looks for
  // a free landing spot roughly below; if they reach the ground floor on a stair,
  // they're out.
  takeStairDown(k) {
    const a = this.agents[k], f = a.floor - 1;
    for (let rad = 0; rad <= this.DESC_R; rad++) {
      for (let dr = -rad; dr <= rad; dr++) for (let dc = -rad; dc <= rad; dc++) {
        if (Math.max(Math.abs(dr), Math.abs(dc)) !== rad) continue;
        const cc = a.c + dc, rr = a.r + dr;
        if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
        const j = this.idx(cc, rr);
        const landExit = (this.type[f][j] === STAIR && f === 0);
        if (this.passable(f, j) && this.field[f][j] >= 0 && (landExit || this.occ[f][j] < 0)) {
          this.occ[a.floor][a.cell] = -1;                     // step off the stair above
          a.floor = f; a.c = cc; a.r = rr; a.cell = j; a.budget = 0; a.onStair = false;
          if (this.type[f][j] === STAIR) {
            if (f === 0) { a.state = 2; this.evacuated++; }    // made it to a ground exit
            else { this.occ[f][j] = k; a.onStair = true; a.stairT = STAIR_TICKS; } // keep going down
          } else this.occ[f][j] = k;
          return true;
        }
      }
    }
    return false;
  }

  // ---- go: one tick -----------------------------------------------------
  // Advance the clock, grow the fire on its own slower schedule, then ask every
  // still-active person to take their turn — closest-to-exit first, so queues
  // resolve from the front like real ones do.
  go() {
    if (this.done) return;
    this.t += DT;   // tick

    if (this.hasFire && Math.round(this.t / DT) % 4 === 0) this.spreadFireAndSmoke();

    const movers = this.agents
      .map((a, k) => k)
      .filter(k => this.agents[k].state <= 1)
      .sort((k1, k2) =>
        this.field[this.agents[k1].floor][this.agents[k1].cell] -
        this.field[this.agents[k2].floor][this.agents[k2].cell]);

    ask(movers, (k) => {
      const a = this.agents[k], f = a.floor;

      // still waiting? hold until the alarm reaches this floor, then burn down
      // their personal pre-movement timer. (phased evac staggers the upper floors.)
      if (a.state === 0) {
        const gate = this.alarmAt + (this.params.phased ? a.floor * 15 : 0);
        if (this.t < gate) return;
        a.preMove -= DT;
        if (a.preMove <= 0) a.state = 1; else return;
      }

      // anyone standing on a ground-floor exit is out, full stop
      if (f === 0 && this.type[0][a.cell] === STAIR) { this.occ[0][a.cell] = -1; a.state = 2; this.evacuated++; return; }

      // tenability check: breathe smoke, maybe get overcome; standing in fire is fatal
      if (this.hasFire) {
        const onStair = this.type[f][a.cell] === STAIR;
        const protectedStair = this.params.stairPressurized && onStair;   // pressurized stairs stay clear
        const s = protectedStair ? 0 : this.smoke[f][a.cell];
        if (s > 0.4) a.dose += (s - 0.4) * DT * this.smokeDoseMul;          // FED: only real smoke counts toward the dose
        if ((this.fire[f][a.cell] && !protectedStair) || a.dose > 3.0) { this.kill(k, 4); return; }
      }

      // on a stair landing: wait out the capacity delay, then drop a floor
      if (a.onStair) {
        if (--a.stairT <= 0) { if (!this.takeStairDown(k)) a.stairT = 1; }
        return;
      }

      // crowd crush: in a jam, an assertive/selfish shove can put someone on the floor
      const dens = this.crowdDensity(f, a.c, a.r);
      if (dens > this.peakDensity) this.peakDensity = dens;
      if (dens >= 0.8) {
        const push = a.assertiveness * (1 - a.altruism);
        if (Math.random() < 0.0010 * push * this.crushMul) { this.kill(k, 3); return; }
      }

      // how far they get to move this tick: comfortable speed, slowed by the local
      // density (Weidmann) and by poor visibility in smoke, scaled to the timestep.
      const smokeHere = this.hasFire ? this.smoke[f][a.cell] : 0;
      const vis = Math.max(0.2, 1 - 0.7 * smokeHere);
      a.budget += a.vComfort * Math.max(0.15, 1 - 0.85 * dens) * vis * this.speedMul * DT;
      if (a.budget < CELL_M) return;   // not enough "distance saved up" to cross a whole patch yet

      // pick the next patch: usually downhill; sometimes lost in smoke; sometimes herding
      let dest;
      if (smokeHere > 0.35 && Math.random() < 0.3 * smokeHere * this.wrongTurnMul) dest = this.stepRandom(a);
      else if (a.herding > 0 && Math.random() < 0.22 * a.herding) dest = this.stepWithCrowd(a);
      else dest = this.stepDownhill(a);

      // boxed in? after enough stuck ticks, take a random step to break the standoff
      if (dest === -1) { a.stuck = (a.stuck || 0) + 1; if (a.stuck > 40) dest = this.stepRandom(a); }
      if (dest === -1) { a.budget = CELL_M; return; }
      a.stuck = 0;

      // commit the move
      this.occ[f][a.cell] = -1;
      a.cell = dest; a.c = dest % this.W; a.r = (dest / this.W) | 0; a.budget -= CELL_M;
      if (this.type[f][dest] === STAIR) {
        if (f === 0) { a.state = 2; this.evacuated++; }     // walked straight out
        else {                                              // stepped into a stairwell
          this.occ[f][dest] = k; a.onStair = true;
          a.stairT = (this.params.evacElevators && a.group === 'impaired') ? 1 : STAIR_TICKS; // evac elevators fast-track the impaired
        }
      } else this.occ[f][dest] = k;
    });

    // end-of-tick bookkeeping
    const active = this.agents.some(a => a.state <= 1);
    if (!active && this.rset == null) this.rset = this.t;            // freeze the clearance time (RSET)
    this.done = !active && !(this.hasFire && this.fireGrowing);      // keep running while the fire is still spreading

    // stall guard: if nobody's gotten out (or died) for ~60 s and people remain,
    // call it — whoever's left is trapped, and we don't want an endless run.
    const progress = this.evacuated + this.crushDeaths + this.smokeDeaths;
    if (progress === this._lastProg) this._stall++; else { this._stall = 0; this._lastProg = progress; }
    if (!this.done && active && !this.fireGrowing && this._stall > 240) {
      this.done = true; this.stalled = true;
      if (this.rset == null) this.rset = this.t;
    }
  }

  step() { return this.go(); }   // alias — the UI's run loop calls step()

  kill(k, state) {
    const a = this.agents[k];
    a.state = state; this.occ[a.floor][a.cell] = -1;
    if (state === 3) this.crushDeaths++; else this.smokeDeaths++;
  }

  // nearest walkable patch within radius R (spiralling out ring by ring)
  nearestPassable(f, c, r, R) { return this.nearestOfType(f, c, r, R, null); }

  // nearest patch of a given type within R (want === null means "any walkable")
  nearestOfType(f, c, r, R, want) {
    for (let rad = 0; rad <= R; rad++)
      for (let dr = -rad; dr <= rad; dr++) for (let dc = -rad; dc <= rad; dc++) {
        if (Math.max(Math.abs(dr), Math.abs(dc)) !== rad) continue;
        const cc = c + dc, rr = r + dr;
        if (cc < 0 || rr < 0 || cc >= this.W || rr >= this.H) continue;
        const t = this.type[f][this.idx(cc, rr)];
        if (want === null ? isNav(t) : t === want) return this.idx(cc, rr);
      }
    return -1;
  }

  // ---- spread fire and smoke, across every floor ------------------------
  // Within a floor the fire creeps to neighbours (fast in the open, stalled at
  // doors); smoke runs ahead of it down corridors; and a stairwell acts like a
  // chimney, carrying both to the floors above and below.
  spreadFireAndSmoke() {
    const { W, H, F } = this, N = W * H;
    const policy = this.params.doorPolicy || 'closed';
    const FDOOR = ({ open: 0.60, closed: 0.10, auto: 0.0 })[policy] ?? 0.10;  // flame getting through a doorway
    const SDOOR = ({ open: 0.90, closed: 0.45, auto: 0.0 })[policy] ?? 0.45;  // smoke getting through a doorway

    // t²-ish growth: a young fire is small and slow, then ramps toward fully
    // developed over the first minute and a half.
    const growth = Math.max(0.25, Math.min(1, (this.t - (this.ignitedAt || 0)) / 90));

    // sprinklers wait until the fire reaches a size, then hold it there — which
    // is really a cap on growth, and mostly buys time (extends ASET).
    if (this.params.sprinklers && !this.sprinklerActive) {
      let burning = 0;
      for (let f = 0; f < F; f++) { const fr = this.fire[f]; for (let i = 0; i < N; i++) if (fr[i]) burning++; }
      if (burning >= 14) this.sprinklerActive = true;
    }
    const active = !this.sprinklerActive;   // is the fire still allowed to grow?

    const changed = new Array(F).fill(false);
    let frontier = false;

    // --- within-floor spread ---
    for (let f = 0; f < F; f++) {
      const fire = this.fire[f], smoke = this.smoke[f], door = this.door[f], add = [];
      for (let i = 0; i < N; i++) {
        if (!fire[i]) continue;
        const c = i % W, r = (i / W) | 0;
        for (const [dc, dr] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
          const cc = c + dc, rr = r + dr;
          if (cc < 0 || rr < 0 || cc >= W || rr >= H) continue;
          const j = this.idx(cc, rr);
          if (this.type[f][j] === WALL) continue;          // a wall stops both
          const cross = door[i] || door[j];
          if (active) smoke[j] = Math.min(1, smoke[j] + 0.22 * this.smokeVentFactor * (cross ? SDOOR : 1) * Math.max(0.4, growth));
          if (!fire[j] && active) {
            frontier = true;
            if (this.door[f][j]) {                         // a doorway has to burn through first
              this.doorHeat[f][j] += 1;                    // +1 "second" of exposure each spread step
              if (this.doorHeat[f][j] >= this.burnThrough) add.push(j);
            } else if (Math.random() < this.params.fireSpread * growth) add.push(j);
          }
        }
      }
      for (const j of add) { fire[j] = 1; smoke[j] = Math.max(smoke[j], 0.8); }
      if (add.length) changed[f] = true;
    }

    // --- smoke diffusion, independent of the flame ---
    // Smoke doesn't wait for fire; it drifts into any patch quieter than itself,
    // slowed (or stopped, if auto-closing) at doors.
    if (active) for (let f = 0; f < F; f++) {
      const smoke = this.smoke[f], door = this.door[f], bump = [];
      for (let i = 0; i < N; i++) {
        const s = smoke[i]; if (s < 0.25) continue;
        const c = i % W, r = (i / W) | 0;
        for (const [dc, dr] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
          const cc = c + dc, rr = r + dr; if (cc < 0 || rr < 0 || cc >= W || rr >= H) continue;
          const j = this.idx(cc, rr); if (this.type[f][j] === WALL) continue;
          const reduce = (door[i] || door[j]) ? (policy === 'auto' ? 0 : 0.55) : 1;
          const target = Math.min(1, (s - 0.12) * reduce);
          if (target > smoke[j]) { bump.push(j); bump.push(target); }
        }
      }
      for (let b = 0; b < bump.length; b += 2) { const j = bump[b], v = bump[b + 1]; if (v > smoke[j]) smoke[j] = v; }
    }

    // --- vertical chimney through the stairwells ---
    if (active) for (let f = 0; f < F; f++) {
      for (let i = 0; i < N; i++) {
        if (this.type[f][i] !== STAIR) continue;
        const hot = this.fire[f][i], sm = this.smoke[f][i];
        if (!hot && sm < 0.3) continue;
        const c = i % W, r = (i / W) | 0;
        for (const nf of [f - 1, f + 1]) {
          if (nf < 0 || nf >= F) continue;
          let t = this.nearestOfType(nf, c, r, 12, STAIR);
          if (t < 0) t = this.nearestPassable(nf, c, r, 4);
          if (t < 0) continue;
          this.smoke[nf][t] = 1;
          if (!this.fire[nf][t] && (hot || Math.random() < 0.12)) { this.fire[nf][t] = 1; changed[nf] = true; frontier = true; }
        }
      }
    }

    this.fireGrowing = frontier;
    for (let f = 0; f < F; f++) if (changed[f]) this.buildFloorField(f);   // fire closed a route — recompute
  }

  // ---- reporters (NetLogo's `to-report`) --------------------------------
  // The one snapshot the UI, the charts, and the CSV export all read.
  metrics() {
    const alive = this.agents.filter(a => a.state <= 1).length;
    return {
      t: (this.rset != null ? this.rset : this.t),   // clearance time (frozen once everyone's accounted for)
      tNow: this.t,                                   // live clock
      population: this.agents.length,
      evacuated: this.evacuated,
      remaining: alive,
      crushDeaths: this.crushDeaths,
      smokeDeaths: this.smokeDeaths,
      totalDeaths: this.crushDeaths + this.smokeDeaths,
      peakDensity: this.peakDensity,
      done: this.done,
      stalled: !!this.stalled,
    };
  }
}

// Run a scenario many times with no rendering and collect the spread of outcomes.
// One run is a single draw from a stochastic model; the distribution is the thing
// you actually report.
function monteCarlo(floors, scenario, reps, cap) {
  reps = reps || 25; cap = cap || 60000;
  const R = { reps, rset: [], deaths: [], evac: [], allEscape: 0, pop: 0 };
  for (let i = 0; i < reps; i++) {
    const s = new EvacSim(floors);
    s.reset(scenario);
    let g = 0; while (!s.done && g++ < cap) s.step();   // run to completion (cap guards against a runaway)
    const m = s.metrics();
    R.rset.push(m.t); R.deaths.push(m.totalDeaths); R.evac.push(m.evacuated); R.pop = m.population;
    if (m.totalDeaths === 0 && m.remaining === 0) R.allEscape++;   // a clean "everyone out" run
  }
  const stat = a => {
    const s = [...a].sort((x, y) => x - y), n = s.length;
    return { mean: a.reduce((p, c) => p + c, 0) / n, min: s[0], max: s[n - 1], p50: s[n >> 1], p90: s[Math.min(n - 1, Math.floor(n * 0.9))] };
  };
  R.rsetStats = stat(R.rset); R.deathStats = stat(R.deaths);
  R.allEscapePct = Math.round(100 * R.allEscape / reps);
  return R;
}

// make the model available both to Node (tests, Monte-Carlo scripts) and the browser
if (typeof module !== 'undefined') module.exports = { EvacSim, DT, CELL_M, monteCarlo };
if (typeof globalThis !== 'undefined') { globalThis.EvacSim = EvacSim; globalThis.monteCarlo = monteCarlo; }
