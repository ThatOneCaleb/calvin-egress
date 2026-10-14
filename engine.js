// ============================================================================
// Multi-floor evacuation engine — standalone, no DOM. Browser + Node.
// 1 cell = 1 m, 1 tick = 0.25 s. Floors: index 0 = bottom (exits), higher = up.
//
//  - Static FLOOR FIELD per floor: BFS from that floor's stairwells (S cells).
//  - People descend the gradient to a stairwell; on upper floors that stairwell
//    drops them to the floor below (a capacity-limited bottleneck); on the
//    bottom floor a stairwell is a building exit.
//  - Weidmann density->speed, one-person-per-cell volume exclusion (queuing),
//    OCEAN personality (speed, reaction, competitive pushing -> crush deaths),
//    optional fire/smoke that blocks routes and is lethal.
// ============================================================================

const DT = 0.25, CELL_M = 1.0, V_FREE = 1.34, STAIR_TICKS = 4;
// demographic mobility groups: free-speed multiplier (Fruin/SFPE) + visual size
const GROUPS = {
  able:     { speed: 1.00, size: 1.00 },
  older:    { speed: 0.72, size: 0.95 },
  child:    { speed: 0.66, size: 0.66 },
  impaired: { speed: 0.42, size: 1.15 },   // assisted / wheelchair
};
const DEFAULT_MIX = { able: 0.82, older: 0.10, child: 0.03, impaired: 0.05 };
function pickGroup(mix) {
  const m = mix || DEFAULT_MIX; let x = Math.random(), acc = 0;
  for (const k of ['able','older','child','impaired']) { acc += m[k]||0; if (x <= acc) return k; }
  return 'able';
}

function clamp01(x) { return Math.max(0, Math.min(1, x)); }
function randn() { let u=0,v=0; while(u===0)u=Math.random(); while(v===0)v=Math.random();
  return Math.sqrt(-2*Math.log(u))*Math.cos(2*Math.PI*v); }

class EvacSim {
  constructor(floors) {
    this.floors = floors;                 // array of floors, each an array of row strings
    this.F = floors.length;
    this.H = floors[0].length;
    this.W = floors[0].reduce((m, r) => Math.max(m, r.length), 0);
    const N = this.W * this.H;
    this.type = [], this.field = [], this.fire = [], this.smoke = [], this.occ = [];
    for (let f = 0; f < this.F; f++) {
      const t = new Uint8Array(N);
      for (let r = 0; r < this.H; r++) {
        const row = floors[f][r];
        for (let c = 0; c < this.W; c++) {
          const ch = c < row.length ? row[c] : 'o';
          t[r*this.W+c] = ch==='.'?1 : ch==='S'?2 : ch==='E'?3 : 0;
        }
      }
      this.type.push(t);
      this.field.push(new Int32Array(N));
      this.fire.push(new Uint8Array(N));
      this.smoke.push(new Float32Array(N));
      this.occ.push(new Int32Array(N).fill(-1));
    }
    // --- rooms & doors inferred from the wall grid (Phase 1) ---
    // A door is a 1-cell navigable pinch-point in a wall line (an opening between two
    // rooms). Fire & smoke are throttled crossing doors, so they spread fast in open
    // rooms and slow at doorways. A room is a connected component of navigable cells.
    this.door = []; this.room = [];
    const nav = (f,i) => { const t=this.type[f][i]; return t===1||t===2||t===3; };
    const sol = (f,c,r) => (c<0||r<0||c>=this.W||r>=this.H) ? true : (this.type[f][r*this.W+c]===0);
    for (let f = 0; f < this.F; f++) {
      const d = new Uint8Array(N);
      for (let r = 0; r < this.H; r++) for (let c = 0; c < this.W; c++) {
        const i = r*this.W+c; if (!nav(f,i)) continue;
        const L=sol(f,c-1,r), R=sol(f,c+1,r), U=sol(f,c,r-1), D=sol(f,c,r+1);
        if ((L&&R&&!U&&!D) || (U&&D&&!L&&!R)) d[i] = 1;   // gap through a wall = doorway
      }
      this.door.push(d);
      const room = new Int32Array(N).fill(-1); let rid = 0;
      for (let s = 0; s < N; s++) {
        if (!nav(f,s) || room[s] !== -1) continue;
        const st=[s]; room[s]=rid;
        while (st.length){ const j=st.pop(), jc=j%this.W;
          for (const off of [-1,1,-this.W,this.W]){ const k=j+off;
            if (off===-1&&jc===0) continue; if (off===1&&jc===this.W-1) continue;
            if (k<0||k>=N||room[k]!==-1||!nav(f,k)) continue; room[k]=rid; st.push(k); } }
        rid++;
      }
      this.room.push(room);
    }
    // precompute which stairwells actually connect to the floor below (static).
    // floor 0 stairs are building exits (always valid); upper stairs are valid
    // only if a walkable cell exists below within DESC_R -> agents never route
    // to a dead-end stair.
    this.DESC_R = 12;
    this.stairOK = [];
    for (let f = 0; f < this.F; f++) {
      const ok = new Uint8Array(N);
      for (let i = 0; i < N; i++) {
        if (this.type[f][i] !== 2) continue;
        if (f === 0) { ok[i] = 1; continue; }
        const c = i%this.W, r = (i/this.W)|0;
        outer:
        for (let rad = 0; rad <= this.DESC_R; rad++)
          for (let dr = -rad; dr <= rad; dr++) for (let dc = -rad; dc <= rad; dc++) {
            if (Math.max(Math.abs(dr),Math.abs(dc)) !== rad) continue;
            const cc=c+dc, rr=r+dr;
            if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue;
            if (this.passable(f-1, this.idx(cc,rr))) { ok[i] = 1; break outer; }
          }
      }
      this.stairOK.push(ok);
    }
    this.reset({});
  }

  idx(c, r) { return r*this.W + c; }
  passable(f, i) { const t=this.type[f][i]; return (t===1||t===2||t===3) && !this.fire[f][i] && !(f===0 && this.blockedExit && this.blockedExit.has(i)); }

  buildField(f) {
    const { W, H } = this, N = W*H, fld = this.field[f];
    fld.fill(-1);
    let frontier = [];
    for (let i = 0; i < N; i++)
      if (this.type[f][i]===2 && !this.fire[f][i] && this.stairOK[f][i] && !(f===0 && this.blockedExit.has(i))) { fld[i]=0; frontier.push(i); }
    const nb = [-1, 1, -W, W];
    while (frontier.length) {
      const next = [];
      for (const i of frontier) {
        const d = fld[i], c = i % W;
        for (const off of nb) {
          if (off===-1 && c===0) continue;
          if (off===1 && c===W-1) continue;
          const j = i + off;
          if (j<0 || j>=N || fld[j]!==-1 || !this.passable(f, j)) continue;
          fld[j] = d+1; next.push(j);
        }
      }
      frontier = next;
    }
  }

  reset(params) {
    const p = Object.assign({ population:200, medianPreMoveS:20, cooperation:0.5,
      vFree:V_FREE, fire:false, fireCell:null, fireSpread:0.25,
      sprinklers:false, doorPolicy:'closed', detectionTime:30, alarmType:'voice',
      blockedExits:0, demographics:null,
      // --- experimental / novel levers (default 0 = no effect) ---
      wardens:0, familiarity:0, signage:0, smartGuidance:0, personalAlert:0, smokeVents:0,
      clutter:0, herding:0, stairPressurized:false, evacElevators:false, phased:false, night:false,
      // human factors that "shouldn't" matter — expose them and let the sim decide
      belongings:0, phone:0, cohesion:0, attire:0, noise:0, urgency:0, handrails:false, ceiling:0, slip:0,
      daylight:0, exitConspicuity:0 }, params);
    this.params = p;
    this.alarmAt = p.detectionTime * (1 - 0.7*p.personalAlert) * (1 + 0.6*p.noise); // alerts speed detection; noise masks alarm
    this.smokeVentFactor = 1 - 0.7*p.smokeVents;                     // vents slow smoke build-up
    this.speedMul = (1 - 0.4*p.clutter) * (1 - 0.2*p.attire) * (1 - 0.15*p.slip);   // clutter / bulky attire / slippery floor
    this.crushMul = (1 + 0.8*p.slip + 0.6*p.urgency) * (p.handrails?0.6:1);         // falls: slip & urgency raise, handrails lower
    this.smokeDoseMul = 1 + 0.6*p.ceiling;                          // low ceilings → smoke reaches head height sooner
    this.wrongTurnMul = Math.max(0, 1 - 0.8*p.signage - 0.9*p.smartGuidance - 0.5*p.familiarity - 0.4*p.daylight - 0.5*p.exitConspicuity);
    this.sprinklerActive = false; this.ignitedAt = null;
    const N = this.W*this.H;
    // doors resist fire for a burn-through time (s): propped-open passes fast, self-closing
    // holds ~45 s, fire-rated/auto holds ~10 min (effectively blocks for a normal run)
    this.doorHeat = this.type.map(()=>new Float32Array(N));
    this.burnThrough = ({open:3, closed:45, auto:600})[p.doorPolicy] ?? 45;
    // egress lever: lock (block) some ground-floor exits — people funnel to the rest
    this.blockedExit = new Set();
    if (p.blockedExits > 0) {
      const ex = []; for (let i=0;i<N;i++) if (this.type[0][i]===2) ex.push(i);
      for (let k=ex.length-1;k>0;k--){ const j=(Math.random()*(k+1))|0; [ex[k],ex[j]]=[ex[j],ex[k]]; }
      for (let k=0;k<Math.min(p.blockedExits, ex.length-1);k++) this.blockedExit.add(ex[k]);  // always leave ≥1 open
    }
    for (let f = 0; f < this.F; f++) {
      this.fire[f].fill(0); this.smoke[f].fill(0); this.occ[f].fill(-1);
      this.buildField(f);
    }
    // spawn candidates per floor, weighted by walkable area
    const cand = [], walk = [];
    let sum = 0;
    for (let f = 0; f < this.F; f++) {
      const list = [];
      for (let i = 0; i < N; i++)
        if ((this.type[f][i]===1||this.type[f][i]===3) && this.field[f][i]>0) list.push(i);
      for (let k = list.length-1; k>0; k--) { const j=(Math.random()*(k+1))|0; [list[k],list[j]]=[list[j],list[k]]; }
      cand.push(list); walk.push(list.length); sum += list.length;
    }
    this.agents = [];
    for (let f = 0; f < this.F; f++) {
      const n = Math.min(cand[f].length, Math.round(p.population * walk[f] / sum));
      for (let k = 0; k < n; k++) {
        const i = cand[f][k];
        const a = this.makeAgent(f, i%this.W, (i/this.W)|0, p);
        this.occ[f][i] = this.agents.length; this.agents.push(a);
      }
    }
    this.hasFire = false; this.fireFloor = null;
    if (p.fire) this.ignite(p.fireCell);
    this.t = 0; this.evacuated = 0; this.crushDeaths = 0; this.smokeDeaths = 0;
    this.peakDensity = 0; this.done = false; this.rset = null; this.fireGrowing = this.hasFire;
    this._stall = 0; this._lastProg = 0; this.stalled = false;
  }

  makeAgent(f, c, r, p) {
    const E = clamp01(0.5+0.15*randn()), C = clamp01(0.5+0.15*randn());
    const A = clamp01(p.cooperation+0.15*randn()), N = clamp01(0.5+0.15*randn());
    const composure = 1-N, assertiveness = 0.5*E+0.5*(1-A), awareness = C;
    const fitness = clamp01(0.6+0.15*randn());
    const gk = pickGroup(p.demographics), G = GROUPS[gk];   // demographic mobility group
    const v = (p.vFree+0.26*randn())*(0.9+0.15*fitness+0.05*assertiveness)*G.speed;
    const alarmF = (p.alarmType==='bell') ? 1.0 : 0.62;   // voice-evac cuts pre-movement (SFPE)
    let preMove = Math.max(0, p.medianPreMoveS*alarmF*(1-0.5*awareness)*Math.exp(0.5*randn()));
    const warden = Math.random() < (p.wardens||0);
    if (warden) preMove *= 0.1;                       // trained wardens move at once
    preMove *= (1 - 0.5*(p.wardens||0));              // wardens get everyone else moving (leadership)
    preMove *= (1 - 0.4*(p.familiarity||0));          // drills → faster reaction
    if (p.night) preMove *= 3;                         // sleeping occupants react slowly
    preMove += (p.belongings||0)*40*Math.random();     // stopping to grab belongings
    preMove *= (1 + 0.5*(p.phone||0));                 // phone distraction delays noticing
    preMove *= (1 + 0.3*(p.cohesion||0));              // waiting for your group
    preMove *= (1 - 0.3*(p.urgency||0));               // urgent alarm tone → move sooner
    return { floor:f, c, r, cell:this.idx(c,r), composure, assertiveness, altruism:A,
      awareness, group:gk, gsize:G.size, warden, herding:(p.herding||0),
      vComfort:Math.max(0.35,Math.min(2.0,v)), preMove, budget:0, dose:0,
      onStair:false, stairT:0, state:0 };
  }

  // light a small visible patch (a fire isn't a single 1 m cell), not just one cell
  seedFire(f, i) {
    if (i<0) return false;
    const c=i%this.W, r=(i/this.W)|0, cells=[i];
    for (const [dc,dr] of [[-1,0],[1,0],[0,-1],[0,1]]) { const cc=c+dc, rr=r+dr;
      if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue; const j=this.idx(cc,rr); const t=this.type[f][j];
      if (t===1||t===3) cells.push(j); }
    for (const j of cells) { this.fire[f][j]=1; this.smoke[f][j]=1; }
    this.fireFloor=f; this.hasFire=true; this.fireGrowing=true; if(this.ignitedAt==null)this.ignitedAt=this.t; this.buildField(f); return true;
  }
  ignite(cell) {
    let f, i;
    if (cell) { f = cell[2]||0; i = this.idx(cell[0], cell[1]); }
    else { f = 0; i = this.nearestPassable(0, this.W>>1, this.H>>1, 60); }  // ignite centrally
    this.seedFire(f, i);
  }
  placeFire(f, c, r) {   // click-to-place; returns true if placed
    const i = this.idx(c, r);
    if (this.type[f][i] !== 1 && this.type[f][i] !== 3) return false;
    return this.seedFire(f, i);
  }

  localDensity(f, c, r) {
    let occ=0, cells=0;
    for (let dr=-1; dr<=1; dr++) for (let dc=-1; dc<=1; dc++) {
      if (!dc && !dr) continue;
      const cc=c+dc, rr=r+dr;
      if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue;
      const j=this.idx(cc,rr);
      if (this.type[f][j]===0) continue;
      cells++; if (this.occ[f][j]>=0) occ++;
    }
    return cells ? occ/cells : 0;
  }

  bestNeighbor(a) {
    const f=a.floor, fld=this.field[f], d0=fld[a.cell];
    let best=-1, bd=d0;
    for (const [dc,dr] of [[-1,0],[1,0],[0,-1],[0,1]]) {
      const cc=a.c+dc, rr=a.r+dr;
      if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue;
      const j=this.idx(cc,rr);
      if (!this.passable(f,j) || fld[j]===-1) continue;
      const exit = (this.type[f][j]===2 && f===0);
      if (!exit && this.occ[f][j]>=0) continue;   // occupied (bottom-floor exits absorb)
      if (fld[j] < bd) { bd=fld[j]; best=j; }
    }
    return best;
  }

  // a disoriented step (used in thick smoke): any free passable neighbour, not the best
  randomStep(a) {
    const f=a.floor, opts=[];
    for (const [dc,dr] of [[-1,0],[1,0],[0,-1],[0,1]]) {
      const cc=a.c+dc, rr=a.r+dr;
      if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue;
      const j=this.idx(cc,rr);
      if (!this.passable(f,j) || this.field[f][j]===-1) continue;
      const exit = (this.type[f][j]===2 && f===0);
      if (!exit && this.occ[f][j]>=0) continue;
      opts.push(j);
    }
    return opts.length ? opts[(Math.random()*opts.length)|0] : -1;
  }

  // "follow the crowd": step toward the free neighbour with the most occupied surroundings
  herdStep(a) {
    const f=a.floor; let best=-1, bo=-1;
    for (const [dc,dr] of [[-1,0],[1,0],[0,-1],[0,1]]) {
      const cc=a.c+dc, rr=a.r+dr; if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue;
      const j=this.idx(cc,rr); if (!this.passable(f,j) || this.field[f][j]===-1) continue;
      const exit = (this.type[f][j]===2 && f===0);
      if (!exit && this.occ[f][j]>=0) continue;
      let occ=0; const jc=j%this.W, jr=(j/this.W)|0;
      for (const [q,w] of [[-1,0],[1,0],[0,-1],[0,1]]) { const xc=jc+q, xr=jr+w;
        if (xc<0||xr<0||xc>=this.W||xr>=this.H) continue; if (this.occ[f][this.idx(xc,xr)]>=0) occ++; }
      if (occ>bo) { bo=occ; best=j; }
    }
    return best!==-1 ? best : this.bestNeighbor(a);
  }

  descend(k) {
    const a = this.agents[k], f = a.floor-1;
    for (let rad=0; rad<=this.DESC_R; rad++) {
      for (let dr=-rad; dr<=rad; dr++) for (let dc=-rad; dc<=rad; dc++) {
        if (Math.max(Math.abs(dr),Math.abs(dc))!==rad) continue;
        const cc=a.c+dc, rr=a.r+dr;
        if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue;
        const j=this.idx(cc,rr);
        const landExit = (this.type[f][j]===2 && f===0);
        if (this.passable(f,j) && this.field[f][j]>=0 && (landExit || this.occ[f][j]<0)) {
          this.occ[a.floor][a.cell] = -1;               // leave the stair above
          a.floor=f; a.c=cc; a.r=rr; a.cell=j; a.budget=0; a.onStair=false;
          if (this.type[f][j]===2) {
            if (f===0) { a.state=2; this.evacuated++; }        // landed at a ground exit
            else { this.occ[f][j]=k; a.onStair=true; a.stairT=STAIR_TICKS; } // keep descending
          } else this.occ[f][j]=k;
          return true;
        }
      }
    }
    return false;
  }

  step() {
    if (this.done) return;
    this.t += DT;
    if (this.hasFire && Math.round(this.t/DT)%4===0) this.spreadStep();

    const order = this.agents.map((a,k)=>k).filter(k=>this.agents[k].state<=1)
      .sort((k1,k2)=>this.field[this.agents[k1].floor][this.agents[k1].cell]
                   - this.field[this.agents[k2].floor][this.agents[k2].cell]);

    for (const k of order) {
      const a = this.agents[k], f = a.floor;
      if (a.state===0) { const gate=this.alarmAt+(this.params.phased?a.floor*15:0);   // phased evac staggers upper floors
        if (this.t < gate) continue;
        a.preMove-=DT; if (a.preMove<=0) a.state=1; else continue; }

      // safety: anyone standing on a ground-floor exit leaves
      if (f===0 && this.type[0][a.cell]===2) { this.occ[0][a.cell]=-1; a.state=2; this.evacuated++; continue; }

      if (this.hasFire) {
        const onStair = this.type[f][a.cell]===2, protectedStair = this.params.stairPressurized && onStair;
        const s = protectedStair ? 0 : this.smoke[f][a.cell];   // pressurized stairwells stay tenable
        if (s>0.4) a.dose += (s-0.4)*DT*this.smokeDoseMul;   // FED: appreciable smoke incapacitates (low ceiling faster)
        if ((this.fire[f][a.cell] && !protectedStair) || a.dose>3.0) { this.killAgent(k,4); continue; }
      }

      if (a.onStair) {                          // descending: capacity bottleneck
        if (--a.stairT<=0) { if (!this.descend(k)) a.stairT=1; }
        continue;
      }

      const dens = this.localDensity(f,a.c,a.r);
      if (dens>this.peakDensity) this.peakDensity=dens;
      if (dens>=0.8) {
        const push=a.assertiveness*(1-a.altruism);
        if (Math.random()<0.0010*push*this.crushMul) { this.killAgent(k,3); continue; }
      }

      const smokeHere = this.hasFire ? this.smoke[f][a.cell] : 0;
      const vis = Math.max(0.2, 1 - 0.7*smokeHere);       // smoke cuts visibility → slower
      a.budget += a.vComfort*Math.max(0.15,1-0.85*dens)*vis*this.speedMul*DT;
      if (a.budget<CELL_M) continue;
      let dest;
      if (smokeHere>0.35 && Math.random()<0.3*smokeHere*this.wrongTurnMul) dest=this.randomStep(a);   // disoriented in smoke (signage/guidance reduce)
      else if (a.herding>0 && Math.random()<0.22*a.herding) dest=this.herdStep(a);                    // follow the crowd
      else dest=this.bestNeighbor(a);
      if (dest===-1) { a.stuck=(a.stuck||0)+1; if (a.stuck>40) dest=this.randomStep(a); } // break standoffs
      if (dest===-1) { a.budget=CELL_M; continue; }
      a.stuck=0;
      this.occ[f][a.cell]=-1;
      a.cell=dest; a.c=dest%this.W; a.r=(dest/this.W)|0; a.budget-=CELL_M;
      if (this.type[f][dest]===2) {
        if (f===0) { a.state=2; this.evacuated++; }        // bottom-floor exit
        else { this.occ[f][dest]=k; a.onStair=true; a.stairT=(this.params.evacElevators && a.group==='impaired')?1:STAIR_TICKS; } // enter stair (evac elevators speed the impaired)
      } else this.occ[f][dest]=k;
    }
    const active = this.agents.some(a=>a.state<=1);
    if (!active && this.rset==null) this.rset = this.t;             // freeze clearance time (RSET)
    this.done = !active && !(this.hasFire && this.fireGrowing);     // keep running while fire still spreads
    // stall guard: if nothing changes for ~60 s and people remain, end (they're trapped)
    const prog = this.evacuated + this.crushDeaths + this.smokeDeaths;
    if (prog === this._lastProg) this._stall++; else { this._stall = 0; this._lastProg = prog; }
    if (!this.done && active && !this.fireGrowing && this._stall > 240) { this.done = true; this.stalled = true; if (this.rset==null) this.rset=this.t; }
  }

  killAgent(k, state) {
    const a=this.agents[k]; a.state=state; this.occ[a.floor][a.cell]=-1;
    if (state===3) this.crushDeaths++; else this.smokeDeaths++;
  }

  nearestPassable(f, c, r, R) { return this.nearestOfType(f, c, r, R, null); }
  // nearest cell of a given type (or any walkable if want===null) within radius R
  nearestOfType(f, c, r, R, want) {
    for (let rad=0; rad<=R; rad++)
      for (let dr=-rad; dr<=rad; dr++) for (let dc=-rad; dc<=rad; dc++) {
        if (Math.max(Math.abs(dr),Math.abs(dc))!==rad) continue;
        const cc=c+dc, rr=r+dr;
        if (cc<0||rr<0||cc>=this.W||rr>=this.H) continue;
        const t=this.type[f][this.idx(cc,rr)];
        if (want===null ? (t===1||t===2||t===3) : t===want) return this.idx(cc,rr);
      }
    return -1;
  }

  // one spread step across ALL floors: within-floor + vertical "chimney"
  // (fire/smoke at a stairwell seeds the aligned stair on the floors above/below)
  spreadStep() {
    const { W, H, F } = this, N = W*H;
    const policy = this.params.doorPolicy || 'closed';
    const FDOOR = ({open:0.60, closed:0.10, auto:0.0})[policy] ?? 0.10;  // flame crossing a doorway
    const SDOOR = ({open:0.90, closed:0.45, auto:0.0})[policy] ?? 0.45;  // smoke crossing a doorway
    // t²-style growth: fire is small/slow when young, ramps toward fully-developed
    const growth = Math.max(0.25, Math.min(1, (this.t - (this.ignitedAt||0)) / 90));
    // sprinklers activate once the fire reaches a size, then cap growth (extends ASET)
    if (this.params.sprinklers && !this.sprinklerActive) {
      let burning=0; for (let f=0;f<F;f++){ const fr=this.fire[f]; for (let i=0;i<N;i++) if(fr[i]) burning++; }
      if (burning >= 14) this.sprinklerActive = true;
    }
    const active = !this.sprinklerActive;   // fire still allowed to grow?
    const changed = new Array(F).fill(false);
    let frontier = false;
    for (let f = 0; f < F; f++) {
      const fire=this.fire[f], smoke=this.smoke[f], door=this.door[f], add=[];
      for (let i = 0; i < N; i++) {
        if (!fire[i]) continue;
        const c=i%W, r=(i/W)|0;
        for (const [dc,dr] of [[-1,0],[1,0],[0,-1],[0,1]]) {
          const cc=c+dc, rr=r+dr; if (cc<0||rr<0||cc>=W||rr>=H) continue;
          const j=this.idx(cc,rr); if (this.type[f][j]===0) continue;   // wall blocks both
          const cross = door[i]||door[j];
          if (active) smoke[j]=Math.min(1, smoke[j] + 0.22*this.smokeVentFactor*(cross?SDOOR:1)*Math.max(0.4,growth));
          if (!fire[j] && active) { frontier = true;
            if (this.door[f][j]) {                          // a doorway resists — fire must burn through
              this.doorHeat[f][j] += 1;                     // +1 s of exposure per spread step
              if (this.doorHeat[f][j] >= this.burnThrough) add.push(j);
            } else if (Math.random() < this.params.fireSpread * growth) add.push(j);
          }
        }
      }
      for (const j of add){ fire[j]=1; smoke[j]=Math.max(smoke[j],0.8); }
      if (add.length) changed[f]=true;
    }
    // independent smoke diffusion — smoke outruns the flame down corridors & through doors
    if (active) for (let f=0; f<F; f++){
      const smoke=this.smoke[f], door=this.door[f], bump=[];
      for (let i=0;i<N;i++){ const s=smoke[i]; if (s<0.25) continue; const c=i%W,r=(i/W)|0;
        for (const [dc,dr] of [[-1,0],[1,0],[0,-1],[0,1]]){ const cc=c+dc,rr=r+dr; if(cc<0||rr<0||cc>=W||rr>=H)continue;
          const j=this.idx(cc,rr); if(this.type[f][j]===0) continue;
          const red=(door[i]||door[j]) ? (policy==='auto'?0:0.55) : 1;   // doors slow/stop smoke
          const target=Math.min(1,(s-0.12)*red);
          if (target>smoke[j]) { bump.push(j); bump.push(target); } } }
      for (let b=0;b<bump.length;b+=2){ const j=bump[b], v=bump[b+1]; if (v>smoke[j]) smoke[j]=v; }
    }
    // vertical chimney through stairwells (respects sprinkler control)
    if (active) for (let f = 0; f < F; f++) {
      for (let i = 0; i < N; i++) {
        if (this.type[f][i]!==2) continue;
        const hot=this.fire[f][i], sm=this.smoke[f][i];
        if (!hot && sm<0.3) continue;
        const c=i%W, r=(i/W)|0;
        for (const nf of [f-1, f+1]) {
          if (nf<0||nf>=F) continue;
          let t=this.nearestOfType(nf, c, r, 12, 2); if (t<0) t=this.nearestPassable(nf, c, r, 4); if (t<0) continue;
          this.smoke[nf][t]=1;
          if (!this.fire[nf][t] && (hot || Math.random()<0.12)) { this.fire[nf][t]=1; changed[nf]=true; frontier=true; }
        }
      }
    }
    this.fireGrowing = frontier;
    for (let f=0; f<F; f++) if (changed[f]) this.buildField(f);
  }

  metrics() {
    const alive = this.agents.filter(a=>a.state<=1).length;
    return { t:(this.rset!=null?this.rset:this.t), tNow:this.t, population:this.agents.length, evacuated:this.evacuated,
      remaining:alive, crushDeaths:this.crushDeaths, smokeDeaths:this.smokeDeaths,
      totalDeaths:this.crushDeaths+this.smokeDeaths, peakDensity:this.peakDensity, done:this.done, stalled:!!this.stalled };
  }
}

// Monte-Carlo: run a scenario many times headless → a distribution of outcomes (defensible results)
function monteCarlo(floors, scenario, reps, cap) {
  reps = reps||25; cap = cap||60000;
  const R = { reps, rset:[], deaths:[], evac:[], allEscape:0, pop:0 };
  for (let i=0;i<reps;i++){
    const s = new EvacSim(floors); s.reset(scenario);
    let g=0; while(!s.done && g++<cap) s.step();
    const m = s.metrics();
    R.rset.push(m.t); R.deaths.push(m.totalDeaths); R.evac.push(m.evacuated); R.pop=m.population;
    if (m.totalDeaths===0 && m.remaining===0) R.allEscape++;
  }
  const stat = a => { const s=[...a].sort((x,y)=>x-y), n=s.length;
    return { mean:a.reduce((p,c)=>p+c,0)/n, min:s[0], max:s[n-1], p50:s[n>>1], p90:s[Math.min(n-1,Math.floor(n*0.9))] }; };
  R.rsetStats = stat(R.rset); R.deathStats = stat(R.deaths);
  R.allEscapePct = Math.round(100*R.allEscape/reps);
  return R;
}

if (typeof module !== 'undefined') module.exports = { EvacSim, DT, CELL_M, monteCarlo };
if (typeof globalThis!=="undefined") { globalThis.EvacSim = EvacSim; globalThis.monteCarlo = monteCarlo; }
