# Calvin Egress

A browser-based, performance-based building fire evacuation simulator for Calvin
University safety planning. Occupants are individual agents; fire and smoke spread
on real building geometry; the model compares required vs available safe egress
time (RSET vs ASET).

## Run locally

Static site — serve over HTTP (the 3D view loads ES modules):

```
python3 -m http.server 8030
```

Then open <http://localhost:8030/>.

## Pages

- `index.html` — overview
- `simulator.html` — real-time 3D simulator (exports each run to CSV)
- `methodology.html`, `validation.html`, `about.html`, `credits.html`

## Code

- `engine.js` — simulation core (no DOM, Node-testable): floor-field routing,
  demographic movement, OCEAN behavior, doors/rooms, t² fire + sprinklers + smoke
  + FED, RSET timeline, `monteCarlo()`.
- `buildings.js`, `campus-data.js`, `hekman-floor.js` — geometry and loaders.
- `assets/` — styles, scripts, preview image.

## Scope

A comparative planning tool (ASET vs RSET), not a certified CFD fire calculation.
See `validation.html` for the model's limits and validation status.

Built by Caleb Steele, Calvin University.
