# SATviz — CDCL & DPLL SAT solvers, animated

Two SAT solvers in dependency-free Java, packaged as a runnable JAR —
**plus a Swing visualizer that animates how each one thinks**:

- **CDCL** (conflict-driven clause learning) as an animated **implication
  graph** — decisions on top, propagations layered below their reasons on
  clause-colored edges, conflicts pulsing rose, resolution assembling the
  learned clause, backjumps sweeping as dashed amber arrows.
- **DPLL** (classic Davis–Putnam) as an animated **search tree** — branch
  nodes for each True/False decision, leaves marked SAT or UNSAT, dead
  subtrees in rose, the current path glowing amber.

## Run

```bash
java -jar satviz.jar                 # the visualizer (pick CDCL or DPLL in the toolbar)
java -jar satviz.jar --test          # self-tests (both engines)
java -jar satviz.jar --solve f.cnf   # headless CDCL solve, DIMACS exit codes (10/20)
java -jar satviz.jar --render DIR    # export demo frames as PNG (no display needed)
```

Rebuild from source:

```bash
javac -d build src/satviz/*.java
jar --create --main-class satviz.SatViz --file satviz.jar -C build .
```

## The visualizer

- **Algorithm switch** — choose *CDCL (implication graph)* or
  *DPLL (search tree)* from the toolbar; any loaded formula re-solves and
  re-animates with the chosen engine.
- **Implication graph (CDCL)** — nodes are assignments layered top-down by
  implication depth; edges point from a literal to the variable its reason
  clause forced, labeled `c<id>`. Decisions are amber, conflicts halo
  rose, the learned clause's UIP gets a violet ring.
- **Search tree (DPLL)** — each branch node is a decision literal
  (`x1` / `¬x1`); children hang below; leaves are stamped SAT (emerald) or
  UNSAT (rose); the root-to-current path glows amber; the current
  assignment strip shows the partial model.
- **Time travel** — `←`/`→` step, `space` plays, `r` restarts, the scrubber
  jumps anywhere. Every step snapshots the full state.
- **Side panels** — step explanation with didactic notes; learned-clause DB
  (CDCL) or dead/solved branches (DPLL); the assignment trail.
- **Presets & files** — implication chain, 2-var diamond, PHP(3,2), random
  3-SAT, or any DIMACS file.
- **Pan & zoom** — drag to pan, wheel to zoom, click to re-center.

## The solvers

**CDCL (`satviz.Solver`)**

| Component | Technique |
|---|---|
| Propagation | Two-watched-literal scheme (lazy BCP) |
| Conflict analysis | 1UIP clause learning (MiniSat-style do-while) |
| Clause strength | Self-subsumption minimization |
| Backtracking | Non-chronological backjumping |
| Branching | VSIDS activity (geometric decay) + phase saving |
| Restarts | Luby sequence (1,1,2,1,1,2,4,…) |
| Clause DB | LBD-based reduction; glue clauses (LBD ≤ 2) kept forever |

**DPLL (`satviz.DpllSolver`)**

| Component | Technique |
|---|---|
| Branching | Chronological True-then-False on the lowest-index var |
| Pruning | Unit propagation |
| Pruning | Pure-literal elimination |
| Backtracking | Chronological with clause-DB restore per branch |
| Recording | Full search-tree snapshot per event |

Both engines work on **any DIMACS input**: tautologies and duplicate
literals are handled, contradictory units are detected as trivially
UNSAT, and multi-clause lines / missing headers don't break parsing.

## Correctness

`satviz.Test` validates (all through the same JAR):

- **CDCL**: 36 random 3-SAT instances match brute force; PHP(8,7) UNSAT;
  N-Queens n = 4…9 SAT with verified models; determinism.
- **DPLL**: 36 random 3-SAT instances match brute force; PHP(5,4) UNSAT;
  N-Queens n = 4…7 SAT; every SAT model verified against every clause.

## Files

```
src/satviz/
  Solver.java     CDCL engine + trace recording
  DpllSolver.java DPLL engine + search-tree snapshots
  Trace.java      immutable step snapshots
  Test.java       self-tests (both engines)
  GraphView.java  implication-graph + search-tree renderers (shared GUI/headless)
  SatViz.java     Swing app, presets, DIMACS loading, CLI
  Render.java     headless PNG frame export
```

