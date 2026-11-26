# Research agent guidance

Read [the current manuscript](chebyshev_L1_complete.tex), [README](README.md), and [the formalization map](FORMALIZATION.md) before changing the mathematics. The Lean entry point for Theorem 1 is `SharpL1.Analysis.theorem_sharp_L1_interpolation_full` in [`MainTheorem.lean`](Lean/SharpL1/Analysis/MainTheorem.lean).

For center maximality, orders 1 and 2 use explicit formulas. Order 3 uses the five kernel-checked quadrature blocks in `LowOrderMono.lean`. Orders at least 4 use the analytic vertical-chord estimate in `ChordBoundsN4.lean`. The Sobolev theorem uses the one-dimensional integral representation in `MovingOperator.lean`. Record which statement and hypotheses each change affects.

From `Lean/`, run `lake build` and `lake env lean Audit.lean` to verify proof changes. Keep the manuscript, definitions, statements, and audit synchronized. Inspect the axioms of new main results, report exactly what was checked, and record accepted evidence and open assumptions in the relevant issue or pull request. Keep project build output separate between worktrees. The maintainer decides novelty, attribution, licensing, and publication.

[`paper.tex`](paper.tex), the older bracket certificates, the [Phase A](notes/phase-a.md) and [Phase B](notes/phase-b.md) notes, and the [task cards](notes/tasks/START.md) record the historical v0.2 proof route with cutoff 20. Use the current manuscript and formalization map for follow-up work on Theorem 1.
