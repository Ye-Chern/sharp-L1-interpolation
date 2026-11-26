# Research Agent Guidance

Read [`paper.tex`](paper.tex), [`README.md`](README.md), and [`FORMALIZATION.md`](FORMALIZATION.md) before changing the mathematics or formalization. The Lean entry point for Theorem 1 is `SharpL1.Analysis.theorem_sharp_L1_interpolation_full` in [`Lean/SharpL1/Analysis/MainTheorem.lean`](Lean/SharpL1/Analysis/MainTheorem.lean), audited in [`Lean/Audit.lean`](Lean/Audit.lean).

## Proof Architecture & Formalization Scope

- **Center maximality**: orders $n = 1, 2$ use explicit closed-form formulas; order $n = 3$ uses the five kernel-checked fixed-point quadrature blocks (`by decide`) in `Lean/SharpL1/Analysis/LowOrderMono.lean`; orders $n \ge 4$ use the analytic vertical-chord estimate in `Lean/SharpL1/Analysis/ChordBoundsN4.lean`.
- **Sobolev theorem (`SobolevW1`)**: `Lean/SharpL1/Analysis/MovingOperator.lean` formalizes the one-dimensional Sobolev space $W^{n+1,1}[-1,1]$ via continuous derivatives through order $n$, integrable $(n+1)$-th derivative, and adjacent Fundamental Theorem of Calculus identities.
- **Verification**: from `Lean/`, run `lake build` and `lake env lean Audit.lean` to verify proof changes (never run concurrent `lake build` across processes sharing `.lake/build`; keep build output isolated across worktrees). Inspect `#print axioms` for new top-level theorems, verify only the standard Lean axioms `[propext, Classical.choice, Quot.sound]` appear, and report exactly what was checked.

## Maintenance & Repository Hygiene

- Keep the manuscript (`paper.tex` / `paper.pdf`), Lean statements, `FORMALIZATION.md`, `README.md`, and `Lean/Audit.lean` synchronized whenever statements or assumptions change.
- **Preserve historical records**: keep historical drafts (`notes/origin-second-order-zh.tex`, `notes/working-note-v0.1.tex`, `notes/paper-v0.2-zh.tex`, `notes/chebyshev_L1_complete_zh.tex`), superseded `certificates/`, `notes/phase-a.md`, `notes/phase-b.md`, and archived `notes/tasks/` clearly separated from final verified artifacts; do not delete them or silently overwrite history.
- **No external copyrighted PDFs**: never copy copyrighted reference PDFs or full external articles into the repository.
- **No secrets**: never commit tokens, credentials, or local machine paths into tracked files.
- **Authority**: the human maintainer decides scientific novelty claims, formal authorship, attribution, licensing, and publication.
