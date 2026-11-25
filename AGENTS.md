# Research agent guidance

Read paper.tex, README.md and FORMALIZATION.md before changing mathematics. The v0.2 draft proposes a computer-assisted proof; independent review and Lean formalization remain open. Prioritize auditing the proof and certificate bridge over improving the threshold 20. Do not conflate integer certificate checks with the full real-variable or Sobolev theorem. Keep the paper, code and statements synchronized. Track sorry and custom axioms explicitly; report actual compiled results and gaps. Preserve historical notes. Do not make novelty, attribution or licensing decisions on behalf of the maintainer.

Read [the Phase A map](notes/phase-a.md) for the current dependency to work on. Record accepted evidence and open mathematical assumptions with the relevant issue and PR. Build and inspect the axioms of any new Lean theorem. Keep project build output separate between worktrees.
