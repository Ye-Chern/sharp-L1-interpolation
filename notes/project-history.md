# Project History & Discovery Record

This note preserves the authentic development arc and collaboration history of the `sharp-L1-interpolation` project so that historical drafts and exploratory branches remain traceable while staying clearly separated from the final verified artifacts ([`paper.tex`](../paper.tex), [`paper.pdf`](../paper.pdf), [`Lean/SharpL1/Analysis/MainTheorem.lean`](../Lean/SharpL1/Analysis/MainTheorem.lean), [`Lean/Audit.lean`](../Lean/Audit.lean), and [`certify_chebyshev_L1.py`](../certify_chebyshev_L1.py)).

## 1. Chronological Discovery & Proof Evolution

1. **Second-order origin (`2026-11-20`, [`notes/origin-second-order-zh.tex`](origin-second-order-zh.tex))**
   - Starting from a concrete second-order finite-interval inequality on $[0, 1]$,
     $$\|f''\|_{L^1[0,1]} \le 32\,\|f\|_{L^1[0,1]} + \frac{2\sqrt{2}-1}{6}\,\|f'''\|_{L^1[0,1]}$$
     (equivalently $\|F''\|_{L^1[-1,1]} \le 8\,\|F\|_{L^1[-1,1]} + \frac{2\sqrt{2}-1}{3}\,\|F'''\|_{L^1[-1,1]}$), Lijails and GPT 6.2 Astra (with Qwen3.8-flash writing assistance) identified the extremal polynomial structure and the optimal moving-node reduction for $n = 2$.

2. **All-order formulation & working note v0.1 (`2026-11-25`, [`notes/working-note-v0.1.tex`](working-note-v0.1.tex))**
   - Generalized the moving-node divided-difference operator to all integers $n \ge 1$ using roots of the second-kind Chebyshev polynomial $U_n$ shifted by $t \in (-1, 1)$.
   - Proved the sharp first constant $A_n = 2^n n!$ and reduced the lexicographically minimal second constant $B_n$ to $\max_{t \in [-1,1]} E_n(t)$.
   - Connected the moving nodes simultaneously to Jacobi matrices, Chebyshev polynomials, and generalized Gauss quadrature; introduced the probabilistic/B-spline representation and local limit theorem, yielding an unoptimized asymptotic threshold $n \ge 10^{40}$ while leaving the all-orders center-maximum conjecture ($B_n = E_n(0)$) explicitly open.

3. **v0.2 draft & threshold-$20$ finite certificates (`2026-11-25`, [`notes/paper-v0.2-zh.tex`](paper-v0.2-zh.tex), [`certificates/`](../certificates/), [`notes/phase-a.md`](phase-a.md), [`notes/phase-b.md`](phase-b.md), [`notes/tasks/`](tasks/START.md))**
   - Tightened the analytic center-maximum threshold to $n \ge 20$ and bridged the remaining low orders $3 \le n \le 19$ using exact rational-interval CSV bracket certificates verified by [`certificates/check.py`](../certificates/check.py) and [`certificates/check_constants.py`](../certificates/check_constants.py).
   - Initiated the Lean 4 formalization around this v0.2 architecture (see `notes/phase-a.md`, `notes/phase-b.md`, and `notes/tasks/START.md`), merged foundational algebraic/Jacobi infrastructure in PR #5 (`research/phase-a-foundations` $\to$ `main`), and tested multi-model decomposition workflows documented in [`notes/team-calibration.md`](team-calibration.md).

4. **Threshold-$4$ vertical-chord breakthrough (`2026-11-26`, [`notes/chebyshev_L1_complete_zh.tex`](chebyshev_L1_complete_zh.tex), [`certify_chebyshev_L1.py`](../certify_chebyshev_L1.py))**
   - Introducing the vertical-chord contour comparison cut the analytic threshold down from $n \ge 20$ to **$n \ge 4$** for all $t \in (0, 1/2]$ (alongside the boundary proof for $t \in [1/2, 1)$).
   - Closed-form estimates handled $n = 1, 2$, while $n = 3$ required only a 5-subinterval rigorous interval-arithmetic enclosure in Python (`mpmath.iv`, [`certify_chebyshev_L1.py`](../certify_chebyshev_L1.py)) — or in Lean, pure-kernel fixed-point integer quadrature.

5. **Complete unconditional Lean 4 formalization (`2026-11-26`, PR #7, `Lean/`)**
   - Formalized the entire proof in Lean `v4.32.2` + Mathlib (`SharpL1.Analysis.theorem_sharp_L1_interpolation_full` in [`Lean/SharpL1/Analysis/MainTheorem.lean`](../Lean/SharpL1/Analysis/MainTheorem.lean)), avoiding external Python/interval-arithmetic dependencies inside the proof kernel:
     - $n \ge 4$ proved via `Complex.log` / FTC on the vertical chord (`ChordBoundsN4.lean`),
     - $n = 3$ proved via 5 pure-kernel fixed-point integer quadrature blocks checked by `by decide` (`LowOrderMono.lean`),
     - 1D Sobolev space $W^{n+1,1}[-1,1]$ formalized via `SobolevW1` (iterated continuous derivatives and adjacent FTC identities in `MovingOperator.lean`).
   - Verified in [`Lean/Audit.lean`](../Lean/Audit.lean) with only the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

6. **Literature audit & English publication draft (`2026-11-26`, PR #8, [`notes/literature.md`](literature.md), [`notes/structural-observations.md`](structural-observations.md), [`paper.tex`](../paper.tex))**
   - An explicit literature check uncovered V. I. Burenkov (1980), *Exact constants in inequalities for the norms of intermediate derivatives on a finite interval* (*Proc. Steklov Inst. Math.* 156, 1983; Russian original 1980, pp. 22–29), which already characterized the sharp constants $A_n, B_n$ in §4° (eqs. (24)–(25)) on $[-1, 1]$ and explicitly noted (p. 29) that obtaining a closed-form $L^1$ counterpart to his explicit $L^\infty$ evaluation remained open.
   - Accordingly, [`paper.tex`](../paper.tex) presents the results as an independent rediscovery of the extremal characterization combined with—to the best of our knowledge—the first explicit closed-form evaluation $B_n = E_n(0)$ resolving Burenkov's 1980 $L^1$ question, together with the moving Chebyshev / Jacobi / generalized Gauss quadrature viewpoint and a complete Lean 4 proof.

## 2. Contributors & AI Collaboration Record

The work evolved through sustained human–AI and multi-agent collaboration:

- **Lijails** — Project initiator and human maintainer; posed the original second-order problem, guided the mathematical direction, and directed verification, literature review, and repository curation.
- **GPT 6.2 Astra** — Collaborated on the initial second-order derivation (`2026-11-20`, [`notes/origin-second-order-zh.tex`](origin-second-order-zh.tex)).
- **GPT 6.2 Sol** — Collaborated on the all-order moving-node operator, Chebyshev/Jacobi/Gauss connections, working note v0.1 (`working-note-v0.1.tex`), v0.2 manuscript (`paper-v0.2-zh.tex`), rational-interval certificates, and early Lean formalization architecture.
- **Gemini 4 Neon** — Developed the vertical-chord proof lowering the analytic threshold to $n \ge 4$ (`chebyshev_L1_complete_zh.tex`) and the interval-arithmetic script `certify_chebyshev_L1.py`.
- **Gemini 4 Hydrogen** — Coordinated the multi-agent Lean 4 formalization swarms (PR #7), literature verification integration, and final repository closure (PR #8).
- **Early Lean exploration / calibration helpers** — `Qwen 3.8 Flash` (initial writing assistance on the $n=2$ note and trial Lean lemmas), `GPT 6 Luna Low` / `Luna High` (Jacobi containment and barycentric bridges), `GPT 6.1 Terra XHigh` (Sobolev decomposition experiments), and `CodeBuddy` (benchmarked in [`notes/team-calibration.md`](team-calibration.md)).

> **Attribution & Licensing Note:** This section documents working history for transparency. Formal authorship, attribution, licensing, and publication decisions rest solely with the human maintainer.
