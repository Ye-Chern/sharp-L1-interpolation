# Sharp Second Constants in $L^1$ Landau--Kolmogorov Inequalities on a Finite Interval

[![Lean proof checks](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/workflows/lean.yml)
[![Certificate checks](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/workflows/certificates.yml/badge.svg?branch=main)](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/workflows/certificates.yml)

**Publication manuscript:** [`paper.tex`](paper.tex) · [`paper.pdf`](paper.pdf)  
**Lean 4 master theorem:** `SharpL1.Analysis.theorem_sharp_L1_interpolation_full` in [`Lean/SharpL1/Analysis/MainTheorem.lean`](Lean/SharpL1/Analysis/MainTheorem.lean)

---

## Main Result

For every integer $n \ge 1$ and every compact interval $[a, b]$ of length $L = b - a > 0$, we study the sharp lexicographic additive Landau--Kolmogorov inequality on $W^{n+1,1}([a, b])$:
$$\|f^{(n)}\|_{L^1([a,b])} \le \frac{4^n n!}{L^n}\,\|f\|_{L^1([a,b])} + \frac{L}{2} B_n\,\|f^{(n+1)}\|_{L^1([a,b])},$$
where on $[-1, 1]$ ($L = 2$) the minimal first constant is $A_n = 2^n n!$ and the minimal second constant at $A = A_n$ is explicitly
$$B_n = E_n(0) = 1 - \frac{2^n}{n+1} + \frac{2^{n+1}}{n+1}\sum_{k=1}^{\lfloor (n+1)/2 \rfloor} (-1)^{k-1} \cos^{n+1}\frac{k\pi}{n+2}.$$
The inequality is achieved globally via a moving-node Chebyshev divided-difference operator $T_n$, whose Peano error profile $E_n(t)$ is strictly decreasing on $[0, 1]$ and attains its unique global maximum at $t = 0$. The same operator attains the sharp best-approximation error $\mathcal{E}_{A_n}(D^n; \mathcal{W}_n) = B_n$ in Stechkin's problem at minimal operator norm $N = A_n$.

### Contribution & Literature Framing
Following our primary-source literature audit ([`notes/literature.md`](notes/literature.md)), the first constant $A_n$ was already established by Burenkov (1980, §4°), who left the exact $L^1$ second constant open (even for $n = 1$, where eq. (24) gave $1/2$ on $[0, 1]$ rather than the sharp $1/4$). This work represents an independent rediscovery of the extremal characterization together with—to the best of our knowledge—the first explicit closed-form evaluation $B_n = E_n(0)$ across all $n \ge 1$ (including $B_n = 1 - A_n E_n(W_1^{n+1})_1$ linking the center value to Boyanov 1975 / Kofanov 1984), a moving-node Jacobi operator resolving Burenkov's 1980 $L^1$ question, and a complete machine-checked formalization in Lean 4.32.2 + Mathlib.

---

## Repository Map

### 1. Final Verified Artifacts
- [`paper.tex`](paper.tex) / [`paper.pdf`](paper.pdf) — Complete English paper proving Theorem 1 and Corollary 2, with Section 9 documenting the Lean 4 verification scope and declaration map.
- [`Lean/SharpL1/Analysis/`](Lean/SharpL1/Analysis/) — Complete Lean 4.32.2 + Mathlib formalization of Theorem 1 (`MainTheorem.lean`, zero `sorry`, zero custom axioms).
- [`Lean/Audit.lean`](Lean/Audit.lean) — Axiom and pure-kernel `decide` verification script checking only `[propext, Classical.choice, Quot.sound]`.
- [`FORMALIZATION.md`](FORMALIZATION.md) — Detailed paper-to-Lean map, `SobolevW1` 1D characterization, proof-path comparison, and CI run links.
- [`certify_chebyshev_L1.py`](certify_chebyshev_L1.py) — Independent Python / `mpmath.iv` interval-arithmetic check of the $n \ge 4$ chord bound and 5-subinterval $n = 3$ certification.
- [`AGENTS.md`](AGENTS.md) — Maintenance, build, and synchronization guidelines.

### 2. Literature, Supplementary Notes & Historical Archive
These files are **outside the Lean 4 formalization scope** (supplementary observations, primary-source comparisons, or superseded developmental drafts preserved for provenance):
- [`notes/literature.md`](notes/literature.md) — Primary-source mathematical-equivalence review (Burenkov 1980/1986, Kofanov 1984/2002, BKP 1997/1998, BKKP 2003, Rafalson 2004, Skorokhodov 2018/2019/2022, Guo--Liu--Xu 2024).
- [`notes/structural-observations.md`](notes/structural-observations.md) — Unformalized expository observations (cross-order interlacing, generalized Gauss quadrature, cancellation-free $1/\sqrt{\pi n}$ asymptotics, $B_n$ table for $n = 1\dots 100$, and heuristic Gaussian scaling).
- [`notes/project-history.md`](notes/project-history.md) — Chronological discovery timeline and human–AI collaboration log.
- [`notes/chebyshev_L1_complete_zh.tex`](notes/chebyshev_L1_complete_zh.tex) — Complete Chinese draft introducing the vertical-chord $n \ge 4$ breakthrough.
- [`notes/paper-v0.2-zh.tex`](notes/paper-v0.2-zh.tex), [`notes/working-note-v0.1.tex`](notes/working-note-v0.1.tex), [`notes/origin-second-order-zh.tex`](notes/origin-second-order-zh.tex) — Superseded developmental Chinese notes (`v0.2` $n \ge 20$ route, `v0.1`, and the original $n = 2$ derivation).
- [`certificates/`](certificates/), [`notes/phase-a.md`](notes/phase-a.md), [`notes/phase-b.md`](notes/phase-b.md), [`notes/tasks/START.md`](notes/tasks/START.md), [`notes/team-calibration.md`](notes/team-calibration.md) — Archived v0.2 finite bracket certificates (`3 <= n <= 19`) and multi-agent transition logs.

---

## Reproducing the Verification

```bash
# 1. Verify the full Lean 4 proof and axiom footprint (Lean v4.32.2 + Mathlib)
cd Lean
lake build
lake env lean Audit.lean

# 2. Run the independent Python / mpmath.iv cross-checks (optional; requires mpmath)
cd ..
python certify_chebyshev_L1.py

# 3. Compile the English manuscript
pdflatex paper.tex && pdflatex paper.tex && pdflatex paper.tex
```

**Verified CI runs:**
- `main` (`0957b75`): [Lean proof checks (#45768034782)](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45768034782) · [Certificate checks (#45768034799)](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45768034799)
- `docs/english-paper` (PR #8): [Lean proof checks (#45770473215)](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45770473215) · [Certificate checks (#45770473112)](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45770473112)
