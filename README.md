# Sharp higher-order L1 interpolation on an interval

**Complete all-order formalization (`formalize/chebyshev-L1-complete`).** The complete all-$n$ proof in [`paper.tex`](paper.tex) ([`paper.pdf`](paper.pdf); archived Chinese exposition [`notes/chebyshev_L1_complete_zh.tex`](notes/chebyshev_L1_complete_zh.tex), with companion verification script [`certify_chebyshev_L1.py`](certify_chebyshev_L1.py)) is formalized unconditionally in Lean 4.32.2 / Mathlib under [`Lean/`](Lean/), with zero `sorry`, zero `native_decide`, and only the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

For every positive integer $n \ge 1$ and every compact interval $[a, b]$ with $L = b - a > 0$, the sharp $L^1$ interpolation inequality

```
||f^(n)||_{L^1[a,b]} <= 4^n n! L^(-n) ||f||_{L^1[a,b]} + (L/2) b_n ||f^(n+1)||_{L^1[a,b]}
```

holds for all $f \in W^{n+1,1}([a,b])$ (and $C^{n+1}([a,b])$), where

```
b_n = E_n(0) = 1 - 2^n/(n+1) + 2^(n+1)/(n+1) * sum_{m=1}^{floor((n+1)/2)} (-1)^(m-1) cos(m pi / (n+2))^(n+1).
```

Both constants are optimal (even on $C^\infty([a,b])$), and equality in $C^{n+1}([a,b])$ holds if and only if $f(x) = c\, U_n((2x - a - b)/(b - a))$ for some $c \in \mathbb{R}$.

## Contents

- [`paper.tex`](paper.tex) ([`paper.pdf`](paper.pdf)): English paper with the complete all-$n$ proof (Theorem 1 `thm:full`, moving-node operator $T_n$, vertical-chord contour integral $\Delta_n(t)$, analytic $n \ge 4$ bounds, elementary $n=1,2$ and certified $n=3$ bounds, and Section 9 Lean 4 formalization map).
- [`notes/chebyshev_L1_complete_zh.tex`](notes/chebyshev_L1_complete_zh.tex): archived Chinese exposition of the complete all-$n$ proof.
- [`certify_chebyshev_L1.py`](certify_chebyshev_L1.py): companion Python script for the $n=3$ rational Riemann-sum check and sanity checks.
- [`Lean/SharpL1/Analysis/MainTheorem.lean`](Lean/SharpL1/Analysis/MainTheorem.lean): unconditional master theorem `SharpL1.Analysis.theorem_sharp_L1_interpolation_full` and its individual parts.
- [`Lean/Audit.lean`](Lean/Audit.lean): axiom audit across all modules.
- [`FORMALIZATION.md`](FORMALIZATION.md): module map, theorem inventory, and verification instructions.
- Historical v0.2 draft artifacts (preserved): [`notes/paper-v0.2-zh.tex`](notes/paper-v0.2-zh.tex), `certificates/`, `notes/`.

## Reproduce

Run the Lean build and axiom audit from `Lean/` (using `LEAN_NUM_THREADS=1` on 16 GiB hosts):

```sh
cd Lean
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 lake env lean Audit.lean
```

All `#print axioms` checks in `Lean/Audit.lean` report only `[propext, Classical.choice, Quot.sound]` (with kernel-computed checks such as `n3_block0_certified`..`n3_block4_certified` depending only on `[propext]`).
