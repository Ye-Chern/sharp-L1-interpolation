# Lean 4 Formalization Map

This document maps [`paper.tex`](paper.tex) (*Sharp Second Constants in $L^1$ Landau--Kolmogorov Inequalities on a Finite Interval*, Section 9) to the machine-checked Lean 4.36.0 + Mathlib formalization in `Lean/`.

**Palomar Comparator statement:** `SharpL1.theorem_sharp_L1_interpolation_full` in [`Lean/Challenge.lean`](Lean/Challenge.lean) / [`Lean/Solution.lean`](Lean/Solution.lean) ([`Lean/comparator.json`](Lean/comparator.json))  
**Internal library master theorem:** `SharpL1.Analysis.theorem_sharp_L1_interpolation_full` in [`Lean/SharpL1/Analysis/MainTheorem.lean`](Lean/SharpL1/Analysis/MainTheorem.lean)  
**Axiom & certificate audit:** [`Lean/Audit.lean`](Lean/Audit.lean)  
**Palomar metadata:** [`Lean/formalization.yaml`](Lean/formalization.yaml)

---

## 1. Verification Scope & Proof-Path Boundaries

### Machine-Checked in Lean 4
All four clauses of Theorem 1 in [`paper.tex`](paper.tex) are unconditionally proved for every order $n = k + 1 \ge 1$ (`k : Nat`) and every compact interval $[a, b]$ ($a < b$):
- **Monotonicity and unique center maximum of $E_n$:** `explicitErrorDerivCurve_neg_all_orders`, `explicitErrorCurve_strictAntiOn_Icc_zero_one`, `explicitErrorCurve_zero_eq_centerBestConstant`, `explicitErrorCurve_unique_global_max_zero`, and `explicitErrorCurve_le_centerBestConstant`.
- **Sobolev & $C^{n+1}$ sharp inequalities:** `sharp_L1_interpolation_W1` on `SobolevW1 (k + 2) a b f`, and `sharp_L1_interpolation_contDiffOn` on $C^{n+1}([a,b])$.
- **Lexicographic optimality of $(A_n, B_n)$:** `sharp_L1_interpolation_constants_optimal` over smooth (`ContDiff`) functions.
- **$C^{n+1}$ equality characterization:** `sharp_L1_interpolation_contDiffOn_eq_iff` (scalar multiples of rescaled $U_n$).

### One-Dimensional Sobolev Definition (`SobolevW1`)
In [`Lean/SharpL1/Analysis/MovingOperator.lean`](Lean/SharpL1/Analysis/MovingOperator.lean), `SobolevW1 m a b f` formalizes $W^{m,1}[a,b]$ directly via the classical 1D absolutely continuous characterization: a derivative family `d : Nat -> R -> R` with `d 0 = f` on $[a,b]$, `ContinuousOn (d j) (Icc a b)` for $j < m$, `IntegrableOn (d m) (Icc a b) volume`, and the Fundamental Theorem of Calculus relation
$$\mathrm{d}_j(x) - \mathrm{d}_j(a) = \int_a^x \mathrm{d}_{j+1}(s)\,ds \qquad \forall j < m,\ \forall x \in [a,b].$$

### Streamlined Proof Paths vs. Paper Prose
Without altering any theorem statement, four Lean modules use elementary algebraic/complex-analytic paths tailored to Mathlib:
1. **Weighted-exponential CDFs instead of Hermite--Genocchi integration** ([`DividedCDFBridge.lean`](Lean/SharpL1/Analysis/DividedCDFBridge.lean)): `weightedCdfZero_eq_barycentric_truncatedPower` establishes $0 \le T_n h_t(x) \le 1$ and the barycentric identity directly via finite exponential laws.
2. **Paired real Gaussian vectors instead of complex Gaussian matrices** ([`FirstTermPos.lean`](Lean/SharpL1/Analysis/FirstTermPos.lean)): `pairQuadForm_pencil_law` represents $g^* M g$ via independent real pairs $\frac12(x^T M x + y^T M y)$ with explicit positive witness.
3. **Partial fractions + `Complex.log` FTC instead of Fourier inversion** ([`ChordIntegral.lean`](Lean/SharpL1/Analysis/ChordIntegral.lean)): `barycentricDelta_eq_chordDelta` derives the vertical-chord contour formula along the Joukowsky loop using `Complex.log` and the Fundamental Theorem of Calculus.
4. **Pure-kernel `decide` fixed-point quadrature for $n = 3$ instead of `mpmath.iv`** ([`LowOrderMono.lean`](Lean/SharpL1/Analysis/LowOrderMono.lean)): `n3_block0_certified` through `n3_block4_certified` verify the five subintervals on $(0, 1/2]$ purely inside Lean's kernel via exact natural-number arithmetic (`by decide`, zero external arithmetic or `native_decide`).

### Outside the Lean 4 Formalization
- Historical and literature comparisons in [`paper.tex`](paper.tex) Section 1.1, Remarks 3.2 and 4.2, and [`notes/literature.md`](notes/literature.md).
- Supplementary/unformalized analytical observations in [`notes/structural-observations.md`](notes/structural-observations.md) (cross-order interlacing, generalized Gauss quadrature walk counts, cancellation-free $1/\sqrt{\pi n}$ asymptotics, $B_n$ tables for $n=1\dots 100$, and heuristic Gaussian scaling).
- The short $L^1$-quotient extension step concluding Stechkin's problem (Corollary 2 in [`paper.tex`](paper.tex)), although all four quantitative ingredients (`movingOperator_L1_le`, `SobolevW1.L1_deriv_sub_movingOperator_le`, `sharp_L1_interpolation_constants_optimal`, and `explicitErrorCurve_le_centerBestConstant`) are Lean-verified, and the short Cauchy-theorem contour deduction proving strict monotonicity $B_{n+1} > B_n$ (Corollary 3 in [`paper.tex`](paper.tex)), deduced from the Lean-verified formula `centerBestConstant` / `explicitError_center_eq`.

---

## 2. Module Map (`Lean/SharpL1/Analysis/`)

| Paper Result | Lean Module | Key Verified Declarations |
| --- | --- | --- |
| Prop. `prop:An` ($A_n = 2^n n!$ & $U_n$ uniqueness) | [`ChebyshevFirstConstant.lean`](Lean/SharpL1/Analysis/ChebyshevFirstConstant.lean) | `intervalIntegral_chebyshevSign_mul_pow_eq_zero`, `polynomial_L1_deriv_le`, `firstBestConstant_le_of_poly_bound`, `polynomial_L1_deriv_eq_iff` |
| Prop. `prop:jacobi` (global nodes on $[-1, 1]$) | [`GlobalNodes.lean`](Lean/SharpL1/Analysis/GlobalNodes.lean) | `orderedNode_bijOn_Icc`, `orderedNode_neg`, `orderedNode_zero`, `hasDerivAt_orderedNode` (building on `JacobiOrdered`, `JacobiSymmetry`, `JacobiContainment`, `OrderedNodeCurves`) |
| Sec. `sec:sharp` (operator $T_n$, $E_n$, eq. `eq:bn`) | [`MovingOperator.lean`](Lean/SharpL1/Analysis/MovingOperator.lean) | `movingOperator_L1_le`, `movingOperator_poly`, `movingOperator_normTruncatedPower_mem_Icc`, `SobolevW1.deriv_sub_movingOperator_eq`, `SobolevW1.L1_deriv_sub_movingOperator_le`, `integral_abs_indicator_sub_movingOperator_eq_explicitError`, `explicitError_center_eq` |
| Prop. `prop:sharp` & $C^{n+1}$ equality | [`SharpSobolev.lean`](Lean/SharpL1/Analysis/SharpSobolev.lean) | `sharp_sobolev_Icc_le`, `sharp_firstConstant_Icc_le`, `sharp_secondConstant_Icc_le`, `sharp_sobolev_contDiffOn_Icc_eq_iff` |
| Prop. `prop:outer` & Lem. `lem:decomp` | [`DividedCDFBridge.lean`](Lean/SharpL1/Analysis/DividedCDFBridge.lean), [`ExplicitError.lean`](Lean/SharpL1/Analysis/ExplicitError.lean) | `weightedCdfZero_eq_barycentric_truncatedPower`, `explicitErrorDerivCurve_neg_of_Ico_half_one`, `deriv_HCurve_eq_lawSignMean`, `lawSignMean_Hcomp_of_nodes` |
| Prop. `prop:first-term` (first term $> 0$) | [`FirstTermPos.lean`](Lean/SharpL1/Analysis/FirstTermPos.lean) | `pairQuadForm_pencil_law`, `firstTerm_lawSignMean_pos` |
| Prop. `prop:chord` (vertical-chord integral) | [`ChordIntegral.lean`](Lean/SharpL1/Analysis/ChordIntegral.lean) | `barycentricDelta_eq_chordDelta`, `lawSignMean_diff_eq_chordDelta` |
| Prop. `prop:n4` & App. `app:poly-n4` ($n \ge 4$) | [`ChordBoundsN4.lean`](Lean/SharpL1/Analysis/ChordBoundsN4.lean) | `rem_lt_main_of_ge_four`, `chordDelta_pos_of_ge_four` |
| Prop. `prop:low-orders` & App. `app:n3` ($n=1,2,3$) | [`LowOrderMono.lean`](Lean/SharpL1/Analysis/LowOrderMono.lean) | `explicitError_orderedNode_one_strictAntiOn`, `explicitError_orderedNode_two_strictAntiOn`, `explicitError_orderedNode_three_lt_center`, `n3_block0_certified`..`n3_block4_certified`, `chordDelta_three_pos` |
| **Theorem 1** (`thm:full`, internal bundle) | [`MainTheorem.lean`](Lean/SharpL1/Analysis/MainTheorem.lean) | `explicitErrorDerivCurve_neg_all_orders`, `explicitErrorCurve_unique_global_max_zero`, `explicitErrorCurve_le_centerBestConstant`, `sharp_L1_interpolation_W1`, `sharp_L1_interpolation_constants_optimal`, `sharp_L1_interpolation_contDiffOn_eq_iff`, `theorem_sharp_L1_interpolation_full` |
| **Theorem 1** (`thm:full`, Palomar Comparator pair) | [`Challenge.lean`](Lean/Challenge.lean), [`Solution.lean`](Lean/Solution.lean) | `SharpL1.theorem_sharp_L1_interpolation_full` (Mathlib-only statement surface in `Challenge.lean`, verified by `lake comparator` with NanoDa + Lean kernel against `Solution.lean`) |
| Axiom & `decide` footprint audit | [`Lean/Audit.lean`](Lean/Audit.lean) | `#print axioms` on all top-level theorems: only `[propext, Classical.choice, Quot.sound]` (`[propext]` for `n=3` `decide` certificates) |

---

## 3. Reproduction & CI Verification

### Local Verification

```bash
# Lean module checks, Lean 4.36.0 + Mathlib build, and axiom audit
python3 Lean/scripts/check-lean-sources.py
cd Lean
lake exe cache get
lake build Challenge Solution SharpL1
lake env lean Audit.lean
# On Linux with bubblewrap (bwrap): ./scripts/verify-comparator.sh

# Independent Python / mpmath.iv interval-arithmetic cross-check (threshold n = 4, 5-block n = 3)
cd ..
python certify_chebyshev_L1.py
```

### GitHub Actions CI Runs
- **Lean proof checks (`lean.yml`) & Certificate checks (`certificates.yml`) on `main` (PR #7 merge `0957b75`):**
  - Lean proof checks: [Run #45768034782](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45768034782)
  - Certificate checks: [Run #45768034799](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45768034799)
- **PR #8 (`docs/english-paper`):**
  - Lean proof checks: [Run #45770473215](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45770473215)
  - Certificate checks: [Run #45770473112](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45770473112)
- **Historical v0.2 CSV certificate run (superseded cutoff $n \ge 20$):**
  - Certificate checks: [Run #45636804324](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45636804324)

---

## 4. Historical & Archived Artifacts (Superseded)

For provenance, the repository retains earlier drafts and planning artifacts from the superseded v0.2 route ($n \ge 20$ threshold + $3 \le n \le 19$ CSV bracket certificates) clearly separated from the final verified proof:
- [`notes/project-history.md`](notes/project-history.md) — Chronological record from the Nov 20 second-order note through PR #7 and PR #8.
- [`notes/origin-second-order-zh.tex`](notes/origin-second-order-zh.tex), [`notes/working-note-v0.1.tex`](notes/working-note-v0.1.tex), [`notes/paper-v0.2-zh.tex`](notes/paper-v0.2-zh.tex), [`notes/chebyshev_L1_complete_zh.tex`](notes/chebyshev_L1_complete_zh.tex) — Chinese developmental manuscripts.
- [`certificates/`](certificates/) (`check.py`, `check_constants.py`) — Superseded v0.2 rational-interval certificates (`3 <= n <= 19`).
- [`notes/phase-a.md`](notes/phase-a.md), [`notes/phase-b.md`](notes/phase-b.md), [`notes/tasks/START.md`](notes/tasks/START.md), [`notes/team-calibration.md`](notes/team-calibration.md) — Archived Lean transition plans and multi-model calibration logs.
