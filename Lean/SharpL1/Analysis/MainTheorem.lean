import SharpL1.Analysis.ExplicitError
import SharpL1.Analysis.ChordBoundsN4
import SharpL1.Analysis.LowOrderMono
import SharpL1.Analysis.MovingOperator
import SharpL1.Analysis.SharpSobolev

/-!
# Unconditional All-Order Center Maximum & Sharp `L¹` Sobolev Interpolation (Theorem 1)

This module assembles the complete, completely unconditional proof of Theorem 1 (`thm:full`)
from `chebyshev_L1_complete.tex` for every order `n = k + 1 ≥ 1`:

1. **All-order strict monotonicity (`explicitErrorDerivAt_neg_all_orders`,
   `explicitErrorDerivCurve_neg_all_orders`, `explicitErrorCurve_strictAntiOn_Icc_zero_one`)**:
   - `n = 1` (`k = 0`) and `n = 2` (`k = 1`): elementary proofs from `LowOrderMono`.
   - `n = 3` (`k = 2`): kernel-certified vertical-chord positivity `chordDelta_three_pos`
     from `LowOrderMono` + `ExplicitError` decomposition (`FirstTermPos`, `ChordIntegral`)
     on `(0, 1/2]` and exterior monotonicity on `[1/2, 1)`.
   - `n ≥ 4` (`k ≥ 3`): analytic vertical-chord bound `chordDelta_pos_of_ge_four` from
     `ChordBoundsN4` + `ExplicitError` decomposition on `(0, 1/2]` and exterior monotonicity
     on `[1/2, 1)`.
2. **Unique global maximum at `t = 0` (`explicitErrorCurve_unique_global_max_zero`)**:
   for every `k : ℕ` and `t ∈ [-1, 1] \ {0}`,
   `E_{k+1}(t) < E_{k+1}(0) = centerBestConstant (k + 1)`.
3. **Unconditional Theorem 1 (`sharp_L1_interpolation_W1`, `sharp_L1_interpolation_contDiffOn`,
   `sharp_L1_interpolation_constants_optimal`, `sharp_L1_interpolation_contDiffOn_eq_iff`,
   and the bundled master theorem `theorem_sharp_L1_interpolation_full`)**:
   - Sharp inequality on `W^{n+1, 1}([a, b])` and `C^{n+1}([a, b])` for every `a < b`
     (`L = b - a`) with constants `4^n * n! * L^(-n)` and `(L / 2) * centerBestConstant n`.
   - Optimality of both constants even on `C^∞([a, b])`.
   - Exact `C^{n+1}([a, b])` equality characterization: equality holds if and only if
     `∀ x ∈ [a, b], f x = c * U_n((2x - a - b) / (b - a))` for some `c : ℝ`.
-/

namespace SharpL1.Analysis

open Polynomial MeasureTheory Set Filter Topology
open Polynomial.Chebyshev (U)
open scoped ContDiff

/-! ### Part 1: Unconditional all-order strict monotonicity and unique center maximum -/

/-- For every order `n = k + 1 ≥ 1` and every `t ∈ (0, 1)`, `E_n'(t) < 0`. -/
theorem explicitErrorDerivAt_neg_all_orders (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    explicitErrorDerivAt k t < 0 := by
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  match k with
  | 0 =>
    have hd := (hasDerivAt_explicitErrorAt 0 ht_abs).deriv
    rw [← hd]
    exact (hasDerivAt_explicitError_orderedNode_one ht.1 ht.2).2
  | 1 =>
    have hd := (hasDerivAt_explicitErrorAt 1 ht_abs).deriv
    rw [← hd]
    exact hasDerivAt_explicitError_orderedNode_two ht.1 ht.2
  | 2 =>
    by_cases hle : t ≤ 1 / 2
    · exact explicitErrorDerivAt_neg_of_chordDelta_pos 2 ht.1 ht.2
        (chordDelta_three_pos ⟨ht.1, hle⟩)
    · exact explicitErrorDerivAt_neg_of_Ico_half_one 2 (le_of_not_ge hle) ht.2
  | k + 3 =>
    by_cases hle : t ≤ 1 / 2
    · exact explicitErrorDerivAt_neg_of_chordDelta_pos (k + 3) ht.1 ht.2
        (chordDelta_pos_of_ge_four (k + 4) (by omega) ⟨ht.1, hle⟩)
    · exact explicitErrorDerivAt_neg_of_Ico_half_one (k + 3) (le_of_not_ge hle) ht.2

/-- Curve form of all-order negative derivative: for every `k : ℕ` (`n = k + 1`) and
`t ∈ (0, 1)`, `explicitErrorDerivCurve (k + 1) t < 0`. -/
theorem explicitErrorDerivCurve_neg_all_orders (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    explicitErrorDerivCurve (k + 1) t < 0 := by
  rw [explicitErrorDerivCurve_succ]
  exact explicitErrorDerivAt_neg_all_orders k ht

/-- For every order `n = k + 1 ≥ 1`, `E_n` is strictly decreasing on `[0, 1]`. -/
theorem explicitErrorCurve_strictAntiOn_Icc_zero_one (k : ℕ) :
    StrictAntiOn (explicitErrorCurve (k + 1)) (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (continuous_explicitErrorCurve (k + 1)).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  rw [(hasDerivAt_explicitErrorCurve (Nat.succ_pos k) ht_abs).deriv]
  exact explicitErrorDerivCurve_neg_all_orders k ht

/-- At the center `t = 0`, `explicitErrorCurve (k + 1) 0` equals the closed-form cosine sum
`centerBestConstant (k + 1)` (eq. (6) of `chebyshev_L1_complete.tex`). -/
theorem explicitErrorCurve_zero_eq_centerBestConstant (k : ℕ) :
    explicitErrorCurve (k + 1) 0 = centerBestConstant (k + 1) := by
  rw [explicitErrorCurve_succ]
  exact explicitError_center_eq k

/-- **Unconditional unique center maximum**: for every order `n = k + 1 ≥ 1` and every
`t ∈ [-1, 1]` with `t ≠ 0`, `E_n(t) < centerBestConstant n`. -/
theorem explicitErrorCurve_unique_global_max_zero (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (ht0 : t ≠ 0) :
    explicitErrorCurve (k + 1) t < centerBestConstant (k + 1) := by
  rw [← explicitErrorCurve_zero_eq_centerBestConstant k]
  have hanti := explicitErrorCurve_strictAntiOn_Icc_zero_one k
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · rw [← explicitErrorCurve_neg ht]
    exact hanti ⟨le_rfl, zero_le_one⟩ ⟨by linarith, by linarith [ht.1]⟩ (neg_pos.mpr hneg)
  · exact hanti ⟨le_rfl, zero_le_one⟩ ⟨hpos.le, ht.2⟩ hpos

/-- Non-strict global center maximum bound on `[-1, 1]`. -/
theorem explicitErrorCurve_le_centerBestConstant (k : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    explicitErrorCurve (k + 1) t ≤ centerBestConstant (k + 1) := by
  by_cases ht0 : t = 0
  · subst ht0
    exact (explicitErrorCurve_zero_eq_centerBestConstant k).le
  · exact (explicitErrorCurve_unique_global_max_zero k ht ht0).le

/-! ### Part 2: Unconditional Theorem 1 (`thm:full`) -/

/-- **Unconditional sharp `L¹` Sobolev interpolation inequality on `W^{n+1, 1}([a, b])`**
for every order `n = k + 1 ≥ 1` and every interval `[a, b]` (`a < b`, `L = b - a`):
`‖f^(n)‖_{L¹[a,b]} ≤ 4^n * n! * L^(-n) * ‖f‖_{L¹[a,b]} + (L / 2) * b_n * ‖f^(n+1)‖_{L¹[a,b]}`. -/
theorem sharp_L1_interpolation_W1 (k : ℕ) {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (F : SobolevW1 (k + 2) a b f) :
    ∫ x in a..b, |F.d (k + 1) x| ≤
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
          (∫ y in a..b, |f y|) +
        ((b - a) / 2) * centerBestConstant (k + 1) * (∫ t in a..b, |F.d (k + 2) t|) :=
  sharp_sobolev_Icc_le k hab
    (fun t ht => by
      simpa only [explicitErrorCurve_succ, explicitErrorAt] using
        explicitErrorCurve_le_centerBestConstant k ht)
    F

/-- **Unconditional sharp `L¹` interpolation inequality on `C^{n+1}([a, b])`**
for every order `n = k + 1 ≥ 1` and every interval `[a, b]` (`a < b`, `L = b - a`). -/
theorem sharp_L1_interpolation_contDiffOn (k : ℕ) {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (k + 2) f (Icc a b)) :
    ∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x| ≤
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
          (∫ y in a..b, |f y|) +
        ((b - a) / 2) * centerBestConstant (k + 1) *
          (∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t|) :=
  sharp_L1_interpolation_W1 k hab (SobolevW1.ofContDiffOn hab hf)

/-- **Unconditional optimality of both constants (even on `C^∞([a, b])`)**:
1. The first constant `4^n * n! * L^(-n)` cannot be reduced for any `B : ℝ`.
2. Once the first constant is fixed at `4^n * n! * L^(-n)`, the second constant
   `(L / 2) * centerBestConstant n` cannot be reduced. -/
theorem sharp_L1_interpolation_constants_optimal (k : ℕ) {a b : ℝ} (hab : a < b) :
    (∀ A B : ℝ,
      (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
        ∫ x in a..b, |iteratedDeriv (k + 1) f x| ≤
          A * (∫ y in a..b, |f y|) + B * (∫ t in a..b, |iteratedDeriv (k + 2) f t|)) →
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) ≤ A) ∧
    (∀ B : ℝ,
      (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
        ∫ x in a..b, |iteratedDeriv (k + 1) f x| ≤
          (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
              (∫ y in a..b, |f y|) +
            B * (∫ t in a..b, |iteratedDeriv (k + 2) f t|)) →
      ((b - a) / 2) * centerBestConstant (k + 1) ≤ B) :=
  ⟨fun A B hAB => sharp_firstConstant_Icc_le (k + 1) hab A B hAB,
    fun B hB => sharp_secondConstant_Icc_le k hab B hB⟩

/-- **Unconditional `C^{n+1}([a, b])` equality characterization**:
equality holds for `f ∈ C^{n+1}([a, b])` (`a < b`, `n = k + 1`) if and only if
`∀ x ∈ [a, b], f x = c * U_n((2x - a - b) / (b - a))` for some `c : ℝ`. -/
theorem sharp_L1_interpolation_contDiffOn_eq_iff (k : ℕ) {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (k + 2) f (Icc a b)) :
    (∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x| =
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
          (∫ y in a..b, |f y|) +
        ((b - a) / 2) * centerBestConstant (k + 1) *
          (∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t|)) ↔
    ∃ c : ℝ, ∀ x ∈ Icc a b,
      f x = c * (U ℝ ((k + 1 : ℕ) : ℤ)).eval ((2 * x - a - b) / (b - a)) :=
  sharp_sobolev_contDiffOn_Icc_eq_iff k hab
    (fun t ht ht0 => by
      simpa only [explicitErrorCurve_succ, explicitErrorAt] using
        explicitErrorCurve_unique_global_max_zero k ht ht0)
    hf

/-- **Theorem 1 (`thm:full`) of `chebyshev_L1_complete.tex` — Complete Unconditional Bundle**:
for every order `n = k + 1 ≥ 1` and every nondegenerate compact interval `[a, b]` (`a < b`):
1. `E_n'(t) < 0` for all `t ∈ (0, 1)`, `E_n` is strictly decreasing on `[0, 1]`, and `E_n` attains
   its unique global maximum on `[-1, 1]` at `t = 0` with value `centerBestConstant n` (eq. (6)).
2. The sharp `L¹` Sobolev interpolation inequality holds for all `f ∈ W^{n+1, 1}([a, b])`
   with constants `4^n * n! * (b - a)^(-n)` and `((b - a) / 2) * centerBestConstant n`.
3. Both constants are optimal even when restricted to `C^∞([a, b])`.
4. In `C^{n+1}([a, b])`, equality holds if and only if
   `∀ x ∈ [a, b], f x = c * U_n((2x - a - b) / (b - a))` for some `c : ℝ`. -/
theorem theorem_sharp_L1_interpolation_full (k : ℕ) {a b : ℝ} (hab : a < b) :
    ((∀ t ∈ Ioo (0 : ℝ) 1, explicitErrorDerivCurve (k + 1) t < 0) ∧
      StrictAntiOn (explicitErrorCurve (k + 1)) (Icc (0 : ℝ) 1) ∧
      explicitErrorCurve (k + 1) 0 = centerBestConstant (k + 1) ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, t ≠ 0 →
        explicitErrorCurve (k + 1) t < centerBestConstant (k + 1))) ∧
    (∀ {f : ℝ → ℝ} (F : SobolevW1 (k + 2) a b f),
      ∫ x in a..b, |F.d (k + 1) x| ≤
        (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
            (∫ y in a..b, |f y|) +
          ((b - a) / 2) * centerBestConstant (k + 1) * (∫ t in a..b, |F.d (k + 2) t|)) ∧
    ((∀ A B : ℝ,
      (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
        ∫ x in a..b, |iteratedDeriv (k + 1) f x| ≤
          A * (∫ y in a..b, |f y|) + B * (∫ t in a..b, |iteratedDeriv (k + 2) f t|)) →
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) ≤ A) ∧
     (∀ B : ℝ,
      (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
        ∫ x in a..b, |iteratedDeriv (k + 1) f x| ≤
          (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
              (∫ y in a..b, |f y|) +
            B * (∫ t in a..b, |iteratedDeriv (k + 2) f t|)) →
      ((b - a) / 2) * centerBestConstant (k + 1) ≤ B)) ∧
    (∀ {f : ℝ → ℝ}, ContDiffOn ℝ (k + 2) f (Icc a b) →
      ((∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x| =
        (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
            (∫ y in a..b, |f y|) +
          ((b - a) / 2) * centerBestConstant (k + 1) *
            (∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t|)) ↔
      ∃ c : ℝ, ∀ x ∈ Icc a b,
        f x = c * (U ℝ ((k + 1 : ℕ) : ℤ)).eval ((2 * x - a - b) / (b - a)))) :=
  ⟨⟨fun _ ht => explicitErrorDerivCurve_neg_all_orders k ht,
    explicitErrorCurve_strictAntiOn_Icc_zero_one k,
    explicitErrorCurve_zero_eq_centerBestConstant k,
    fun _ ht ht0 => explicitErrorCurve_unique_global_max_zero k ht ht0⟩,
   fun F => sharp_L1_interpolation_W1 k hab F,
   sharp_L1_interpolation_constants_optimal k hab,
   fun hf => sharp_L1_interpolation_contDiffOn_eq_iff k hab hf⟩

end SharpL1.Analysis
