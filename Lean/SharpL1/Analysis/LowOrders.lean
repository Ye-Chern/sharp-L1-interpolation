module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

/-!
# Low-order center comparisons from Section 7

This file formalizes the explicit low-order error functions `e₁` and `e₂` from
Section 7 (`\label{sec:certificate}`) of `paper.tex`, and proves their strict
center maximality on `(0, 1]`:

- `e₁ t = (1 - t ^ 2) / 2` satisfies `e₁ t < e₁ 0` for `0 < t ≤ 1`.
- `e₂ t = ((2 + 7 * t ^ 2) * Real.sqrt (8 + t ^ 2) - 2 - 24 * t ^ 2 - t ^ 3) / 6`
  satisfies `e₂ t < e₂ 0` for `0 < t ≤ 1`, proved via `HasDerivAt` for `6 * e₂`,
  the bound `135 / Real.sqrt 8 < 48`, and interval strict anti-monotonicity on `[0, 1]`.
-/

namespace SharpL1.Analysis

/-- Explicit order-1 error function `E₁(t) = (1 - t²) / 2` from `paper.tex` Section 7. -/
@[expose] noncomputable def e₁ (t : ℝ) : ℝ :=
  (1 - t ^ 2) / 2

/-- Explicit order-2 error function on `[0, 1]` from `paper.tex` Section 7:
`6 E₂(t) = (2 + 7 t²) √(8 + t²) - 2 - 24 t² - t³`. -/
@[expose] noncomputable def e₂ (t : ℝ) : ℝ :=
  ((2 + 7 * t ^ 2) * Real.sqrt (8 + t ^ 2) - 2 - 24 * t ^ 2 - t ^ 3) / 6

/-- Center comparison for `e₁`: `e₁ t < e₁ 0` for `0 < t ≤ 1`. -/
theorem e₁_lt_e₁_zero {t : ℝ} (ht0 : 0 < t) (_ht1 : t ≤ 1) : e₁ t < e₁ 0 := by
  unfold e₁
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht0
  linarith

/-- Scaled form `6 * e₂ t` matching the display in `paper.tex` Section 7. -/
theorem six_mul_e₂_eq (t : ℝ) :
    6 * e₂ t = (2 + 7 * t ^ 2) * Real.sqrt (8 + t ^ 2) - 2 - 24 * t ^ 2 - t ^ 3 := by
  unfold e₂
  ring

/-- Derivative of `6 * e₂` at any `t : ℝ`, matching
`t ((114 + 21 t²) / √(8 + t²) - 48 - 3 t)` in `paper.tex` Section 7. -/
theorem hasDerivAt_six_mul_e₂ (t : ℝ) :
    HasDerivAt (fun x => 6 * e₂ x)
      (t * ((114 + 21 * t ^ 2) / Real.sqrt (8 + t ^ 2) - 48 - 3 * t)) t := by
  have hfn : (fun x => 6 * e₂ x) =
      fun x => (2 + 7 * x ^ 2) * Real.sqrt (8 + x ^ 2) - 2 - 24 * x ^ 2 - x ^ 3 :=
    funext six_mul_e₂_eq
  rw [hfn]
  have h8 : (0 : ℝ) < 8 + t ^ 2 := by positivity
  have hpoly : HasDerivAt (fun x : ℝ => 2 + 7 * x ^ 2) (14 * t) t :=
    (HasDerivAt.const_add 2 (HasDerivAt.const_mul 7 (hasDerivAt_pow 2 t))).congr_deriv (by simp; ring)
  have hinner : HasDerivAt (fun x : ℝ => 8 + x ^ 2) (2 * t) t :=
    (HasDerivAt.const_add 8 (hasDerivAt_pow 2 t)).congr_deriv (by simp)
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (8 + x ^ 2))
      (2 * t / (2 * Real.sqrt (8 + t ^ 2))) t :=
    hinner.sqrt h8.ne'
  have hfull := (((HasDerivAt.mul hpoly hsqrt).sub_const 2).sub
    (HasDerivAt.const_mul 24 (hasDerivAt_pow 2 t))).sub (hasDerivAt_pow 3 t)
  refine hfull.congr_deriv ?_
  have hsqrt_ne : Real.sqrt (8 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h8).ne'
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  rw [Real.sq_sqrt h8.le]
  ring

/-- Key numerical bound `135 / √8 < 48` from `paper.tex` Section 7. -/
theorem one_hundred_thirty_five_div_sqrt_eight_lt_forty_eight :
    (135 : ℝ) / Real.sqrt 8 < 48 := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_lt_iff₀ hsqrt_pos]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

/-- For `0 < t ≤ 1`, the derivative of `6 * e₂` is strictly negative. -/
theorem six_mul_e₂_deriv_neg {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * ((114 + 21 * t ^ 2) / Real.sqrt (8 + t ^ 2) - 48 - 3 * t) < 0 := by
  have hsq_le : t ^ 2 ≤ 1 := by nlinarith
  have hnum_le : 114 + 21 * t ^ 2 ≤ 135 := by linarith
  have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_ge : Real.sqrt 8 ≤ Real.sqrt (8 + t ^ 2) :=
    Real.sqrt_le_sqrt (by linarith [sq_nonneg t])
  have hfrac_le : (114 + 21 * t ^ 2) / Real.sqrt (8 + t ^ 2) ≤ 135 / Real.sqrt 8 :=
    div_le_div₀ (by norm_num) hnum_le hsqrt8_pos hsqrt_ge
  have hconst := one_hundred_thirty_five_div_sqrt_eight_lt_forty_eight
  have hfactor : (114 + 21 * t ^ 2) / Real.sqrt (8 + t ^ 2) - 48 - 3 * t < 0 := by
    linarith
  exact mul_neg_of_pos_of_neg ht0 hfactor

/-- `e₂` is strictly decreasing on `[0, 1]`. -/
theorem e₂_strictAntiOn : StrictAntiOn e₂ (Set.Icc (0 : ℝ) 1) := by
  let g : ℝ → ℝ := fun x => 6 * e₂ x
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_six_mul_e₂ x).continuousAt).continuousOn
  have hg_deriv : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1), deriv g x < 0 := by
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_six_mul_e₂ x).deriv]
    exact six_mul_e₂_deriv_neg hx.1 hx.2.le
  have hg_anti : StrictAntiOn g (Set.Icc (0 : ℝ) 1) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 1) hg_cont hg_deriv
  intro a ha b hb hab
  have hlt : g b < g a := hg_anti ha hb hab
  dsimp only [g] at hlt
  linarith

/-- Center comparison for `e₂`: `e₂ t < e₂ 0` for `0 < t ≤ 1`. -/
theorem e₂_lt_e₂_zero {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : e₂ t < e₂ 0 :=
  e₂_strictAntiOn ⟨le_refl 0, zero_le_one⟩ ⟨ht0.le, ht1⟩ ht0

end SharpL1.Analysis
