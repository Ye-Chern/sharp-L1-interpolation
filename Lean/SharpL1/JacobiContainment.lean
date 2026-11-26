import SharpL1.JacobiSymmetry
import Mathlib.Tactic.Ring

open Polynomial
open Polynomial.Chebyshev (U)

namespace SharpL1

private noncomputable def uEval (y : ℝ) (m : ℕ) : ℝ := (U ℝ (m : ℤ)).eval y

private theorem uEval_zero (y : ℝ) : uEval y 0 = 1 := by
  simp [uEval]

private theorem uEval_one (y : ℝ) : uEval y 1 = 2 * y := by
  simp [uEval]

private theorem uEval_recurrence (y : ℝ) (m : ℕ) :
    uEval y (m + 2) = 2 * y * uEval y (m + 1) - uEval y m := by
  have h := congrArg (fun p : ℝ[X] => p.eval y)
    (Polynomial.Chebyshev.U_add_two ℝ (m : ℤ))
  simp only [uEval, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    eval_sub, eval_mul, eval_ofNat, eval_X] at h ⊢
  exact h

/-- For `y ≥ 1`, the Chebyshev values start at one and increase. -/
private theorem uEval_ge_one_and_mono (y : ℝ) (hy : 1 ≤ y) (m : ℕ) :
    1 ≤ uEval y m ∧ uEval y m ≤ uEval y (m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      constructor
      · rw [uEval_zero]
      · rw [uEval_zero, uEval_one]
        linarith
  | one =>
      constructor
      · rw [uEval_one]
        linarith
      · have h2 : uEval y 2 = 4 * y * y - 1 := by
          rw [uEval_recurrence y 0, uEval_zero, uEval_one]
          ring
        rw [uEval_one, h2]
        nlinarith [sq_nonneg (y - 1)]
  | more m ih0 ih1 =>
      have hrec := uEval_recurrence y (m + 1)
      have hm : 1 ≤ uEval y (m + 1) := ih1.1
      have hmono : uEval y (m + 1) ≤ uEval y (m + 2) := ih1.2
      constructor
      · exact hm.trans hmono
      · have hyprod : uEval y (m + 2) ≤ y * uEval y (m + 2) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hy) (le_of_lt (by linarith : 0 < uEval y (m + 2)))]
        have hrec' : uEval y (m + 3) =
            2 * y * uEval y (m + 2) - uEval y (m + 1) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec
        rw [hrec']
        nlinarith

/-- A useful parameter decomposition of the node polynomial on evaluation. -/
private theorem nodePolynomial_eval_decompose (k : ℕ) (t y : ℝ) :
    (nodePolynomial k t).eval y = (nodePolynomial k 1).eval y +
      (1 - t) * (2 * uEval y (k + 1) - (1 + t) * uEval y k) := by
  simp only [nodePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    Nat.cast_add, Nat.cast_one, uEval]
  ring

/-- For `y ≥ 1`, the node polynomial is strictly positive whenever `-1 < t < 1`. -/
theorem nodePolynomial_eval_pos_of_one_le (k : ℕ) {t y : ℝ}
    (hthi : t < 1) (hy : 1 ≤ y) :
    0 < (nodePolynomial k t).eval y := by
  have hU := uEval_ge_one_and_mono y hy k
  have hU0 : 0 < uEval y k := by linarith [hU.1]
  have hcoef : 0 < 1 - t := by linarith
  have hbracket : 0 < 2 * uEval y (k + 1) - (1 + t) * uEval y k := by
    have hprod : 0 < (1 - t) * uEval y k := mul_pos hcoef hU0
    nlinarith [hU.2]
  have hUplus : 0 ≤ (U ℝ ((k : ℤ) + 1)).eval y := by
    have h := (uEval_ge_one_and_mono y hy (k + 1)).1
    simpa [uEval] using (show 0 ≤ uEval y (k + 1) by linarith)
  have hp1 : 0 ≤ (nodePolynomial k 1).eval y := by
    rw [nodePolynomial_one]
    simp only [eval_mul, eval_sub, eval_ofNat, eval_X, eval_one]
    have hyminus : 0 ≤ y - 1 := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hyminus) hUplus
  rw [nodePolynomial_eval_decompose]
  have hterm : 0 < (1 - t) * (2 * uEval y (k + 1) - (1 + t) * uEval y k) :=
    mul_pos hcoef hbracket
  linarith

/-- Every root of `nodePolynomial k t` lies strictly inside `(-1,1)` for `|t| < 1`. -/
theorem nodePolynomial_root_mem_Ioo (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hroot : (nodePolynomial k t).IsRoot y) :
    y ∈ Set.Ioo (-1 : ℝ) 1 := by
  have ht' := abs_lt.mp ht
  have h_eval : (nodePolynomial k t).eval y = 0 := hroot
  constructor
  · by_contra hy
    have hy' : y ≤ -1 := by linarith
    have hreflect : (nodePolynomial k (-t)).IsRoot (-y) :=
      (nodePolynomial_isRoot_reflect k t y).mpr hroot
    have hneg_param : -t < 1 := by linarith [ht'.1]
    have hneg_y : 1 ≤ -y := by linarith [hy']
    have hpos : 0 < (nodePolynomial k (-t)).eval (-y) :=
      nodePolynomial_eval_pos_of_one_le (k := k) (t := -t) (y := -y)
        hneg_param hneg_y
    exact (ne_of_gt hpos) hreflect
  · by_contra hy
    have hy' : 1 ≤ y := by linarith
    exact (ne_of_gt (nodePolynomial_eval_pos_of_one_le k ht'.2 hy')) h_eval

end SharpL1
