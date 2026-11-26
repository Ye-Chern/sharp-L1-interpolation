import SharpL1.Jacobi
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

open Polynomial
open Polynomial.Chebyshev (U)

namespace SharpL1

/-- At the center the node polynomial is the Chebyshev polynomial U_(k+2). -/
theorem nodePolynomial_zero (k : ℕ) :
    nodePolynomial k 0 = U ℝ ((k : ℤ) + 2) := by
  simp [nodePolynomial]

/-- The positive endpoint factorization in the paper. -/
theorem nodePolynomial_one (k : ℕ) :
    nodePolynomial k 1 = 2 * (X - 1) * U ℝ ((k : ℤ) + 1) := by
  simp only [nodePolynomial, mul_one, one_pow, map_ofNat, map_one, one_mul]
  rw [Polynomial.Chebyshev.U_add_two]
  ring

/-- The negative endpoint factorization in the paper. -/
theorem nodePolynomial_neg_one (k : ℕ) :
    nodePolynomial k (-1) = 2 * (X + 1) * U ℝ ((k : ℤ) + 1) := by
  simp only [nodePolynomial, mul_neg, mul_one, neg_one_sq, map_neg, map_ofNat,
    map_one, one_mul]
  rw [Polynomial.Chebyshev.U_add_two]
  ring

/-- Simultaneous reflection of parameter and variable changes the sign by degree parity. -/
theorem nodePolynomial_eval_reflect (k : ℕ) (t y : ℝ) :
    (nodePolynomial k (-t)).eval (-y) = (-1 : ℝ) ^ (k + 2) * (nodePolynomial k t).eval y := by
  have h0 := Polynomial.Chebyshev.U_eval_neg ℝ k y
  have h1 := Polynomial.Chebyshev.U_eval_neg ℝ (k + 1) y
  have h2 := Polynomial.Chebyshev.U_eval_neg ℝ (k + 2) y
  simp only [Int.cast_negOnePow_natCast] at h0 h1 h2
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2
  simp only [nodePolynomial, eval_add, eval_sub, eval_mul, eval_C, neg_sq, mul_neg]
  rw [h0, h1, h2]
  simp only [pow_add, pow_two]
  ring

/-- The node roots for opposite parameters are reflections of each other. -/
theorem nodePolynomial_isRoot_reflect (k : ℕ) (t y : ℝ) :
    (nodePolynomial k (-t)).IsRoot (-y) ↔ (nodePolynomial k t).IsRoot y := by
  simp [IsRoot, nodePolynomial_eval_reflect]

/-- Reflection as an identity of polynomials, not just of evaluations. -/
theorem nodePolynomial_comp_reflect (k : ℕ) (t : ℝ) :
    (nodePolynomial k (-t)).comp (-X) =
      C ((-1 : ℝ) ^ (k + 2)) * nodePolynomial k t := by
  apply Polynomial.funext
  intro y
  simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] using
    nodePolynomial_eval_reflect k t y

/-- Reflection of the entire multiset of roots, retaining multiplicities. -/
theorem nodePolynomial_roots_reflect (k : ℕ) (t : ℝ) :
    (nodePolynomial k (-t)).roots.map (fun y => -y) = (nodePolynomial k t).roots := by
  calc
    _ = ((nodePolynomial k (-t)).comp (-X)).roots :=
      (Polynomial.roots_comp_neg_X _).symm
    _ = _ := by rw [nodePolynomial_comp_reflect, Polynomial.roots_C_mul _ (by positivity)]

end SharpL1
