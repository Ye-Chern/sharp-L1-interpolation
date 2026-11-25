import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp

/-!
# Chebyshev evaluation on the certificate grid

The certificate uses the unnormalized node polynomial from paper.tex, equation
`char`. The order is `k + 1`, so all three Chebyshev indices are natural.
-/

namespace SharpL1

open Polynomial
open Polynomial.Chebyshev (U)

/-- `(V_k, V_{k+1})`, evaluated by the integer loop in the certificate checker. -/
def scaledUPair (s y : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 2 * y)
  | k + 1 =>
    let (a, b) := scaledUPair s y k
    (b, 2 * y * b - s ^ 2 * a)

/-- The unnormalized node polynomial at order `k + 1`. -/
noncomputable def nodePolynomial (k : ℕ) (t : ℝ) : ℝ[X] :=
  U ℝ ((k : ℤ) + 2) - C (2 * t) * U ℝ ((k : ℤ) + 1) + C (t ^ 2) * U ℝ k

/-- The integer sign test in certificates/check.py at order `k + 1`. -/
def scaledNodeEval (s t y : ℤ) (k : ℕ) : ℤ :=
  let (a, b) := scaledUPair s y k
  2 * y * b - s ^ 2 * a - 2 * t * b + t ^ 2 * a

private theorem scaledUPair_spec (s y : ℤ) (hs : s ≠ 0) (k : ℕ) :
    ((scaledUPair s y k).1 : ℝ) =
      (s : ℝ) ^ k * (U ℝ k).eval ((y : ℝ) / s) ∧
    ((scaledUPair s y k).2 : ℝ) =
      (s : ℝ) ^ (k + 1) * (U ℝ ((k : ℤ) + 1)).eval ((y : ℝ) / s) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  induction k with
  | zero =>
    constructor
    · simp [scaledUPair, Polynomial.Chebyshev.U_zero]
    · simp [scaledUPair, Polynomial.Chebyshev.U_one]
      field_simp
  | succ k ih =>
    obtain ⟨ha, hb⟩ := ih
    constructor
    · simpa [scaledUPair] using hb
    · simp only [scaledUPair, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat,
        Nat.cast_succ]
      rw [ha, hb, show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X, pow_succ]
      field_simp

theorem scaledNodeEval_spec (s t y : ℤ) (hs : s ≠ 0) (k : ℕ) :
    (scaledNodeEval s t y k : ℝ) =
      (s : ℝ) ^ (k + 2) * (nodePolynomial k ((t : ℝ) / s)).eval ((y : ℝ) / s) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  obtain ⟨ha, hb⟩ := scaledUPair_spec s y hs k
  simp only [scaledNodeEval, nodePolynomial, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, eval_add, eval_sub, eval_mul, eval_C]
  rw [ha, hb, Polynomial.Chebyshev.U_add_two]
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X, pow_succ]
  field_simp

theorem natDegree_nodePolynomial (k : ℕ) (t : ℝ) :
    (nodePolynomial k t).natDegree = k + 2 := by
  have hu₂ : (U ℝ ((k : ℤ) + 2)).natDegree = k + 2 := by
    simpa using Polynomial.Chebyshev.natDegree_U_natCast ℝ (k + 2)
  have hu₁ : (U ℝ ((k : ℤ) + 1)).natDegree = k + 1 := by
    simpa using Polynomial.Chebyshev.natDegree_U_natCast ℝ (k + 1)
  have hu₀ := Polynomial.Chebyshev.natDegree_U_natCast ℝ k
  have h₁ : (C (2 * t) * U ℝ ((k : ℤ) + 1)).natDegree <
      (U ℝ ((k : ℤ) + 2)).natDegree := by
    calc
      _ ≤ (U ℝ ((k : ℤ) + 1)).natDegree := natDegree_C_mul_le _ _
      _ < _ := by rw [hu₁, hu₂]; omega
  have hsub := natDegree_sub_eq_left_of_natDegree_lt h₁
  have h₀ : (C (t ^ 2) * U ℝ k).natDegree <
      (U ℝ ((k : ℤ) + 2) - C (2 * t) * U ℝ ((k : ℤ) + 1)).natDegree := by
    calc
      _ ≤ (U ℝ k).natDegree := natDegree_C_mul_le _ _
      _ < _ := by rw [hsub, hu₀, hu₂]; omega
  rw [nodePolynomial, natDegree_add_eq_left_of_natDegree_lt h₀, hsub, hu₂]

theorem nodePolynomial_ne_zero (k : ℕ) (t : ℝ) : nodePolynomial k t ≠ 0 := by
  intro h
  have hdeg := natDegree_nodePolynomial k t
  rw [h, natDegree_zero] at hdeg
  omega

theorem scaledNodeEval_sign_change (s t lo hi : ℤ) (hs : 0 < s) (k : ℕ)
    (h : scaledNodeEval s t lo k * scaledNodeEval s t hi k < 0) :
    let p := nodePolynomial k ((t : ℝ) / s)
    p.eval ((lo : ℝ) / s) * p.eval ((hi : ℝ) / s) < 0 := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have h' : (scaledNodeEval s t lo k : ℝ) * (scaledNodeEval s t hi k : ℝ) < 0 := by
    exact_mod_cast h
  rw [scaledNodeEval_spec s t lo hs.ne' k, scaledNodeEval_spec s t hi hs.ne' k,
    mul_mul_mul_comm] at h'
  exact neg_of_mul_neg_right h' (mul_nonneg (pow_nonneg hs'.le _) (pow_nonneg hs'.le _))

end SharpL1
