module

public import SharpL1.Chebyshev
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

public section

open Polynomial

namespace SharpL1

open Matrix Polynomial
open Polynomial.Chebyshev (U)

variable {R : Type*} [CommRing R]

/-- Laplace expansion for a matrix whose first row and column have bandwidth one. -/
theorem sparse_det (n : ℕ) (A : Matrix (Fin (n+2)) (Fin (n+2)) R)
    (hr : ∀ j : Fin n, A 0 j.succ.succ = 0)
    (hc : ∀ i : Fin n, A i.succ.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      A 0 1 * A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
  have h10 : (1 : Fin (n+2)).succAbove 0 = 0 := by
    change (0 : Fin (n+1)).succ.succAbove 0 = 0
    simp
  have h1s (i : Fin n) : (1 : Fin (n+2)).succAbove i.succ = i.succ.succ := by
    apply Fin.ext
    simp [Fin.succAbove]
  have hminor : (A.submatrix Fin.succ (1 : Fin (n+2)).succAbove).det =
      A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Matrix.submatrix_apply,
      Fin.succ_zero_eq_one, h10, hc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    congr 1
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, one_mul, Fin.succ_zero_eq_one,
    hr, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    hminor]
  simp only [Fin.succAbove_zero, Fin.val_one, pow_one]
  ring




/-- Leading continuants of the unnormalized tridiagonal pencil. -/
@[expose] noncomputable def leadingContinuant (t : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 * X - C t
  | n + 2 => 2 * X * leadingContinuant t (n + 1) - leadingContinuant t n

theorem leadingContinuant_spec (t : ℝ) (k : ℕ) :
    leadingContinuant t k = U ℝ k - C t * U ℝ ((k : ℤ) - 1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [leadingContinuant, Polynomial.Chebyshev.U_zero,
      Polynomial.Chebyshev.U_neg_one]
  | one => simp [leadingContinuant, Polynomial.Chebyshev.U_zero,
      Polynomial.Chebyshev.U_one]
  | more k ih0 ih1 =>
    have hprev : U ℝ ((k : ℤ) + 1) =
        2 * X * U ℝ k - U ℝ ((k : ℤ) - 1) := by
      have h := Polynomial.Chebyshev.U_add_two ℝ ((k : ℤ) - 1)
      have h2 : (k : ℤ) - 1 + 2 = (k : ℤ) + 1 := by omega
      have h1 : (k : ℤ) - 1 + 1 = (k : ℤ) := by omega
      rw [h2, h1] at h
      exact h
    simp only [leadingContinuant, ih0, ih1, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, add_sub_cancel_right]
    rw [Polynomial.Chebyshev.U_add_two]
    simp only [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by omega, hprev]
    ring

/-- Closing the last endpoint yields the paper's unnormalized node polynomial. -/
theorem closingContinuant_eq_nodePolynomial (t : ℝ) (k : ℕ) :
    (2 * X - C t) * leadingContinuant t (k + 1) - leadingContinuant t k =
      nodePolynomial k t := by
  rw [leadingContinuant_spec, leadingContinuant_spec]
  simp only [Nat.cast_add, Nat.cast_one, show (k : ℤ) + 1 - 1 = k by omega]
  unfold nodePolynomial
  rw [Polynomial.Chebyshev.U_add_two]
  have hprev : U ℝ ((k : ℤ) + 1) =
      2 * X * U ℝ k - U ℝ ((k : ℤ) - 1) := by
    have h := Polynomial.Chebyshev.U_add_two ℝ ((k : ℤ) - 1)
    have h2 : (k : ℤ) - 1 + 2 = (k : ℤ) + 1 := by omega
    have h1 : (k : ℤ) - 1 + 1 = (k : ℤ) := by omega
    rw [h2, h1] at h
    exact h
  rw [hprev]
  simp only [map_mul, map_ofNat, map_pow]
  ring

end SharpL1





open Polynomial

namespace SharpL1

/-- A tridiagonal matrix with arbitrary diagonal and −1 on neighboring indices. -/
@[expose] def pathPencil {R : Type*} [CommRing R] (m : ℕ) (a : ℕ → R) :
    Matrix (Fin m) (Fin m) R := fun i j =>
  if i.val = j.val then a i.val
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

theorem pathPencil_tail {R : Type*} [CommRing R] (m : ℕ) (a : ℕ → R) :
    (pathPencil (m + 1) a).submatrix Fin.succ Fin.succ =
      pathPencil m (fun i => a (i + 1)) := by
  ext i j
  simp only [pathPencil, Matrix.submatrix_apply, Fin.val_succ]
  have heq : i.val + 1 = j.val + 1 ↔ i.val = j.val := by omega
  have hadj : (i.val + 1 + 1 = j.val + 1 ∨ j.val + 1 + 1 = i.val + 1) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
  simp only [heq, hadj]

theorem pathPencil_det_succ_succ {R : Type*} [CommRing R] (m : ℕ) (a : ℕ → R) :
    (pathPencil (m + 2) a).det =
      a 0 * (pathPencil (m + 1) (fun i => a (i + 1))).det -
      (pathPencil m (fun i => a (i + 2))).det := by
  have hr : ∀ j : Fin m, pathPencil (m + 2) a 0 j.succ.succ = 0 := by
    intro j
    simp [pathPencil]
  have hc : ∀ i : Fin m, pathPencil (m + 2) a i.succ.succ 0 = 0 := by
    intro i
    simp [pathPencil]
  rw [sparse_det m _ hr hc]
  have htwo : (pathPencil (m + 2) a).submatrix (Fin.succ ∘ Fin.succ)
      (Fin.succ ∘ Fin.succ) = pathPencil m (fun i => a (i + 2)) := by
    rw [← Matrix.submatrix_submatrix, pathPencil_tail, pathPencil_tail]
  rw [pathPencil_tail, htwo]
  simp [pathPencil]

end SharpL1




open Polynomial

namespace SharpL1

/-- The pencil diagonal with the single t endpoint at its final index. -/
@[expose] noncomputable def lastDiagonal (t : ℝ) (m i : ℕ) : ℝ[X] :=
  if i + 1 = m then 2 * X - C t else 2 * X

theorem lastPencil_det (t : ℝ) (m : ℕ) :
    (pathPencil m (lastDiagonal t m)).det = leadingContinuant t m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [leadingContinuant]
  | one => simp [pathPencil, lastDiagonal, leadingContinuant]
  | more m ih0 ih1 =>
    rw [pathPencil_det_succ_succ]
    have ha : lastDiagonal t (m + 2) 0 = 2 * X := by
      simp [lastDiagonal]
    have h1 : (fun i => lastDiagonal t (m + 2) (i + 1)) =
        lastDiagonal t (m + 1) := by
      funext i
      simp only [lastDiagonal]
      have h : i + 1 + 1 = m + 2 ↔ i + 1 = m + 1 := by omega
      simp only [h]
    have h2 : (fun i => lastDiagonal t (m + 2) (i + 2)) =
        lastDiagonal t m := by
      funext i
      simp only [lastDiagonal]
      have h : i + 2 + 1 = m + 2 ↔ i + 1 = m := by omega
      simp only [h]
    rw [ha, h1, h2, ih1, ih0]
    rfl

/-- The polynomial diagonal of the unnormalized two-endpoint pencil. -/
@[expose] noncomputable def endpointDiagonal (t : ℝ) (m i : ℕ) : ℝ[X] :=
  if i = 0 ∨ i + 1 = m then 2 * X - C t else 2 * X

theorem endpointPencil_det (t : ℝ) (k : ℕ) :
    (pathPencil (k + 2) (endpointDiagonal t (k + 2))).det = nodePolynomial k t := by
  rw [pathPencil_det_succ_succ]
  have ha : endpointDiagonal t (k + 2) 0 = 2 * X - C t := by simp [endpointDiagonal]
  have h1 : (fun i => endpointDiagonal t (k + 2) (i + 1)) =
      lastDiagonal t (k + 1) := by
    funext i
    simp only [endpointDiagonal, lastDiagonal]
    have h : (i + 1 = 0 ∨ i + 1 + 1 = k + 2) ↔ i + 1 = k + 1 := by omega
    simp only [h]
  have h2 : (fun i => endpointDiagonal t (k + 2) (i + 2)) =
      lastDiagonal t k := by
    funext i
    simp only [endpointDiagonal, lastDiagonal]
    have h : (i + 2 = 0 ∨ i + 2 + 1 = k + 2) ↔ i + 1 = k := by omega
    simp only [h]
  rw [ha, h1, h2, lastPencil_det, lastPencil_det,
    closingContinuant_eq_nodePolynomial]

end SharpL1



open Polynomial

namespace SharpL1

/-- The real symmetric Jacobi matrix from paper.tex, equation J, with n = k+1. -/
@[expose] noncomputable def jacobiMatrix (k : ℕ) (t : ℝ) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ := fun i j =>
  if i.val = j.val then
    if i.val = 0 ∨ i.val + 1 = k + 2 then t / 2 else 0
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 / 2 else 0

theorem jacobi_charmatrix (k : ℕ) (t : ℝ) :
    (jacobiMatrix k t).charmatrix =
      C (1 / 2 : ℝ) • pathPencil (k + 2) (endpointDiagonal t (k + 2)) := by
  have hhalf : C (1 / 2 : ℝ) * (2 : ℝ[X]) = 1 := by
    rw [← map_ofNat (C : ℝ →+* ℝ[X]) 2, ← map_mul]
    norm_num
  have ht : C (t / 2) = C t * C (1 / 2 : ℝ) := by
    rw [← map_mul]
    congr 1
    ring
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hedge : i.val = 0 ∨ i.val + 1 = k + 2
    · simp only [Matrix.charmatrix_apply_eq, jacobiMatrix, pathPencil,
        endpointDiagonal, Matrix.smul_apply, smul_eq_mul, if_true, hedge, ht]
      calc
        X - C t * C (1 / 2 : ℝ) =
            (C (1 / 2 : ℝ) * 2) * X - C t * C (1 / 2 : ℝ) := by rw [hhalf]; simp
        _ = C (1 / 2 : ℝ) * (2 * X - C t) := by ring
    · simp only [Matrix.charmatrix_apply_eq, jacobiMatrix, pathPencil,
        endpointDiagonal, Matrix.smul_apply, smul_eq_mul, if_true, hedge, if_false,
        map_zero, sub_zero]
      rw [← mul_assoc, hhalf, one_mul]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · simp [Matrix.charmatrix_apply_ne _ _ _ hij, jacobiMatrix, pathPencil, hval, hadj]
    · simp [Matrix.charmatrix_apply_ne _ _ _ hij, jacobiMatrix, pathPencil, hval, hadj]

theorem jacobi_charpoly (k : ℕ) (t : ℝ) :
    (jacobiMatrix k t).charpoly = C ((1 / 2 : ℝ) ^ (k + 2)) * nodePolynomial k t := by
  rw [Matrix.charpoly, jacobi_charmatrix, Matrix.det_smul, Fintype.card_fin,
    endpointPencil_det, ← map_pow]

end SharpL1
