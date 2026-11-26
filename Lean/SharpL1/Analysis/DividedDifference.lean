import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ring

/-!
# Barycentric divided differences

For a finite family of distinct real nodes, the barycentric divided difference is
the weighted sum whose weights are the reciprocals of the nodal products.  The
polynomial reproduction statement below is the leading-coefficient identity
from Lagrange interpolation (Section 2 of `paper.tex`).
-/

namespace SharpL1.Analysis

/-- Divided difference over a finite set of node indices. -/
noncomputable def barycentricDividedDifferenceOn {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, f i * (∏ j ∈ s.erase i, (a i - a j))⁻¹

/-- Barycentric divided difference on `n + 1` nodes.  The product in the
denominator ranges over every node except the selected node. -/
noncomputable def barycentricDividedDifference {n : ℕ} (a : Fin (n + 1) → ℝ)
    (f : Fin (n + 1) → ℝ) : ℝ :=
  barycentricDividedDifferenceOn Finset.univ a f

theorem barycentricDividedDifferenceOn_eval_eq_coeff {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (ha : Set.InjOn a s) (P : Polynomial ℝ)
    (hP : P.degree < s.card) :
    barycentricDividedDifferenceOn s a (fun i => P.eval (a i)) = P.coeff (s.card - 1) := by
  simpa only [barycentricDividedDifferenceOn, div_eq_mul_inv] using
    (Lagrange.coeff_eq_sum ha (P := P) hP).symm

/-- On a polynomial of degree at most `n`, the barycentric divided difference
recovers its coefficient of degree `n`.  This is Mathlib's Lagrange leading
coefficient formula specialized to the finite type `Fin (n + 1)`. -/
theorem barycentricDividedDifference_eval_eq_coeff {n : ℕ}
    {a : Fin (n + 1) → ℝ} (ha : Function.Injective a) (P : Polynomial ℝ)
    (hP : P.degree < (n + 1 : ℕ)) :
    barycentricDividedDifference a (fun i => P.eval (a i)) = P.coeff n := by
  classical
  simpa [barycentricDividedDifference] using
    barycentricDividedDifferenceOn_eval_eq_coeff (s := Finset.univ) ha.injOn P (by simpa using hP)

/-- Multiplication by the linear factor of one node deletes that node. -/
theorem barycentricDividedDifferenceOn_mul_sub_erase {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (ha : Set.InjOn a s) {c : ι} (hc : c ∈ s) (f : ι → ℝ) :
    barycentricDividedDifferenceOn s a (fun i => (a i - a c) * f i) =
      barycentricDividedDifferenceOn (s.erase c) a f := by
  unfold barycentricDividedDifferenceOn
  rw [← Finset.sum_erase_add _ _ hc]
  simp only [sub_self, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hjc, hjs⟩ := Finset.mem_erase.mp hj
  have hcj : c ∈ s.erase j := Finset.mem_erase.mpr ⟨hjc.symm, hc⟩
  have hsets : (s.erase j).erase c = (s.erase c).erase j := by
    ext i
    simp only [Finset.mem_erase]
    tauto
  have hneq : a j - a c ≠ 0 := sub_ne_zero.mpr fun h => hjc (ha hjs hc h)
  rw [← Finset.mul_prod_erase (s.erase j) (fun i => a j - a i) hcj, hsets, mul_inv_rev]
  calc
    _ = ((a j - a c) * (a j - a c)⁻¹) *
        (f j * (∏ i ∈ (s.erase c).erase j, (a j - a i))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hneq, one_mul]

end SharpL1.Analysis
