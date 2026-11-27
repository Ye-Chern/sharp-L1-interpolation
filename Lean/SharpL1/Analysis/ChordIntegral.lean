module

public import SharpL1.JacobiOrdered
public import SharpL1.JacobiContainment
public import SharpL1.Analysis.NodeWeights
public import SharpL1.Analysis.ErrorDividedDifference
public import SharpL1.Probability.WeightedComparison
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Exact vertical-chord integral representation of `Δ_n(t)` (Claim 5)

This file formalizes Claim 5 (`clm:chord`) of `chebyshev_L1_complete.tex`:
for every order `n = k + 1 ≥ 1` and every `t ∈ (0, 1)`, the divided-difference /
sign-mean difference `Δ_n(t)` equals the vertical-chord integral `chordDelta n t`.

Rather than passing through Fourier inversion of probability densities, we prove
the identity directly via partial fractions (Lagrange interpolation) and the
Joukowsky map `y = (u + u⁻¹) / 2` along the vertical chord `u(v) = t + i v`,
`v ∈ [-√(1 - t²), √(1 - t²)]`.  The image `Γ(v) = (u(v) + u(v)⁻¹) / 2` is a
closed smooth loop winding clockwise once around `(t, 1]` and zero times around
`[-1, t)`.  The single-pole integrals `∫ Γ'(v) / (Γ(v) - z) dv` are evaluated
elementary by `Complex.log` primitives and the fundamental theorem of calculus.
-/

namespace SharpL1.Analysis

open Polynomial MeasureTheory
open scoped Complex

/-! ### Core definitions aligned with `ChordBoundsN4` -/

/-- Blaschke factor `φ_t(u) = (u - t) / (1 - t u)`. -/
noncomputable def blaschke (t : ℝ) (u : ℂ) : ℂ :=
  (u - (t : ℂ)) / (1 - (t : ℂ) * u)

/-- The vertical-chord integral representing `Δ_n(t)` (equation `(13)`). -/
noncomputable def chordDelta (n : ℕ) (t : ℝ) : ℝ :=
  (8 / Real.pi) * ∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2),
    (1 - t ^ 2 - v ^ 2) ^ n *
      ((-(blaschke t ((t : ℂ) + (v : ℂ) * Complex.I))) /
        (1 - ((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
          (blaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2)).re

/-- The `n + 3 = k + 4` extended nodes `(-1, u_0(t), ..., u_n(t), 1)` for order `n = k + 1`. -/
noncomputable def extendedNodes (k : ℕ) (t : ℝ) : Fin (k + 4) → ℝ := fun i =>
  if h0 : i.val = 0 then -1
  else if hlast : i.val = k + 3 then 1
  else orderedNode k t ⟨i.val - 1, by omega⟩

/-- The barycentric divided-difference formula for `Δ_{k+1}(t)`. -/
noncomputable def barycentricDelta (k : ℕ) (t : ℝ) : ℝ :=
  4 * t * barycentricDividedDifferenceOn Finset.univ (extendedNodes k t)
      (fun i => truncatedPower (k + 2) t (extendedNodes k t i)) -
    2 * (1 - t ^ 2) * barycentricDividedDifferenceOn Finset.univ (extendedNodes k t)
      (fun i => truncatedPower (k + 1) t (extendedNodes k t i))

/-! ### Properties of `extendedNodes` and factorization of `P_t^*` -/

theorem extendedNodes_zero (k : ℕ) (t : ℝ) :
    extendedNodes k t 0 = -1 := by
  simp [extendedNodes]

theorem extendedNodes_last (k : ℕ) (t : ℝ) :
    extendedNodes k t ⟨k + 3, by omega⟩ = 1 := by
  simp [extendedNodes]

theorem extendedNodes_inner (k : ℕ) (t : ℝ) (i : Fin (k + 2)) :
    extendedNodes k t ⟨i.val + 1, by omega⟩ = orderedNode k t i := by
  have h2 : i.val ≠ k + 2 := by omega
  simp [extendedNodes, h2]

private theorem orderedNode_mem_Ioo_aux (k : ℕ) {t : ℝ} (ht : |t| < 1) (i : Fin (k + 2)) :
    orderedNode k t i ∈ Set.Ioo (-1 : ℝ) 1 :=
  nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t i)

theorem extendedNodes_strictMono (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    StrictMono (extendedNodes k t) := by
  intro i j hij
  have hijv : i.val < j.val := hij
  unfold extendedNodes
  split_ifs with hi0 hilast hj0 hjlast hj0' hjlast'
  · omega
  · norm_num
  · exact (orderedNode_mem_Ioo_aux k ht _).1
  · omega
  · omega
  · omega
  · omega
  · exact (orderedNode_mem_Ioo_aux k ht _).2
  · exact orderedNode_strictMono k t (show (⟨i.val - 1, _⟩ : Fin (k + 2)) < ⟨j.val - 1, _⟩ by
      simp [Fin.lt_def]; omega)

theorem extendedNodes_mem_Icc (k : ℕ) {t : ℝ} (ht : |t| < 1) (i : Fin (k + 4)) :
    extendedNodes k t i ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold extendedNodes
  split_ifs
  · exact ⟨le_rfl, by norm_num⟩
  · exact ⟨by norm_num, le_rfl⟩
  · exact Set.Ioo_subset_Icc_self (orderedNode_mem_Ioo_aux k ht _)

/-- Factorization of `monicNodePolynomial k t` into linear factors over `orderedNode k t`. -/
theorem monicNodePolynomial_eq_prod (k : ℕ) (t : ℝ) :
    monicNodePolynomial k t = ∏ i : Fin (k + 2), (X - C (orderedNode k t i)) := by
  have hne : (1 / 2 : ℝ) ^ (k + 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hroots : (monicNodePolynomial k t).roots = (nodePolynomial k t).roots := by
    rw [monicNodePolynomial, Polynomial.roots_C_mul _ hne]
  have hsplits : (monicNodePolynomial k t).Splits := by
    rw [monicNodePolynomial]
    exact (Polynomial.Splits.C _).mul (nodePolynomial_splits k t)
  have hprod := hsplits.eq_prod_roots
  rw [leadingCoeff_monicNodePolynomial, map_one, one_mul, hroots] at hprod
  have hmult : (nodePolynomial k t).roots =
      (Finset.univ : Finset (Fin (k + 2))).val.map (orderedNode k t) := by
    have h1 := orderedNode_ofFn k t
    have h2 : ((List.ofFn (orderedNode k t) : List ℝ) : Multiset ℝ) =
        ((nodePolynomial k t).roots.sort : Multiset ℝ) := congrArg (fun l : List ℝ => (l : Multiset ℝ)) h1
    rw [Multiset.sort_eq] at h2
    rw [← h2]
    symm
    exact Fin.univ_val_map (orderedNode k t)
  rw [hprod, hmult, Multiset.map_map]
  rfl

/-- Product of `(y - z)` over all `n + 3` extended nodes equals `(y^2 - 1) * p_t(y)`. -/
theorem prod_extendedNodes_eq (k : ℕ) (t : ℝ) (y : ℂ) :
    ∏ i : Fin (k + 4), (y - (extendedNodes k t i : ℂ)) =
      (y ^ 2 - 1) * ((1 / 2 : ℂ) ^ (k + 2) *
        ((nodePolynomial k t).map (algebraMap ℝ ℂ)).eval y) := by
  let last : Fin (k + 4) := ⟨k + 3, by omega⟩
  have h0_mem : (0 : Fin (k + 4)) ∈ Finset.univ := Finset.mem_univ _
  have hlast_ne : last ≠ 0 := by intro h; simp [last, Fin.ext_iff] at h
  have hlast_mem : last ∈ (Finset.univ : Finset (Fin (k + 4))).erase 0 :=
    Finset.mem_erase.mpr ⟨hlast_ne, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase Finset.univ _ h0_mem,
    ← Finset.mul_prod_erase _ _ hlast_mem,
    extendedNodes_zero, extendedNodes_last]
  have hinner : ∏ i ∈ ((Finset.univ : Finset (Fin (k + 4))).erase 0).erase last,
      (y - (extendedNodes k t i : ℂ)) =
      ∏ j : Fin (k + 2), (y - (orderedNode k t j : ℂ)) := by
    refine Finset.prod_bij (fun i hi => ⟨i.val - 1, by
        have h1 : i ≠ last := (Finset.mem_erase.mp hi).1
        have h2 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        have h1v : i.val ≠ k + 3 := fun h => h1 (Fin.ext h)
        have h2v : i.val ≠ 0 := fun h => h2 (Fin.ext h)
        omega⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb hab
      have ha0 : a.val ≠ 0 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1 (Fin.ext h)
      have hb0 : b.val ≠ 0 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1 (Fin.ext h)
      have hv : a.val - 1 = b.val - 1 := congrArg Fin.val hab
      exact Fin.ext (by omega)
    · intro j _
      refine ⟨⟨j.val + 1, by omega⟩, ?_, by simp⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
      · intro h; have := congrArg Fin.val h; dsimp [last] at this; omega
      · intro h; have := congrArg Fin.val h; simp at this
    · intro i hi
      have h1 : i ≠ last := (Finset.mem_erase.mp hi).1
      have h2 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have h1v : i.val ≠ k + 3 := fun h => h1 (Fin.ext h)
      have h2v : i.val ≠ 0 := fun h => h2 (Fin.ext h)
      simp [extendedNodes, h1v, h2v]
  rw [hinner]
  have hpoly : ((monicNodePolynomial k t).map (algebraMap ℝ ℂ)).eval y =
      ∏ j : Fin (k + 2), (y - (orderedNode k t j : ℂ)) := by
    rw [monicNodePolynomial_eq_prod, Polynomial.map_prod, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp
  rw [← hpoly, monicNodePolynomial, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.eval_mul, Polynomial.eval_C]
  push_cast
  ring

/-! ### Chebyshev Joukowsky algebraic identities -/

/-- Second-kind Chebyshev polynomial under the Joukowsky substitution `y = (u + u⁻¹) / 2`. -/
theorem chebyshevU_joukowsky (m : ℕ) {u : ℂ} (hu0 : u ≠ 0) (hu1 : 1 - u ^ 2 ≠ 0) :
    (Polynomial.Chebyshev.U ℂ (m : ℤ)).eval ((u + u⁻¹) / 2) =
      (1 - u ^ (2 * m + 2)) / (u ^ m * (1 - u ^ 2)) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.cast_zero, Polynomial.Chebyshev.U_zero, eval_one, mul_zero, zero_add,
      pow_zero, one_mul]
    field_simp
  | one =>
    simp only [Nat.cast_one, Polynomial.Chebyshev.U_one, eval_mul, eval_ofNat, eval_X,
      mul_one, pow_one]
    field_simp
    ring
  | more m ih0 ih1 =>
    have hrec := congrArg (fun p : ℂ[X] => p.eval ((u + u⁻¹) / 2))
      (Polynomial.Chebyshev.U_add_two ℂ (m : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hrec
    have hm2 : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
    have hm1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    rw [hm2, hrec, ← hm1, ih1, ih0]
    field_simp
    ring

private theorem map_chebyshevU_nat (m : ℕ) :
    (Polynomial.Chebyshev.U ℝ (m : ℤ)).map (algebraMap ℝ ℂ) = Polynomial.Chebyshev.U ℂ (m : ℤ) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [Polynomial.Chebyshev.U_zero]
  | one => simp [Polynomial.Chebyshev.U_one]
  | more m ih0 ih1 =>
    have hm2 : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
    have hm1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    rw [hm2, Polynomial.Chebyshev.U_add_two ℝ (m : ℤ), Polynomial.Chebyshev.U_add_two ℂ (m : ℤ),
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_ofNat,
      Polynomial.map_X, ← hm1, ih1, ih0]

/-- The node polynomial under the Joukowsky substitution `y = (u + u⁻¹) / 2`. -/
theorem nodePolynomial_joukowsky (k : ℕ) (t : ℝ) {u : ℂ} (hu0 : u ≠ 0) (hu1 : 1 - u ^ 2 ≠ 0) :
    ((nodePolynomial k t).map (algebraMap ℝ ℂ)).eval ((u + u⁻¹) / 2) =
      ((1 - (t : ℂ) * u) ^ 2 - u ^ (2 * (k + 1) + 2) * (u - (t : ℂ)) ^ 2) /
        (u ^ (k + 2) * (1 - u ^ 2)) := by
  have hk2 : ((k : ℤ) + 2) = ((k + 2 : ℕ) : ℤ) := by push_cast; ring
  have hk1 : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  unfold nodePolynomial
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    hk2, hk1, map_chebyshevU_nat, eval_add, eval_sub, eval_mul, eval_C]
  rw [chebyshevU_joukowsky (k + 2) hu0 hu1, chebyshevU_joukowsky (k + 1) hu0 hu1,
    chebyshevU_joukowsky k hu0 hu1]
  have e1 : 2 * (k + 2) + 2 = 2 * k + 6 := by omega
  have e2 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  rw [e1, e2]
  simp only [Complex.coe_algebraMap, pow_add, pow_mul]
  push_cast
  field_simp
  ring

/-! ### Partial fraction decomposition via Lagrange interpolation -/

/-- The numerator polynomial `4t (y - t)^(k+2) - 2(1 - t^2)(y - t)^(k+1)`. -/
noncomputable def deltaNumPoly (k : ℕ) (t : ℝ) : ℂ[X] :=
  C (4 * (t : ℂ)) * (X - C (t : ℂ)) ^ (k + 2) -
    C (2 * (1 - (t : ℂ) ^ 2)) * (X - C (t : ℂ)) ^ (k + 1)

theorem deltaNumPoly_eval (k : ℕ) (t : ℝ) (y : ℂ) :
    (deltaNumPoly k t).eval y =
      4 * (t : ℂ) * (y - (t : ℂ)) ^ (k + 2) -
        2 * (1 - (t : ℂ) ^ 2) * (y - (t : ℂ)) ^ (k + 1) := by
  simp [deltaNumPoly]

theorem deltaNumPoly_degree_lt (k : ℕ) (t : ℝ) :
    (deltaNumPoly k t).degree < ((Finset.univ : Finset (Fin (k + 4))).card : WithBot ℕ) := by
  have hm2 : ((X - C (t : ℂ)) ^ (k + 2)).Monic := (monic_X_sub_C _).pow (k + 2)
  have hm1 : ((X - C (t : ℂ)) ^ (k + 1)).Monic := (monic_X_sub_C _).pow (k + 1)
  have hdeg1 : (C (4 * (t : ℂ)) * (X - C (t : ℂ)) ^ (k + 2)).degree ≤ ((k + 2 : ℕ) : WithBot ℕ) := by
    calc (C (4 * (t : ℂ)) * (X - C (t : ℂ)) ^ (k + 2)).degree
        ≤ (C (4 * (t : ℂ))).degree + ((X - C (t : ℂ)) ^ (k + 2)).degree := degree_mul_le _ _
      _ ≤ (0 : WithBot ℕ) + ((k + 2 : ℕ) : WithBot ℕ) := by
          gcongr
          · exact degree_C_le
          · rw [Polynomial.degree_eq_natDegree hm2.ne_zero, natDegree_pow, natDegree_X_sub_C, mul_one]
      _ = ((k + 2 : ℕ) : WithBot ℕ) := by simp
  have hdeg2 : (C (2 * (1 - (t : ℂ) ^ 2)) * (X - C (t : ℂ)) ^ (k + 1)).degree ≤ ((k + 2 : ℕ) : WithBot ℕ) := by
    calc (C (2 * (1 - (t : ℂ) ^ 2)) * (X - C (t : ℂ)) ^ (k + 1)).degree
        ≤ (C (2 * (1 - (t : ℂ) ^ 2))).degree + ((X - C (t : ℂ)) ^ (k + 1)).degree :=
          degree_mul_le _ _
      _ ≤ (0 : WithBot ℕ) + ((k + 1 : ℕ) : WithBot ℕ) := by
          gcongr
          · exact degree_C_le
          · rw [Polynomial.degree_eq_natDegree hm1.ne_zero, natDegree_pow, natDegree_X_sub_C, mul_one]
      _ ≤ ((k + 2 : ℕ) : WithBot ℕ) := by
          rw [zero_add]
          exact_mod_cast (show k + 1 ≤ k + 2 by omega)
  calc (deltaNumPoly k t).degree
      ≤ max _ _ := degree_sub_le _ _
    _ ≤ ((k + 2 : ℕ) : WithBot ℕ) := max_le hdeg1 hdeg2
    _ < ((Finset.univ : Finset (Fin (k + 4))).card : WithBot ℕ) := by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact_mod_cast (show k + 2 < k + 4 by omega)

/-- Real partial-fraction residue at node `i`. -/
noncomputable def nodeResidue (k : ℕ) (t : ℝ) (i : Fin (k + 4)) : ℝ :=
  (4 * t * (extendedNodes k t i - t) ^ (k + 2) -
    2 * (1 - t ^ 2) * (extendedNodes k t i - t) ^ (k + 1)) *
      (∏ j ∈ Finset.univ.erase i, (extendedNodes k t i - extendedNodes k t j))⁻¹

theorem nodeResidue_eq_zero_of_eq (k : ℕ) (t : ℝ) {i : Fin (k + 4)}
    (hi : extendedNodes k t i = t) : nodeResidue k t i = 0 := by
  simp [nodeResidue, hi]

theorem partial_fraction_deltaNumPoly (k : ℕ) {t : ℝ} (ht : |t| < 1) {y : ℂ}
    (hy : ∀ i : Fin (k + 4), y ≠ (extendedNodes k t i : ℂ)) :
    (deltaNumPoly k t).eval y / ∏ i : Fin (k + 4), (y - (extendedNodes k t i : ℂ)) =
      ∑ i : Fin (k + 4), (nodeResidue k t i : ℂ) / (y - (extendedNodes k t i : ℂ)) := by
  let v : Fin (k + 4) → ℂ := fun i => (extendedNodes k t i : ℂ)
  have hv : Set.InjOn v (Finset.univ : Finset (Fin (k + 4))) := by
    intro a _ b _ hab
    exact (extendedNodes_strictMono k ht).injective (Complex.ofReal_injective hab)
  have hlag := Lagrange.eq_interpolate hv (deltaNumPoly_degree_lt k t)
  have heval := congrArg (fun p : ℂ[X] => p.eval y) hlag
  rw [Lagrange.interpolate_apply, eval_finsetSum] at heval
  rw [heval, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, Lagrange.basis, eval_prod]
  have hsplit : ∏ j : Fin (k + 4), (y - v j) =
      (y - v i) * ∏ j ∈ Finset.univ.erase i, (y - v j) :=
    (Finset.mul_prod_erase Finset.univ (fun j => y - v j) (Finset.mem_univ i)).symm
  have hprod_erase_ne : (∏ j ∈ Finset.univ.erase i, (y - v j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hy j)
  have hsub_ne : y - v i ≠ 0 := sub_ne_zero.mpr (hy i)
  have hbasis : (∏ j ∈ Finset.univ.erase i, eval y (Lagrange.basisDivisor (v i) (v j))) =
      (∏ j ∈ Finset.univ.erase i, (y - v j)) / ∏ j ∈ Finset.univ.erase i, (v i - v j) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Lagrange.basisDivisor, div_eq_mul_inv, mul_comm]
  rw [hbasis, hsplit]
  have hnum : (deltaNumPoly k t).eval (v i) *
      (∏ j ∈ Finset.univ.erase i, (v i - v j))⁻¹ = (nodeResidue k t i : ℂ) := by
    rw [deltaNumPoly_eval, nodeResidue]
    push_cast [v]
    rfl
  rw [← hnum]
  change (deltaNumPoly k t).eval (v i) *
      ((∏ j ∈ Finset.univ.erase i, (y - v j)) / ∏ j ∈ Finset.univ.erase i, (v i - v j)) /
      ((y - v i) * ∏ j ∈ Finset.univ.erase i, (y - v j)) =
    (deltaNumPoly k t).eval (v i) * (∏ j ∈ Finset.univ.erase i, (v i - v j))⁻¹ / (y - v i)
  field_simp [hprod_erase_ne, hsub_ne]

/-! ### The vertical chord and its Joukowsky loop `Γ` -/

/-- Vertical chord parameterization `u(v) = t + i v`. -/
noncomputable def uCurve (t v : ℝ) : ℂ := (t : ℂ) + (v : ℂ) * Complex.I

/-- Image of the vertical chord under Joukowsky: `Γ(v) = (u(v) + u(v)⁻¹) / 2`. -/
noncomputable def joukowskyLoop (t v : ℝ) : ℂ := (uCurve t v + (uCurve t v)⁻¹) / 2

/-- Derivative `Γ'(v) = -i (1 - u(v)²) / (2 u(v)²)`. -/
noncomputable def joukowskyLoopDeriv (t v : ℝ) : ℂ :=
  -Complex.I * (1 - (uCurve t v) ^ 2) / (2 * (uCurve t v) ^ 2)

theorem uCurve_ne_zero {t : ℝ} (ht : 0 < t) (v : ℝ) : uCurve t v ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [uCurve] at hre
  linarith

theorem hasDerivAt_uCurve (t v : ℝ) : HasDerivAt (uCurve t) Complex.I v := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 v := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.I) Complex.I v := by
    simpa using h1.mul_const Complex.I
  exact h2.const_add (t : ℂ)

theorem hasDerivAt_joukowskyLoop {t : ℝ} (ht : 0 < t) (v : ℝ) :
    HasDerivAt (joukowskyLoop t) (joukowskyLoopDeriv t v) v := by
  have hu := hasDerivAt_uCurve t v
  have hne := uCurve_ne_zero ht v
  have hinv : HasDerivAt (fun x : ℝ => (uCurve t x)⁻¹) (-Complex.I / (uCurve t v) ^ 2) v :=
    hu.inv hne
  have hsum : HasDerivAt (joukowskyLoop t) ((Complex.I + -Complex.I / (uCurve t v) ^ 2) / 2) v :=
    (hu.add hinv).div_const 2
  have heq : (Complex.I + -Complex.I / (uCurve t v) ^ 2) / 2 = joukowskyLoopDeriv t v := by
    unfold joukowskyLoopDeriv
    field_simp [hne]
    ring
  rwa [heq] at hsum

theorem joukowskyLoop_re {t : ℝ} (ht : 0 < t) (v : ℝ) :
    (joukowskyLoop t v).re = t * (1 + 1 / (t ^ 2 + v ^ 2)) / 2 := by
  have hr : t ^ 2 + v ^ 2 ≠ 0 := by positivity
  simp [joukowskyLoop, uCurve, Complex.normSq_apply]
  field_simp [hr]

theorem joukowskyLoop_im {t : ℝ} (ht : 0 < t) (v : ℝ) :
    (joukowskyLoop t v).im = -v * (1 - (t ^ 2 + v ^ 2)) / (2 * (t ^ 2 + v ^ 2)) := by
  have hr : t ^ 2 + v ^ 2 ≠ 0 := by positivity
  simp [joukowskyLoop, uCurve, Complex.normSq_apply]
  field_simp [hr]
  ring

theorem joukowskyLoop_at_zero {t : ℝ} (ht : 0 < t) :
    joukowskyLoop t 0 = (((t + t⁻¹) / 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [joukowskyLoop_re ht 0, Complex.ofReal_re]
    field_simp [ht.ne']
    ring
  · rw [joukowskyLoop_im ht 0]
    simp

theorem joukowskyLoop_at_endpoint {t v : ℝ} (ht : 0 < t) (hv : t ^ 2 + v ^ 2 = 1) :
    joukowskyLoop t v = (t : ℂ) := by
  apply Complex.ext
  · rw [joukowskyLoop_re ht v, hv]
    simp
    ring
  · rw [joukowskyLoop_im ht v, hv]
    simp

/-! ### Elementary `Complex.log` evaluations and single-pole integrals -/

private theorem log_I_mul_ofReal {r : ℝ} (hr : 0 < r) :
    Complex.log (Complex.I * (r : ℂ)) = (Real.log r : ℂ) + (Real.pi / 2 : ℝ) * Complex.I := by
  have hexp : Complex.exp ((Real.log r : ℂ) + (Real.pi / 2 : ℝ) * Complex.I) =
      Complex.I * (r : ℂ) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr, Complex.exp_mul_I]
    simp
    ring
  rw [← hexp, Complex.log_exp]
  · simp; linarith [Real.pi_pos]
  · simp; linarith [Real.pi_pos]

private theorem log_neg_I_mul_ofReal {r : ℝ} (hr : 0 < r) :
    Complex.log (-Complex.I * (r : ℂ)) = (Real.log r : ℂ) - (Real.pi / 2 : ℝ) * Complex.I := by
  have hexp : Complex.exp ((Real.log r : ℂ) - (Real.pi / 2 : ℝ) * Complex.I) =
      -Complex.I * (r : ℂ) := by
    rw [sub_eq_add_neg, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr,
      show -((Real.pi / 2 : ℝ) * Complex.I) = (-(Real.pi / 2) : ℝ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp
    ring
  rw [← hexp, Complex.log_exp]
  · simp; linarith [Real.pi_pos]
  · simp; linarith [Real.pi_pos]

/-- On `[-a, a]` with `a = √(1 - t²)`, `Γ(v) - z ≠ 0` whenever `z ≠ t` and `z ≤ 1`. -/
theorem joukowskyLoop_sub_ne_zero {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hz1 : z ≤ 1) (hzt : z ≠ t) {v : ℝ} (hv : v ∈ Set.Icc (-Real.sqrt (1 - t ^ 2)) (Real.sqrt (1 - t ^ 2))) :
    joukowskyLoop t v - (z : ℂ) ≠ 0 := by
  have ha_sq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hv_sq : v ^ 2 ≤ 1 - t ^ 2 := by
    rw [← ha_sq]; exact sq_le_sq.mpr (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact abs_le.mpr hv)
  have hr_pos : 0 < t ^ 2 + v ^ 2 := by positivity
  intro hzero
  have hre : (joukowskyLoop t v).re = z := by
    have := congrArg Complex.re hzero; simp at this; linarith
  have him : (joukowskyLoop t v).im = 0 := by
    have := congrArg Complex.im hzero; simp at this; exact this
  rw [joukowskyLoop_im ht0 v] at him
  have hnum : -v * (1 - (t ^ 2 + v ^ 2)) = 0 := by
    have hden : 2 * (t ^ 2 + v ^ 2) ≠ 0 := by positivity
    exact (div_eq_zero_iff.mp him).resolve_right hden
  rcases mul_eq_zero.mp hnum with hv0 | hr1
  · have hvz : v = 0 := by linarith
    rw [hvz, joukowskyLoop_re ht0 0] at hre
    have hgt : 1 < t * (1 + 1 / (t ^ 2 + 0 ^ 2)) / 2 := by
      have : t * (1 + 1 / (t ^ 2 + 0 ^ 2)) / 2 - 1 = (1 - t) ^ 2 / (2 * t) := by
        field_simp [ht0.ne']; ring
      have hpos : 0 < (1 - t) ^ 2 / (2 * t) := by positivity
      linarith
    linarith
  · have hr1' : t ^ 2 + v ^ 2 = 1 := by linarith
    rw [joukowskyLoop_re ht0 v, hr1'] at hre
    have : t * (1 + 1 / 1) / 2 = t := by ring
    exact hzt (by linarith)

/-- Single-pole integral for a pole `z < t` (outside the loop): equals `0`. -/
theorem integral_joukowskyLoop_pole_lt {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hzt : z < t) :
    ∫ v in (-Real.sqrt (1 - t ^ 2))..Real.sqrt (1 - t ^ 2),
      joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)) = 0 := by
  set a := Real.sqrt (1 - t ^ 2)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha_sq : a ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hslit : ∀ v ∈ Set.uIcc (-a) a, joukowskyLoop t v - (z : ℂ) ∈ Complex.slitPlane := by
    intro v hv
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hv
    have hv_sq : v ^ 2 ≤ 1 - t ^ 2 := by
      rw [← ha_sq]; exact sq_le_sq.mpr (by rw [abs_of_nonneg ha0]; exact abs_le.mpr hv)
    have hr_pos : 0 < t ^ 2 + v ^ 2 := by positivity
    have hr_le : t ^ 2 + v ^ 2 ≤ 1 := by linarith
    have hre_ge : t ≤ (joukowskyLoop t v).re := by
      rw [joukowskyLoop_re ht0 v]
      have hinv : 1 ≤ 1 / (t ^ 2 + v ^ 2) := (one_le_div hr_pos).mpr hr_le
      nlinarith
    exact Or.inl (by simp; linarith)
  have hderiv : ∀ v ∈ Set.uIcc (-a) a,
      HasDerivAt (fun x => Complex.log (joukowskyLoop t x - (z : ℂ)))
        (joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ))) v := by
    intro v hv
    have h1 : HasDerivAt (fun x => joukowskyLoop t x - (z : ℂ)) (joukowskyLoopDeriv t v) v :=
      (hasDerivAt_joukowskyLoop ht0 v).sub_const _
    simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using
      (Complex.hasDerivAt_log (hslit v hv)).scomp v h1
  have hcont : ContinuousOn (fun v => joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)))
      (Set.uIcc (-a) a) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · unfold joukowskyLoopDeriv uCurve
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v _ => ?_
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (uCurve_ne_zero ht0 v))
    · refine ContinuousOn.sub ?_ continuousOn_const
      unfold joukowskyLoop uCurve
      refine ContinuousOn.div_const (ContinuousOn.add (by fun_prop) ?_) 2
      exact ContinuousOn.inv₀ (by fun_prop) fun v _ => uCurve_ne_zero ht0 v
    · intro v hv
      exact Complex.slitPlane_ne_zero (hslit v hv)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  rw [joukowskyLoop_at_endpoint ht0 (by linarith [ha_sq]),
    joukowskyLoop_at_endpoint ht0 (by ring_nf; linarith [ha_sq]), sub_self]

/-- Single-pole integral for a pole `t < z ≤ 1` (inside the loop): equals `-2πi`. -/
theorem integral_joukowskyLoop_pole_gt {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hzt : t < z) (hz1 : z ≤ 1) :
    ∫ v in (-Real.sqrt (1 - t ^ 2))..Real.sqrt (1 - t ^ 2),
      joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)) = -2 * (Real.pi : ℂ) * Complex.I := by
  set a := Real.sqrt (1 - t ^ 2)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  have ha_sq : a ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  set p : ℝ := (t + t⁻¹) / 2 - z
  set q : ℝ := z - t
  have hp : 0 < p := by
    have : (t + t⁻¹) / 2 - 1 = (1 - t) ^ 2 / (2 * t) := by field_simp [ht0.ne']; ring
    have hpos : 0 < (1 - t) ^ 2 / (2 * t) := by positivity
    dsimp [p]; linarith
  have hq : 0 < q := sub_pos.mpr hzt
  have hcont_full : ContinuousOn (fun v => joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)))
      (Set.Icc (-a) a) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · unfold joukowskyLoopDeriv uCurve
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v _ => ?_
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (uCurve_ne_zero ht0 v))
    · refine ContinuousOn.sub ?_ continuousOn_const
      unfold joukowskyLoop uCurve
      refine ContinuousOn.div_const (ContinuousOn.add (by fun_prop) ?_) 2
      exact ContinuousOn.inv₀ (by fun_prop) fun v _ => uCurve_ne_zero ht0 v
    · intro v hv
      exact joukowskyLoop_sub_ne_zero ht0 ht1 hz1 hzt.ne' hv
  have hint1 : IntervalIntegrable (fun v => joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)))
      volume (-a) 0 := by
    apply (hcont_full.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc_right ha0.le
  have hint2 : IntervalIntegrable (fun v => joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)))
      volume 0 a := by
    apply (hcont_full.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le ha0.le]
    exact Set.Icc_subset_Icc_left (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  -- Left half `[-a, 0]`: `-i * (Γ(v) - z) ∈ slitPlane`
  have hslit1 : ∀ v ∈ Set.uIcc (-a) 0, -Complex.I * (joukowskyLoop t v - (z : ℂ)) ∈ Complex.slitPlane := by
    intro v hv
    rw [Set.uIcc_of_le (by linarith)] at hv
    have hv_sq : v ^ 2 ≤ 1 - t ^ 2 := by
      rw [← ha_sq]; exact sq_le_sq.mpr (by rw [abs_of_nonneg ha0.le]; exact abs_le.mpr ⟨hv.1, hv.2.trans ha0.le⟩)
    have hr_pos : 0 < t ^ 2 + v ^ 2 := by positivity
    have him_nonneg : 0 ≤ (joukowskyLoop t v).im := by
      rw [joukowskyLoop_im ht0 v]
      have h1 : 0 ≤ -v := by linarith [hv.2]
      have h2 : 0 ≤ 1 - (t ^ 2 + v ^ 2) := by linarith
      exact div_nonneg (mul_nonneg h1 h2) (by positivity)
    rcases him_nonneg.lt_or_eq with hpos | heq
    · exact Or.inl (by simp [hpos])
    · right
      have hne := joukowskyLoop_sub_ne_zero ht0 ht1 hz1 hzt.ne' ⟨hv.1, hv.2.trans ha0.le⟩
      intro him_zero
      apply hne
      apply Complex.ext
      · simp at him_zero ⊢; linarith
      · simp [← heq]
  have hderiv1 : ∀ v ∈ Set.uIcc (-a) 0,
      HasDerivAt (fun x => Complex.log (-Complex.I * (joukowskyLoop t x - (z : ℂ))))
        (joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ))) v := by
    intro v hv
    have h1 : HasDerivAt (fun x => -Complex.I * (joukowskyLoop t x - (z : ℂ)))
        (-Complex.I * joukowskyLoopDeriv t v) v :=
      ((hasDerivAt_joukowskyLoop ht0 v).sub_const _).const_mul (-Complex.I)
    have hcomp := (Complex.hasDerivAt_log (hslit1 v hv)).scomp v h1
    have hne : joukowskyLoop t v - (z : ℂ) ≠ 0 := by
      intro h; exact Complex.slitPlane_ne_zero (hslit1 v hv) (by simp [h])
    have heq : (-Complex.I * joukowskyLoopDeriv t v) •
        (-Complex.I * (joukowskyLoop t v - (z : ℂ)))⁻¹ =
        joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)) := by
      simp only [smul_eq_mul]
      field_simp [hne, Complex.I_ne_zero]
    rwa [heq] at hcomp
  have hI1 : ∫ v in (-a)..0, joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)) =
      Complex.log (-Complex.I * (p : ℂ)) - Complex.log (Complex.I * (q : ℂ)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv1 hint1,
      joukowskyLoop_at_zero ht0,
      joukowskyLoop_at_endpoint ht0 (by ring_nf; linarith [ha_sq])]
    congr 1
    · congr 1; simp [p]
    · congr 1; simp [q]; ring
  -- Right half `[0, a]`: `i * (Γ(v) - z) ∈ slitPlane`
  have hslit2 : ∀ v ∈ Set.uIcc 0 a, Complex.I * (joukowskyLoop t v - (z : ℂ)) ∈ Complex.slitPlane := by
    intro v hv
    rw [Set.uIcc_of_le ha0.le] at hv
    have hv_sq : v ^ 2 ≤ 1 - t ^ 2 := by
      rw [← ha_sq]; exact sq_le_sq.mpr (by rw [abs_of_nonneg ha0.le]; exact abs_le.mpr ⟨(by linarith [ha0, hv.1]), hv.2⟩)
    have hr_pos : 0 < t ^ 2 + v ^ 2 := by positivity
    have him_nonpos : (joukowskyLoop t v).im ≤ 0 := by
      rw [joukowskyLoop_im ht0 v]
      have h1 : -v ≤ 0 := by linarith [hv.1]
      have h2 : 0 ≤ 1 - (t ^ 2 + v ^ 2) := by linarith
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h1 h2) (by positivity)
    rcases him_nonpos.lt_or_eq with hneg | heq
    · exact Or.inl (by simp; linarith)
    · right
      have hne := joukowskyLoop_sub_ne_zero ht0 ht1 hz1 hzt.ne' ⟨by linarith [ha0, hv.1], hv.2⟩
      intro him_zero
      apply hne
      apply Complex.ext
      · simp at him_zero ⊢; linarith
      · simp [heq]
  have hderiv2 : ∀ v ∈ Set.uIcc 0 a,
      HasDerivAt (fun x => Complex.log (Complex.I * (joukowskyLoop t x - (z : ℂ))))
        (joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ))) v := by
    intro v hv
    have h1 : HasDerivAt (fun x => Complex.I * (joukowskyLoop t x - (z : ℂ)))
        (Complex.I * joukowskyLoopDeriv t v) v :=
      ((hasDerivAt_joukowskyLoop ht0 v).sub_const _).const_mul Complex.I
    have hcomp := (Complex.hasDerivAt_log (hslit2 v hv)).scomp v h1
    have hne : joukowskyLoop t v - (z : ℂ) ≠ 0 := by
      intro h; exact Complex.slitPlane_ne_zero (hslit2 v hv) (by simp [h])
    have heq : (Complex.I * joukowskyLoopDeriv t v) •
        (Complex.I * (joukowskyLoop t v - (z : ℂ)))⁻¹ =
        joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)) := by
      simp only [smul_eq_mul]
      field_simp [hne, Complex.I_ne_zero]
    rwa [heq] at hcomp
  have hI2 : ∫ v in (0 : ℝ)..a, joukowskyLoopDeriv t v / (joukowskyLoop t v - (z : ℂ)) =
      Complex.log (-Complex.I * (q : ℂ)) - Complex.log (Complex.I * (p : ℂ)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 hint2,
      joukowskyLoop_at_zero ht0,
      joukowskyLoop_at_endpoint ht0 (by linarith [ha_sq])]
    congr 1
    · congr 1; simp [q]; ring
    · congr 1; simp [p]
  rw [hI1, hI2, log_neg_I_mul_ofReal hp, log_I_mul_ofReal hq,
    log_neg_I_mul_ofReal hq, log_I_mul_ofReal hp]
  push_cast
  ring

/-! ### Algebraic identity on the vertical chord and main theorem -/

private theorem chord_denominators_ne_zero (k : ℕ) {t v : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hv : v ∈ Set.Ioo (-Real.sqrt (1 - t ^ 2)) (Real.sqrt (1 - t ^ 2))) :
    let u := uCurve t v
    u ≠ 0 ∧ 1 - u ^ 2 ≠ 0 ∧ 1 - (t : ℂ) * u ≠ 0 ∧
      1 - u ^ (2 * (k + 1) + 2) * blaschke t u ^ 2 ≠ 0 := by
  have ha_sq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hv_sq : v ^ 2 < 1 - t ^ 2 := by
    have habs : |v| < Real.sqrt (1 - t ^ 2) := abs_lt.mpr hv
    have hsq : |v| ^ 2 < Real.sqrt (1 - t ^ 2) ^ 2 :=
      sq_lt_sq' (by linarith [abs_nonneg v, Real.sqrt_nonneg (1 - t ^ 2)]) habs
    simpa [sq_abs, ha_sq] using hsq
  set u := uCurve t v
  have hnorm_sq : Complex.normSq u < 1 := by
    simp [u, uCurve, Complex.normSq_apply]
    nlinarith
  have hnorm_lt : ‖u‖ < 1 := by
    rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by rw [← Complex.normSq_eq_norm_sq]; exact hnorm_sq)
  have hu0 : u ≠ 0 := uCurve_ne_zero ht0 v
  have hu1 : 1 - u ^ 2 ≠ 0 := by
    intro h
    have h1 : ‖u ^ 2‖ = 1 := by rw [sub_eq_zero.mp h |>.symm]; simp
    rw [norm_pow] at h1
    have : ‖u‖ ^ 2 < 1 ^ 2 := sq_lt_sq' (by linarith [norm_nonneg u]) hnorm_lt
    linarith
  have hden1 : 1 - (t : ℂ) * u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [u, uCurve] at hre
    nlinarith
  have hphi_lt : ‖blaschke t u‖ < 1 := by
    unfold blaschke
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hden1)]
    have hdiff : Complex.normSq (1 - (t : ℂ) * u) - Complex.normSq (u - (t : ℂ)) =
        (1 - t ^ 2) * (1 - Complex.normSq u) := by
      simp [u, uCurve, Complex.normSq_apply]
      ring
    have hpos : 0 < Complex.normSq (1 - (t : ℂ) * u) - Complex.normSq (u - (t : ℂ)) := by
      rw [hdiff]; exact mul_pos (by nlinarith) (by linarith)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hpos
    nlinarith [norm_nonneg (u - (t : ℂ)), norm_nonneg (1 - (t : ℂ) * u)]
  have hden2 : 1 - u ^ (2 * (k + 1) + 2) * blaschke t u ^ 2 ≠ 0 := by
    intro h
    have h1 : ‖u ^ (2 * (k + 1) + 2) * blaschke t u ^ 2‖ = 1 := by
      rw [(sub_eq_zero.mp h).symm]; simp
    rw [norm_mul, norm_pow, norm_pow] at h1
    have hpow1 : ‖u‖ ^ (2 * (k + 1) + 2) < 1 := pow_lt_one₀ (norm_nonneg u) hnorm_lt (by omega)
    have hpow2 : ‖blaschke t u‖ ^ 2 ≤ 1 := by
      have := hphi_lt.le
      nlinarith [norm_nonneg (blaschke t u)]
    have hprod : ‖u‖ ^ (2 * (k + 1) + 2) * ‖blaschke t u‖ ^ 2 < 1 := by
      calc ‖u‖ ^ (2 * (k + 1) + 2) * ‖blaschke t u‖ ^ 2
          ≤ ‖u‖ ^ (2 * (k + 1) + 2) * 1 := mul_le_mul_of_nonneg_left hpow2 (pow_nonneg (norm_nonneg u) _)
        _ < 1 := by linarith
    linarith
  exact ⟨hu0, hu1, hden1, hden2⟩

/-- Pointwise algebraic identity matching the Joukowsky integrand to the vertical-chord integrand. -/
theorem joukowsky_integrand_eq_chord (k : ℕ) {t v : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hv : v ∈ Set.Ioo (-Real.sqrt (1 - t ^ 2)) (Real.sqrt (1 - t ^ 2))) :
    ((deltaNumPoly k t).eval (joukowskyLoop t v) /
      ∏ i : Fin (k + 4), (joukowskyLoop t v - (extendedNodes k t i : ℂ))) *
        joukowskyLoopDeriv t v =
      8 * Complex.I * ((1 - t ^ 2 - v ^ 2 : ℝ) : ℂ) ^ (k + 1) *
        blaschke t (uCurve t v) /
          (1 - (uCurve t v) ^ (2 * (k + 1) + 2) * blaschke t (uCurve t v) ^ 2) := by
  obtain ⟨hu0, hu1, hden1, hden2⟩ := chord_denominators_ne_zero k ht0 ht1 hv
  have hq : 1 - 2 * (t : ℂ) * uCurve t v + (uCurve t v) ^ 2 = ((1 - t ^ 2 - v ^ 2 : ℝ) : ℂ) := by
    simp [uCurve]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [← hq, prod_extendedNodes_eq, joukowskyLoop, nodePolynomial_joukowsky k t hu0 hu1,
    deltaNumPoly_eval, joukowskyLoopDeriv, blaschke]
  generalize uCurve t v = u at hu0 hu1 hden1 hden2 ⊢
  have hden_poly : (1 - (t : ℂ) * u) ^ 2 - u ^ (2 * (k + 1) + 2) * (u - (t : ℂ)) ^ 2 ≠ 0 := by
    intro h
    apply hden2
    unfold blaschke
    rw [div_pow, ← mul_div_assoc, sub_eq_zero, eq_div_iff (pow_ne_zero 2 hden1)]
    linear_combination h
  have hsub : (u + u⁻¹) / 2 - (t : ℂ) = (1 - 2 * (t : ℂ) * u + u ^ 2) / (2 * u) := by
    field_simp [hu0]; ring
  have hsq : ((u + u⁻¹) / 2) ^ 2 - 1 = (1 - u ^ 2) ^ 2 / (4 * u ^ 2) := by
    field_simp [hu0]; ring
  rw [hsub, hsq]
  simp only [div_pow, mul_pow]
  have h2u : (2 : ℂ) * u ≠ 0 := mul_ne_zero (by norm_num) hu0
  field_simp [hu0, hu1, hden1, hden_poly, h2u]
  ring

/-- The Joukowsky loop never hits any real node in `[-1, 1]` on the open chord `(-a, a)`. -/
private theorem joukowskyLoop_ne_real_of_mem_Ioo {t z v : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hz1 : z ≤ 1) (hv : v ∈ Set.Ioo (-Real.sqrt (1 - t ^ 2)) (Real.sqrt (1 - t ^ 2))) :
    joukowskyLoop t v ≠ (z : ℂ) := by
  have ha_sq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have hv_sq : v ^ 2 < 1 - t ^ 2 := by
    have habs : |v| < Real.sqrt (1 - t ^ 2) := abs_lt.mpr hv
    have hsq : |v| ^ 2 < Real.sqrt (1 - t ^ 2) ^ 2 :=
      sq_lt_sq' (by linarith [abs_nonneg v, Real.sqrt_nonneg (1 - t ^ 2)]) habs
    simpa [sq_abs, ha_sq] using hsq
  intro heq
  by_cases hv0 : v = 0
  · rw [hv0, joukowskyLoop_at_zero ht0] at heq
    have hre : (t + t⁻¹) / 2 = z := Complex.ofReal_injective heq
    have hgt : 1 < (t + t⁻¹) / 2 := by
      have : (t + t⁻¹) / 2 - 1 = (1 - t) ^ 2 / (2 * t) := by field_simp [ht0.ne']; ring
      have hpos : 0 < (1 - t) ^ 2 / (2 * t) := by positivity
      linarith
    linarith
  · have him := congrArg Complex.im heq
    rw [joukowskyLoop_im ht0 v, Complex.ofReal_im] at him
    have hden : 2 * (t ^ 2 + v ^ 2) ≠ 0 := by positivity
    have hnum := (div_eq_zero_iff.mp him).resolve_right hden
    have h1 : 1 - (t ^ 2 + v ^ 2) ≠ 0 := by linarith
    have h2 : -v = 0 := (mul_eq_zero.mp hnum).resolve_right h1
    exact hv0 (by linarith)

/-- Core theorem (Claim 5, barycentric form): for all `n = k + 1 ≥ 1` and `t ∈ (0, 1)`,
`barycentricDelta k t = chordDelta (k + 1) t`. -/
theorem barycentricDelta_eq_chordDelta (k : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    barycentricDelta k t = chordDelta (k + 1) t := by
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  set a := Real.sqrt (1 - t ^ 2)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  let g : ℝ → ℂ := fun v =>
    ((1 - t ^ 2 - v ^ 2 : ℝ) : ℂ) ^ (k + 1) *
      (-(blaschke t (uCurve t v))) /
        (1 - (uCurve t v) ^ (2 * (k + 1) + 2) * blaschke t (uCurve t v) ^ 2)
  let hsum : ℝ → ℂ := fun v =>
    ∑ i : Fin (k + 4),
      if extendedNodes k t i = t then 0
      else (nodeResidue k t i : ℂ) * (joukowskyLoopDeriv t v / (joukowskyLoop t v - (extendedNodes k t i : ℂ)))
  -- Step 1: On `(-a, a)`, `-8i * g(v) = hsum(v)`.
  have hpointwise : ∀ v ∈ Set.Ioo (-a) a, -(8 * Complex.I) * g v = hsum v := by
    intro v hv
    have hy : ∀ i : Fin (k + 4), joukowskyLoop t v ≠ (extendedNodes k t i : ℂ) := fun i =>
      joukowskyLoop_ne_real_of_mem_Ioo ht0 ht1 (extendedNodes_mem_Icc k ht_abs i).2 hv
    have h1 := joukowsky_integrand_eq_chord k ht0 ht1 hv
    rw [partial_fraction_deltaNumPoly k ht_abs hy, Finset.sum_mul] at h1
    have h2 : -(8 * Complex.I) * g v =
        8 * Complex.I * ((1 - t ^ 2 - v ^ 2 : ℝ) : ℂ) ^ (k + 1) *
          blaschke t (uCurve t v) /
            (1 - (uCurve t v) ^ (2 * (k + 1) + 2) * blaschke t (uCurve t v) ^ 2) := by
      dsimp [g]; ring
    rw [h2, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases heq : extendedNodes k t i = t
    · rw [if_pos heq, nodeResidue_eq_zero_of_eq k t heq]; simp
    · rw [if_neg heq]; ring
  -- Step 2: Each term of `hsum` is continuous on `[-a, a]`.
  have hterm_cont : ∀ i : Fin (k + 4),
      ContinuousOn (fun v =>
        if extendedNodes k t i = t then (0 : ℂ)
        else (nodeResidue k t i : ℂ) *
          (joukowskyLoopDeriv t v / (joukowskyLoop t v - (extendedNodes k t i : ℂ))))
        (Set.uIcc (-a) a) := by
    intro i
    by_cases heq : extendedNodes k t i = t
    · simp only [heq, ite_true]; exact continuousOn_const
    · simp only [heq, ite_false]
      refine continuousOn_const.mul (ContinuousOn.div ?_ ?_ ?_)
      · unfold joukowskyLoopDeriv uCurve
        refine ContinuousOn.div (by fun_prop) (by fun_prop) fun v _ => ?_
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (uCurve_ne_zero ht0 v))
      · refine ContinuousOn.sub ?_ continuousOn_const
        unfold joukowskyLoop uCurve
        refine ContinuousOn.div_const (ContinuousOn.add (by fun_prop) ?_) 2
        exact ContinuousOn.inv₀ (by fun_prop) fun v _ => uCurve_ne_zero ht0 v
      · intro v hv
        rw [Set.uIcc_of_le (by linarith)] at hv
        exact joukowskyLoop_sub_ne_zero ht0 ht1 (extendedNodes_mem_Icc k ht_abs i).2 heq hv
  -- Step 3: Evaluate `∫ v in (-a)..a, hsum v = -2πi * barycentricDelta k t`.
  have hint_hsum : ∫ v in (-a)..a, hsum v = -2 * (Real.pi : ℂ) * Complex.I * (barycentricDelta k t : ℂ) := by
    dsimp [hsum]
    rw [intervalIntegral.integral_finsetSum fun i _ => (hterm_cont i).intervalIntegrable]
    have hterm_val : ∀ i : Fin (k + 4),
        (∫ v in (-a)..a,
          if extendedNodes k t i = t then (0 : ℂ)
          else (nodeResidue k t i : ℂ) *
            (joukowskyLoopDeriv t v / (joukowskyLoop t v - (extendedNodes k t i : ℂ)))) =
          -2 * (Real.pi : ℂ) * Complex.I *
            if t < extendedNodes k t i then (nodeResidue k t i : ℂ) else 0 := by
      intro i
      by_cases heq : extendedNodes k t i = t
      · simp [heq]
      · simp only [heq, ite_false, intervalIntegral.integral_const_mul]
        rcases lt_or_gt_of_ne heq with hlt | hgt
        · rw [if_neg hlt.not_gt, integral_joukowskyLoop_pole_lt ht0 ht1 hlt, mul_zero, mul_zero]
        · rw [if_pos hgt, integral_joukowskyLoop_pole_gt ht0 ht1 hgt
            (extendedNodes_mem_Icc k ht_abs i).2]
          ring
    simp_rw [hterm_val, ← Finset.mul_sum]
    congr 1
    -- Match the sum over `t < z` with `barycentricDelta k t`
    have hbary : (barycentricDelta k t : ℂ) =
        ∑ i : Fin (k + 4), if t < extendedNodes k t i then (nodeResidue k t i : ℂ) else 0 := by
      unfold barycentricDelta barycentricDividedDifferenceOn
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hgt : t < extendedNodes k t i
      · rw [if_pos hgt]
        simp only [truncatedPower, hgt.le, ite_true, nodeResidue]
        push_cast
        ring
      · rw [if_neg hgt]
        by_cases heq : t = extendedNodes k t i
        · simp [truncatedPower, ← heq]
        · have hlt : ¬ t ≤ extendedNodes k t i := by
            intro hle; exact hgt (lt_of_le_of_ne hle heq)
          simp [truncatedPower, hlt]
    rw [hbary]
  -- Step 4: Replace `hsum` by `-(8i) * g` via a.e. equality on `(-a, a)`.
  have hae : ∀ᵐ v ∂volume, v ∈ Set.uIoc (-a) a → -(8 * Complex.I) * g v = hsum v := by
    have hnull : volume ({a} : Set ℝ) = 0 := Real.volume_singleton
    filter_upwards [compl_mem_ae_iff.mpr hnull] with v hv hv_mem
    rw [Set.uIoc_of_le (by linarith)] at hv_mem
    exact hpointwise v ⟨hv_mem.1, lt_of_le_of_ne hv_mem.2 hv⟩
  have hint_g : ∫ v in (-a)..a, -(8 * Complex.I) * g v =
      -2 * (Real.pi : ℂ) * Complex.I * (barycentricDelta k t : ℂ) := by
    rw [intervalIntegral.integral_congr_ae hae, hint_hsum]
  rw [intervalIntegral.integral_const_mul] at hint_g
  have h8i : -(8 * Complex.I) ≠ 0 := by
    intro h; exact Complex.I_ne_zero ((mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left (by norm_num))
  have hint_g_val : ∫ v in (-a)..a, g v = ((Real.pi / 4 * barycentricDelta k t : ℝ) : ℂ) := by
    apply mul_left_cancel₀ h8i
    rw [hint_g]
    push_cast
    ring
  -- Step 5: Take the real part and fold `[-a, a]` to `[0, a]` by conjugate symmetry!
  have hae_restrict :
      (fun v => -(8 * Complex.I) * g v) =ᵐ[volume.restrict (Set.uIoc (-a) a)] hsum :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr hae
  have hg_int : IntervalIntegrable g volume (-a) a := by
    have hsum_int : IntervalIntegrable hsum volume (-a) a := by
      have h := IntervalIntegrable.sum (s := Finset.univ) (μ := volume) (a := -a) (b := a)
        (f := fun i v => if extendedNodes k t i = t then (0 : ℂ)
          else (nodeResidue k t i : ℂ) *
            (joukowskyLoopDeriv t v / (joukowskyLoop t v - (extendedNodes k t i : ℂ))))
        (fun i _ => (hterm_cont i).intervalIntegrable)
      have heq : (∑ i : Fin (k + 4), fun v => if extendedNodes k t i = t then (0 : ℂ)
          else (nodeResidue k t i : ℂ) *
            (joukowskyLoopDeriv t v / (joukowskyLoop t v - (extendedNodes k t i : ℂ)))) = hsum := by
        funext v
        exact Finset.sum_apply v Finset.univ _
      rwa [heq] at h
    have hmul_int : IntervalIntegrable (fun v => -(8 * Complex.I) * g v) volume (-a) a :=
      hsum_int.congr_ae hae_restrict.symm
    have hinv := hmul_int.const_mul (-(8 * Complex.I))⁻¹
    convert hinv using 1
    funext v
    rw [inv_mul_cancel_left₀ h8i]
  have hre_int : ∫ v in (-a)..a, (g v).re = Real.pi / 4 * barycentricDelta k t := by
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm hg_int
    change ∫ v in (-a)..a, (g v).re = (∫ v in (-a)..a, g v).re at hcomm
    rw [hcomm, hint_g_val, Complex.ofReal_re]
  have hg_even : ∀ v : ℝ, (g (-v)).re = (g v).re := by
    intro v
    have hu_conj : uCurve t (-v) = starRingEnd ℂ (uCurve t v) := by
      apply Complex.ext <;> simp [uCurve]
    have hphi_conj : blaschke t (uCurve t (-v)) = starRingEnd ℂ (blaschke t (uCurve t v)) := by
      rw [hu_conj]
      unfold blaschke
      simp [map_div₀, map_sub, map_mul]
    have hg_conj : g (-v) = starRingEnd ℂ (g v) := by
      dsimp [g]
      rw [hphi_conj, hu_conj]
      have hneg_sq : (-v) ^ 2 = v ^ 2 := neg_sq v
      rw [hneg_sq]
      simp [map_div₀, map_mul, map_sub, map_neg, map_pow]
    rw [hg_conj, Complex.conj_re]
  have hre_integrable : IntervalIntegrable (fun v => (g v).re) volume (-a) a :=
    ⟨Complex.reCLM.integrable_comp hg_int.1, Complex.reCLM.integrable_comp hg_int.2⟩
  have hre_int1 : IntervalIntegrable (fun v => (g v).re) volume (-a) 0 :=
    hre_integrable.mono_set (by
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc_right ha0.le)
  have hre_int2 : IntervalIntegrable (fun v => (g v).re) volume 0 a :=
    hre_integrable.mono_set (by
      rw [Set.uIcc_of_le ha0.le, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc_left (by linarith))
  rw [← intervalIntegral.integral_add_adjacent_intervals hre_int1 hre_int2] at hre_int
  have hleft : ∫ v in (-a)..0, (g v).re = ∫ v in (0 : ℝ)..a, (g v).re := by
    have hcomp := intervalIntegral.integral_comp_neg (f := fun v => (g v).re) (a := -a) (b := 0)
    simp only [neg_zero, neg_neg] at hcomp
    rw [← hcomp]
    exact intervalIntegral.integral_congr fun v _ => (hg_even v).symm
  rw [hleft] at hre_int
  have hhalf : ∫ v in (0 : ℝ)..a, (g v).re = Real.pi / 8 * barycentricDelta k t := by linarith
  have hintegrand : ∀ v : ℝ, (g v).re =
      (1 - t ^ 2 - v ^ 2) ^ (k + 1) *
        ((-(blaschke t ((t : ℂ) + (v : ℂ) * Complex.I))) /
          (1 - ((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * (k + 1) + 2) *
            (blaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2)).re := by
    intro v
    dsimp [g, uCurve]
    rw [mul_div_assoc, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  unfold chordDelta
  have hcongr : (∫ v in (0 : ℝ)..a, (g v).re) =
      ∫ v in (0 : ℝ)..a, (1 - t ^ 2 - v ^ 2) ^ (k + 1) *
        ((-(blaschke t ((t : ℂ) + (v : ℂ) * Complex.I))) /
          (1 - ((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * (k + 1) + 2) *
            (blaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2)).re :=
    intervalIntegral.integral_congr fun v _ => hintegrand v
  rw [← hcongr, hhalf]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]

/-! ### Bridge to `weightedExpSum` and `lawSignMean` -/

/-- The law of a weighted exponential sum is invariant under permutations of its coefficients. -/
private theorem weightedExpSum_perm_aux {xs ys : List ℝ} (h : xs.Perm ys) :
    Probability.weightedExpSum xs = Probability.weightedExpSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [Probability.weightedExpSum, ih]
  | swap x y l =>
    simp only [Probability.weightedExpSum, ← Measure.conv_assoc]
    rw [Measure.conv_comm (Probability.weightedExp y) (Probability.weightedExp x)]
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

private theorem weightedCdfZero_perm_aux {xs ys : List ℝ} (h : xs.Perm ys) :
    Probability.weightedCdfZero xs = Probability.weightedCdfZero ys := by
  simp [Probability.weightedCdfZero, weightedExpSum_perm_aux h]

private theorem barycentricDividedDifferenceOn_fin_erase_zero {m : ℕ}
    (a : Fin (m + 2) → ℝ) (f : ℝ → ℝ) :
    barycentricDividedDifferenceOn (Finset.univ.erase (0 : Fin (m + 2))) a (fun i => f (a i)) =
      barycentricDividedDifferenceOn Finset.univ (fun i : Fin (m + 1) => a i.succ)
        (fun i => f (a i.succ)) := by
  unfold barycentricDividedDifferenceOn
  refine Finset.sum_bij (fun i hi => i.pred (Finset.mem_erase.mp hi).1) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro x hx y hy hxy
    have hx0 := (Finset.mem_erase.mp hx).1
    have hy0 := (Finset.mem_erase.mp hy).1
    have := congrArg Fin.succ hxy
    simpa [Fin.succ_pred] using this
  · intro j _
    exact ⟨j.succ, Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩, Fin.pred_succ j⟩
  · intro i hi
    have hi0 := (Finset.mem_erase.mp hi).1
    dsimp only
    rw [Fin.succ_pred i hi0]
    congr 2
    refine Finset.prod_bij (fun j hj => j.pred (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1)
      ?_ ?_ ?_ ?_
    · intro j hj
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      apply (Finset.mem_erase.mp hj).1
      have := congrArg Fin.succ h
      simpa [Fin.succ_pred] using this
    · intro x hx y hy hxy
      have := congrArg Fin.succ hxy
      simpa [Fin.succ_pred] using this
    · intro j hj
      refine ⟨j.succ, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩⟩,
        Fin.pred_succ j⟩
      intro h
      apply (Finset.mem_erase.mp hj).1
      apply Fin.succ_injective
      simpa [Fin.succ_pred] using h
    · intro j hj
      rw [Fin.succ_pred]

private theorem barycentricDividedDifferenceOn_fin_erase_last {m : ℕ}
    (a : Fin (m + 2) → ℝ) (f : ℝ → ℝ) :
    barycentricDividedDifferenceOn (Finset.univ.erase (Fin.last (m + 1))) a (fun i => f (a i)) =
      barycentricDividedDifferenceOn Finset.univ (fun i : Fin (m + 1) => a i.castSucc)
        (fun i => f (a i.castSucc)) := by
  unfold barycentricDividedDifferenceOn
  refine Finset.sum_bij (fun i hi => i.castPred (Finset.mem_erase.mp hi).1) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro x hx y hy hxy
    have := congrArg Fin.castSucc hxy
    simpa [Fin.castSucc_castPred] using this
  · intro j _
    exact ⟨j.castSucc, Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last j, Finset.mem_univ _⟩,
      Fin.castPred_castSucc⟩
  · intro i hi
    have hil := (Finset.mem_erase.mp hi).1
    dsimp only
    rw [Fin.castSucc_castPred i hil]
    congr 2
    refine Finset.prod_bij (fun j hj => j.castPred (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1)
      ?_ ?_ ?_ ?_
    · intro j hj
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      apply (Finset.mem_erase.mp hj).1
      have := congrArg Fin.castSucc h
      simpa [Fin.castSucc_castPred] using this
    · intro x hx y hy hxy
      have := congrArg Fin.castSucc hxy
      simpa [Fin.castSucc_castPred] using this
    · intro j hj
      refine ⟨j.castSucc, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last j, Finset.mem_univ _⟩⟩,
        Fin.castPred_castSucc⟩
      intro h
      apply (Finset.mem_erase.mp hj).1
      apply Fin.castSucc_injective
      simpa [Fin.castSucc_castPred] using h
    · intro j hj
      rw [Fin.castSucc_castPred]

/-- The closed CDF at zero of `weightedExpSum [t - a 0, ..., t - a m]` equals the
barycentric divided difference of `truncatedPower m t` on strictly increasing nodes `a`. -/
private theorem weightedCdfZero_eq_barycentric_truncatedPower_aux :
    ∀ {m : ℕ} {a : Fin (m + 1) → ℝ}, StrictMono a → ∀ t : ℝ,
      Probability.weightedCdfZero (List.ofFn fun i : Fin (m + 1) => t - a i) =
        barycentricDividedDifferenceOn Finset.univ a (fun i => truncatedPower m t (a i))
  | 0, a, _, t => by
    rw [List.ofFn_succ, List.ofFn_zero]
    have hdd : barycentricDividedDifferenceOn Finset.univ a (fun i => truncatedPower 0 t (a i)) =
        truncatedPower 0 t (a 0) := by
      simp [barycentricDividedDifferenceOn]
    rw [hdd]
    by_cases hle : t ≤ a 0
    · rw [Probability.weightedCdfZero_nonpos _ (by intro c hc; simp at hc; subst hc; linarith)]
      simp [truncatedPower, hle]
    · rw [Probability.weightedCdfZero_nonneg_pos _
        (by intro c hc; simp at hc; subst hc; linarith)
        ⟨t - a 0, by simp, by linarith⟩]
      simp [truncatedPower, hle]
  | m + 1, a, ha, t => by
    by_cases hlo : t ≤ a 0
    · have hall : ∀ i : Fin (m + 2), t ≤ a i := fun i =>
        hlo.trans (ha.monotone (Fin.zero_le i))
      rw [Probability.weightedCdfZero_nonpos _ (by
        intro c hc; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc; linarith [hall i])]
      simpa using (barycentric_truncatedPower_nonneg_side (s := Finset.univ) ha.injective.injOn
        Finset.univ_nonempty t (fun i _ => hall i)).symm
    · by_cases hhi : a (Fin.last (m + 1)) ≤ t
      · have hall : ∀ i : Fin (m + 2), a i ≤ t := fun i =>
          (ha.monotone (Fin.le_last i)).trans hhi
        have hpos : ∃ c ∈ List.ofFn (fun i : Fin (m + 2) => t - a i), 0 < c :=
          ⟨t - a 0, List.mem_ofFn.mpr ⟨0, rfl⟩, by linarith⟩
        rw [Probability.weightedCdfZero_nonneg_pos _ (by
          intro c hc; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc; linarith [hall i]) hpos]
        exact (barycentric_truncatedPower_nonpos_side Finset.univ a (Nat.succ_pos m) t
          (fun i _ => hall i)).symm
      · have ht0 : a 0 < t := lt_of_not_ge hlo
        have ht1 : t < a (Fin.last (m + 1)) := lt_of_not_ge hhi
        let l : ℝ := t - a (Fin.last (m + 1))
        let h : ℝ := t - a 0
        have hl : l < 0 := sub_neg.mpr ht1
        have hh : 0 < h := sub_pos.mpr ht0
        let mid : List ℝ := List.ofFn (fun i : Fin m => t - a i.castSucc.succ)
        have hlast_eq : (Fin.last m).succ = Fin.last (m + 1) := rfl
        have hperm_full : (List.ofFn fun i : Fin (m + 2) => t - a i).Perm (l :: (mid ++ [h])) := by
          rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append, hlast_eq]
          change (h :: (mid ++ [l])).Perm (l :: (mid ++ [h]))
          have p1 : (h :: (mid ++ [l])).Perm ((mid ++ [l]) ++ [h]) :=
            (List.perm_append_singleton h _).symm
          have p2 : ((mid ++ [l]) ++ [h]).Perm (([l] ++ [h]) ++ mid) := by
            rw [List.append_assoc]; exact List.perm_append_comm
          have p3 : (l :: (h :: mid)).Perm (l :: (mid ++ [h])) :=
            List.Perm.cons l (List.perm_append_singleton h mid).symm
          exact (p1.trans p2).trans p3
        have hperm_hi : (List.ofFn fun i : Fin (m + 1) => t - a i.succ).Perm (l :: mid) := by
          rw [List.ofFn_succ', List.concat_eq_append, hlast_eq]
          exact List.perm_append_singleton l mid
        have hperm_lo : (List.ofFn fun i : Fin (m + 1) => t - a i.castSucc).Perm (mid ++ [h]) := by
          rw [List.ofFn_succ]
          have hmid' : (List.ofFn fun i : Fin m => t - a i.succ.castSucc) = mid := by
            dsimp [mid]
          rw [hmid']
          exact (List.perm_append_singleton h mid).symm
        rw [weightedCdfZero_perm_aux hperm_full, Probability.weightedCdfZero_mixed hl hh mid,
          ← weightedCdfZero_perm_aux hperm_hi, ← weightedCdfZero_perm_aux hperm_lo]
        have ha_hi : StrictMono (fun i : Fin (m + 1) => a i.succ) := fun i j hij =>
          ha (Fin.succ_lt_succ_iff.mpr hij)
        have ha_lo : StrictMono (fun i : Fin (m + 1) => a i.castSucc) := fun i j hij =>
          ha (Fin.castSucc_lt_castSucc_iff.mpr hij)
        have h0last : (0 : Fin (m + 2)) < Fin.last (m + 1) := by
          rw [Fin.lt_def]; simp [Fin.last]
        rw [weightedCdfZero_eq_barycentric_truncatedPower_aux ha_hi t,
          weightedCdfZero_eq_barycentric_truncatedPower_aux ha_lo t,
          ← barycentricDividedDifferenceOn_fin_erase_zero,
          ← barycentricDividedDifferenceOn_fin_erase_last,
          barycentric_truncatedPower_erase_pair ha.injective.injOn (Finset.mem_univ 0)
            (Finset.mem_univ (Fin.last (m + 1))) (ha h0last) m t]
        dsimp [l, h]
        ring

/-- The core exponential coefficients `[t - u_0(t), ..., t - u_n(t)]` for order `n = k + 1`. -/
noncomputable def coreCoeffs (k : ℕ) (t : ℝ) : List ℝ :=
  List.ofFn fun i : Fin (k + 2) => t - orderedNode k t i

/-- The full exponential coefficients `[t + 1, t - 1, t - u_0(t), ..., t - u_n(t)]`. -/
noncomputable def fullCoeffs (k : ℕ) (t : ℝ) : List ℝ :=
  (t + 1) :: (t - 1) :: coreCoeffs k t

/-- Claim 5 (probability / sign-mean form): for all `n = k + 1 ≥ 1` and `t ∈ (0, 1)`,
`lawSignMean(Q_t) - lawSignMean(Q_t^0) = chordDelta (k + 1) t`. -/
theorem lawSignMean_diff_eq_chordDelta (k : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Probability.lawSignMean (Probability.weightedExpSum (fullCoeffs k t)) -
        Probability.lawSignMean (Probability.weightedExpSum (coreCoeffs k t)) =
      chordDelta (k + 1) t := by
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have hfull_nz : ∃ c ∈ fullCoeffs k t, c ≠ 0 :=
    ⟨t + 1, by simp [fullCoeffs], by linarith⟩
  have hcore_nz : ∃ c ∈ coreCoeffs k t, c ≠ 0 := by
    by_cases h0 : t - orderedNode k t 0 = 0
    · refine ⟨t - orderedNode k t 1, List.mem_ofFn.mpr ⟨1, rfl⟩, ?_⟩
      have hlt : orderedNode k t 0 < orderedNode k t 1 :=
        orderedNode_strictMono k t (by simp)
      linarith
    · exact ⟨t - orderedNode k t 0, List.mem_ofFn.mpr ⟨0, rfl⟩, h0⟩
  rw [Probability.weightedExpSum_signMean hfull_nz, Probability.weightedExpSum_signMean hcore_nz]
  -- Match `fullCoeffs k t` with `List.ofFn (fun i => t - extendedNodes k t i)` up to permutation.
  have hperm_full : (fullCoeffs k t).Perm (List.ofFn fun i : Fin (k + 4) => t - extendedNodes k t i) := by
    rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append]
    have h0 : t - extendedNodes k t 0 = t + 1 := by rw [extendedNodes_zero]; ring
    have hlast : t - extendedNodes k t (Fin.last (k + 2)).succ = t - 1 := by
      have : (Fin.last (k + 2)).succ = (⟨k + 3, by omega⟩ : Fin (k + 4)) := rfl
      rw [this, extendedNodes_last]
    have hmid : (List.ofFn fun i : Fin (k + 2) => t - extendedNodes k t i.castSucc.succ) =
        coreCoeffs k t := by
      unfold coreCoeffs
      congr 1
      funext i
      have : i.castSucc.succ = (⟨i.val + 1, by omega⟩ : Fin (k + 4)) := rfl
      rw [this, extendedNodes_inner]
    rw [h0, hlast, hmid]
    unfold fullCoeffs
    exact List.Perm.cons (t + 1) (List.perm_append_singleton (t - 1) (coreCoeffs k t)).symm
  rw [weightedCdfZero_perm_aux hperm_full,
    weightedCdfZero_eq_barycentric_truncatedPower_aux (extendedNodes_strictMono k ht_abs) t]
  unfold coreCoeffs
  rw [weightedCdfZero_eq_barycentric_truncatedPower_aux (orderedNode_strictMono k t) t]
  -- Identify the core barycentric divided difference with erasing `0` and `last` from `extendedNodes`.
  let last : Fin (k + 4) := Fin.last (k + 3)
  have hcore_dd :
      barycentricDividedDifferenceOn Finset.univ (orderedNode k t)
        (fun i => truncatedPower (k + 1) t (orderedNode k t i)) =
      barycentricDividedDifferenceOn ((Finset.univ.erase (0 : Fin (k + 4))).erase last)
        (extendedNodes k t) (fun i => truncatedPower (k + 1) t (extendedNodes k t i)) := by
    have h2 := barycentricDividedDifferenceOn_fin_erase_last
      (fun i : Fin (k + 3) => extendedNodes k t i.succ) (truncatedPower (k + 1) t)
    have hinner : (fun i : Fin (k + 2) => extendedNodes k t i.castSucc.succ) = orderedNode k t := by
      funext i
      have : i.castSucc.succ = (⟨i.val + 1, by omega⟩ : Fin (k + 4)) := rfl
      rw [this, extendedNodes_inner]
    rw [← hinner, ← h2]
    unfold barycentricDividedDifferenceOn
    symm
    refine Finset.sum_bij (fun i hi => i.pred (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1)
      ?_ ?_ ?_ ?_
    · intro i hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      apply (Finset.mem_erase.mp hi).1
      have := congrArg Fin.succ h
      simpa [Fin.succ_pred, last] using this
    · intro x hx y hy hxy
      have := congrArg Fin.succ hxy
      simpa [Fin.succ_pred] using this
    · intro j hj
      refine ⟨j.succ, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩⟩,
        Fin.pred_succ j⟩
      intro h
      apply (Finset.mem_erase.mp hj).1
      have : j.succ = (Fin.last (k + 2)).succ := by simpa [last] using h
      exact Fin.succ_injective _ this
    · intro i hi
      dsimp only
      rw [Fin.succ_pred]
      congr 2
      refine Finset.prod_bij (fun j hj => j.pred
        (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2).1) ?_ ?_ ?_ ?_
      · intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        have hjl := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
        · intro h; apply hji; have := congrArg Fin.succ h; simpa [Fin.succ_pred] using this
        · intro h; apply hjl; have := congrArg Fin.succ h; simpa [Fin.succ_pred, last] using this
      · intro x hx y hy hxy
        have := congrArg Fin.succ hxy
        simpa [Fin.succ_pred] using this
      · intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        have hjl := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        refine ⟨j.succ, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
          Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩⟩⟩, Fin.pred_succ j⟩
        · intro h; apply hji; apply Fin.succ_injective; simpa [Fin.succ_pred] using h
        · intro h; apply hjl; have : j.succ = (Fin.last (k + 2)).succ := by simpa [last] using h
          exact Fin.succ_injective _ this
      · intro j hj
        rw [Fin.succ_pred]
  rw [hcore_dd,
    barycentric_truncatedPower_erase_endpoints (extendedNodes_strictMono k ht_abs).injective.injOn
      (Finset.mem_univ 0) (Finset.mem_univ last) (extendedNodes_zero k t)
      (by exact extendedNodes_last k t) (k + 1) t]
  rw [← barycentricDelta_eq_chordDelta k ht0 ht1]
  unfold barycentricDelta
  ring

end SharpL1.Analysis
