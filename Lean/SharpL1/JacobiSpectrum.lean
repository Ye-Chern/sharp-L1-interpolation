module

public import SharpL1.Jacobi
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic.NormNum

public section

namespace SharpL1

/-- A Jacobi eigenvector whose first component vanishes must be zero. -/
theorem jacobi_eigenvector_eq_zero_of_head_eq_zero (k : ℕ) (t μ : ℝ)
    (v : Fin (k + 2) → ℝ)
    (hv : (jacobiMatrix k t).mulVec v = μ • v) (h0 : v 0 = 0) : v = 0 := by
  have h : ∀ m : ℕ, ∀ hm : m < k + 2, v ⟨m, hm⟩ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm
      cases m with
      | zero => simpa using h0
      | succ m =>
        let i : Fin (k + 2) := ⟨m, by omega⟩
        let j : Fin (k + 2) := ⟨m + 1, hm⟩
        have hi : v i = 0 := ih m (by omega) (by omega)
        have hsum : ((jacobiMatrix k t).mulVec v) i = (1 / 2 : ℝ) * v j := by
          rw [Matrix.mulVec_apply_eq_sum, Finset.sum_eq_single j]
          · simp [jacobiMatrix, i, j]
          · intro b _ hb
            by_cases hle : b.val ≤ m
            · have hz : v b = 0 := ih b.val (by omega) b.isLt
              rw [hz, mul_zero]
            · have hne : b.val ≠ m + 1 := by
                intro heq
                apply hb
                apply Fin.ext
                simpa [j] using heq
              have hneq : m ≠ b.val := by omega
              have hfar : ¬(m + 1 = b.val ∨ b.val + 1 = m) := by omega
              simp [jacobiMatrix, i, hneq, hfar]
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
        have he := congrFun hv i
        rw [hsum] at he
        simp only [Pi.smul_apply, smul_eq_mul, hi, mul_zero] at he
        have hj0 : v j = 0 := (mul_eq_zero.mp he).resolve_left (by norm_num)
        exact hj0
  funext i
  exact h i.val i.isLt



/-- Two eigenvectors for the same eigenvalue agree if their first coordinates agree. -/
theorem jacobi_eigenvector_head_injective (k : ℕ) (t μ : ℝ)
    (v w : Fin (k + 2) → ℝ)
    (hv : (jacobiMatrix k t).mulVec v = μ • v)
    (hw : (jacobiMatrix k t).mulVec w = μ • w)
    (h0 : v 0 = w 0) : v = w := by
  have hdiff : (jacobiMatrix k t).mulVec (v - w) = μ • (v - w) := by
    rw [Matrix.mulVec_sub, hv, hw, smul_sub]
  have hz := jacobi_eigenvector_eq_zero_of_head_eq_zero k t μ (v - w) hdiff (by
    simp [h0])
  exact sub_eq_zero.mp hz

/-- Every eigenspace of the real Jacobi matrix has dimension at most one. -/
theorem jacobi_eigenspace_finrank_le_one (k : ℕ) (t μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace ((jacobiMatrix k t).mulVecLin) μ) ≤ 1 := by
  let E := Module.End.eigenspace ((jacobiMatrix k t).mulVecLin) μ
  let f : E →ₗ[ℝ] ℝ := (LinearMap.proj 0).comp E.subtype
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply jacobi_eigenvector_head_injective k t μ
    · exact Module.End.mem_eigenspace_iff.mp v.property
    · exact Module.End.mem_eigenspace_iff.mp w.property
    · exact h
  simpa using LinearMap.finrank_le_finrank_of_injective hf



theorem jacobi_isHermitian (k : ℕ) (t : ℝ) : (jacobiMatrix k t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  by_cases h : i = j
  · subst j
    rfl
  · have hv : i.val ≠ j.val := fun h' => h (Fin.ext h')
    simp [jacobiMatrix, hv, hv.symm, or_comm]

theorem jacobi_eigenvalues_injective (k : ℕ) (t : ℝ) :
    Function.Injective (jacobi_isHermitian k t).eigenvalues := by
  let hA := jacobi_isHermitian k t
  let v : Fin (k + 2) → (Fin (k + 2) → ℝ) := fun i => ⇑(hA.eigenvectorBasis i)
  let e := WithLp.linearEquiv 2 ℝ (Fin (k + 2) → ℝ)
  have li : LinearIndependent ℝ v := by
    have h := hA.eigenvectorBasis.toBasis.linearIndependent.map' e.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.injective)
    exact h
  have hv (i : Fin (k + 2)) :
      (jacobiMatrix k t).mulVec (v i) = hA.eigenvalues i • v i :=
    hA.mulVec_eigenvectorBasis i
  have hn (i : Fin (k + 2)) : v i 0 ≠ 0 := by
    intro hz
    have hvzero := jacobi_eigenvector_eq_zero_of_head_eq_zero k t (hA.eigenvalues i)
      (v i) (hv i) hz
    exact (li.ne_zero i) hvzero
  intro i j hij
  have hsame : (v j 0) • v i = (v i 0) • v j := by
    apply jacobi_eigenvector_head_injective k t (hA.eigenvalues i)
    · rw [Matrix.mulVec_smul, hv i]
      simp only [smul_smul, mul_comm]
    · rw [Matrix.mulVec_smul, hv j, ← hij]
      simp only [smul_smul, mul_comm]
    · simp [smul_eq_mul, mul_comm]
  exact li.eq_of_smul_apply_eq_smul_apply (v j 0) (v i 0) i j (hn j) hsame

theorem jacobi_charpoly_roots_nodup (k : ℕ) (t : ℝ) :
    (jacobiMatrix k t).charpoly.roots.Nodup := by
  rw [(jacobi_isHermitian k t).roots_charpoly_eq_eigenvalues]
  apply (Multiset.nodup_map_iff_of_injective ?_).2
  · exact Finset.univ.nodup
  · simpa using jacobi_eigenvalues_injective k t

theorem nodePolynomial_roots_nodup (k : ℕ) (t : ℝ) :
    (nodePolynomial k t).roots.Nodup := by
  have h := jacobi_charpoly_roots_nodup k t
  rw [jacobi_charpoly, Polynomial.roots_C_mul _ (by positivity)] at h
  exact h



/-- Positive parameter direction of the core pencil tI − J(t). -/
@[expose] noncomputable def jacobiPencilD (k : ℕ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ :=
  Matrix.diagonal fun i => if i.val = 0 ∨ i.val + 1 = k + 2 then 1 / 2 else 1

theorem jacobi_pencil_affine (k : ℕ) (t : ℝ) :
    t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t =
      t • jacobiPencilD k - jacobiMatrix k 0 := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      mul_one, jacobiPencilD, Matrix.diagonal_apply_eq, jacobiMatrix, if_true, zero_div]
    split_ifs <;> ring
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [jacobiPencilD, jacobiMatrix, hij, hv, smul_eq_mul]

theorem jacobiPencilD_diag_bounds (k : ℕ) (i : Fin (k + 2)) :
    0 < jacobiPencilD k i i ∧ jacobiPencilD k i i ≤ 1 := by
  simp only [jacobiPencilD, Matrix.diagonal_apply_eq]
  split_ifs <;> norm_num

/-- The real characteristic polynomial splits completely. -/
theorem jacobi_charpoly_splits (k : ℕ) (t : ℝ) :
    (jacobiMatrix k t).charpoly.Splits :=
  (jacobi_isHermitian k t).splits_charpoly

/-- The unnormalized node polynomial has only real roots. -/
theorem nodePolynomial_splits (k : ℕ) (t : ℝ) : (nodePolynomial k t).Splits := by
  have h := jacobi_charpoly_splits k t
  rw [jacobi_charpoly, Polynomial.splits_mul_iff_right (by simp) (Polynomial.Splits.C _)] at h
  exact h

/-- Counting multiplicity, there are exactly k+2 real roots. -/
theorem nodePolynomial_card_roots (k : ℕ) (t : ℝ) :
    (nodePolynomial k t).roots.card = k + 2 := by
  rw [← (nodePolynomial_splits k t).natDegree_eq_card_roots, natDegree_nodePolynomial]

end SharpL1
