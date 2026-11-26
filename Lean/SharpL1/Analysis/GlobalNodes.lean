module

public import SharpL1.JacobiOrdered
public import SharpL1.JacobiSymmetry
public import SharpL1.JacobiContainment
public import SharpL1.Analysis.OrderedNodeCurves
public import SharpL1.Analysis.NodeWeights
public import SharpL1.RootBrackets
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Comp

public section

/-!
# Global ordered Jacobi nodes on the closed interval [-1, 1]

This module extends the interior node curves from `OrderedNodeCurves` to the full
closed interval `[-1, 1]` for order `n = k + 1`:
1. `continuous_orderedNode` (and endpoint continuity at `t = ±1`).
2. Reflection symmetry `orderedNode k (-t) j = -orderedNode k t j.rev` and speed symmetry.
3. Exact endpoint values `orderedNode k (-1) j = chebyshevGrid k j.val`,
   `orderedNode k 1 j = chebyshevGrid k (j.val + 1)`, and center value `orderedNode k 0 j`.
4. Strict monotonicity on `[-1, 1]` and bijection `[-1, 1] → [r_j, r_{j+1}]`.
-/

namespace SharpL1

open Polynomial Filter Set Topology
open Polynomial.Chebyshev (U)

/-- The Chebyshev-U partition points `r_j = -cos(j * π / (n + 1))` for order `n = k + 1`
(so `n + 1 = k + 2` and `j = 0, ..., k + 2`). -/
@[expose] noncomputable def chebyshevGrid (k j : ℕ) : ℝ :=
  -Real.cos ((j : ℝ) * Real.pi / ((k : ℝ) + 2))

@[simp]
theorem chebyshevGrid_zero (k : ℕ) : chebyshevGrid k 0 = -1 := by
  simp [chebyshevGrid]

@[simp]
theorem chebyshevGrid_last (k : ℕ) : chebyshevGrid k (k + 2) = 1 := by
  have hk : (k : ℝ) + 2 ≠ 0 := by positivity
  simp only [chebyshevGrid, Nat.cast_add, Nat.cast_ofNat]
  rw [mul_div_cancel_left₀ _ hk, Real.cos_pi]
  norm_num

theorem chebyshevGrid_reflect (k j : ℕ) (hj : j ≤ k + 2) :
    chebyshevGrid k (k + 2 - j) = -chebyshevGrid k j := by
  have hk : (k : ℝ) + 2 ≠ 0 := by positivity
  simp only [chebyshevGrid]
  have hcast : ((k + 2 - j : ℕ) : ℝ) = (k : ℝ) + 2 - (j : ℝ) := by
    rw [Nat.cast_sub hj]
    push_cast
    ring
  rw [hcast, sub_mul, sub_div, mul_div_cancel_left₀ _ hk, Real.cos_pi_sub]

theorem chebyshevGrid_lt_of_lt {k i j : ℕ} (hij : i < j) (hj : j ≤ k + 2) :
    chebyshevGrid k i < chebyshevGrid k j := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hi0 : 0 ≤ (i : ℝ) * Real.pi / ((k : ℝ) + 2) := by positivity
  have hjpi : (j : ℝ) * Real.pi / ((k : ℝ) + 2) ≤ Real.pi := by
    rw [div_le_iff₀ hk]
    have hj' : (j : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast hj
    nlinarith [Real.pi_pos]
  have hlt : (i : ℝ) * Real.pi / ((k : ℝ) + 2) < (j : ℝ) * Real.pi / ((k : ℝ) + 2) := by
    gcongr
  have hcos := Real.strictAntiOn_cos ⟨hi0, (hlt.le.trans hjpi)⟩ ⟨hi0.trans hlt.le, hjpi⟩ hlt
  simpa only [chebyshevGrid] using neg_lt_neg hcos

theorem chebyshevGrid_strictMono (k : ℕ) :
    StrictMono (fun j : Fin (k + 3) => chebyshevGrid k j.val) :=
  fun _ j hij => chebyshevGrid_lt_of_lt hij (Nat.lt_succ_iff.mp j.isLt)

theorem chebyshevGrid_mem_Icc (k j : ℕ) (hj : j ≤ k + 2) :
    chebyshevGrid k j ∈ Set.Icc (-1 : ℝ) 1 := by
  let jf : Fin (k + 3) := ⟨j, by omega⟩
  have h0 : chebyshevGrid k 0 ≤ chebyshevGrid k j := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact le_rfl
    · exact (chebyshevGrid_strictMono k (show (0 : Fin (k + 3)) < jf by simpa [Fin.lt_def, jf])).le
  have h1 : chebyshevGrid k j ≤ chebyshevGrid k (k + 2) := by
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact le_rfl
    · exact (chebyshevGrid_strictMono k (show jf < ⟨k + 2, by omega⟩ by simpa [Fin.lt_def, jf])).le
  rw [chebyshevGrid_zero] at h0
  rw [chebyshevGrid_last] at h1
  exact ⟨h0, h1⟩

/-- Reflection symmetry of the globally ordered nodes: `u_j(-t) = -u_{n-j}(t)`. -/
theorem orderedNode_neg (k : ℕ) (t : ℝ) (j : Fin (k + 2)) :
    orderedNode k (-t) j = -orderedNode k t j.rev := by
  let u : Fin (k + 2) → ℝ := fun i => -orderedNode k t i.rev
  have hu_mono : StrictMono u := by
    intro a b hab
    dsimp [u]
    exact neg_lt_neg (orderedNode_strictMono k t (Fin.rev_lt_rev.mpr hab))
  have hS : ∀ x ∈ Finset.univ.image u, (nodePolynomial k (-t)).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact (nodePolynomial_isRoot_reflect k t (orderedNode k t i.rev)).mpr
      (orderedNode_eval_eq_zero k t i.rev)
  have hcard : (nodePolynomial k (-t)).natDegree ≤ (Finset.univ.image u).card := by
    rw [natDegree_nodePolynomial, Finset.card_image_of_injective Finset.univ hu_mono.injective]
    simp
  have hroots : (nodePolynomial k (-t)).roots = (Finset.univ.image u).val :=
    roots_eq_of_natDegree_le_card_of_ne_zero hS hcard (nodePolynomial_ne_zero k (-t))
  exact congrFun (orderedNode_eq_of_strictMono_of_roots k (-t) u hu_mono hroots) j

/-- Reflection symmetry with explicit `k + 1 - j.val` index. -/
theorem orderedNode_neg_sub (k : ℕ) (t : ℝ) (j : Fin (k + 2)) :
    orderedNode k (-t) j = -orderedNode k t ⟨k + 1 - j.val, by omega⟩ := by
  rw [orderedNode_neg]
  congr 2
  ext
  simp [Fin.val_rev]

/-- Exact values of the ordered nodes at `t = -1`: `u_j(-1) = r_j`. -/
theorem orderedNode_neg_one (k : ℕ) (j : Fin (k + 2)) :
    orderedNode k (-1) j = chebyshevGrid k j.val := by
  let u : Fin (k + 2) → ℝ := fun i => chebyshevGrid k i.val
  have hu_mono : StrictMono u := by
    intro a b hab
    exact chebyshevGrid_lt_of_lt hab (by omega)
  have hS : ∀ x ∈ Finset.univ.image u, (nodePolynomial k (-1)).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    rw [nodePolynomial_neg_one]
    simp only [eval_mul, eval_ofNat, eval_add, eval_X, eval_one]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · simp [u, hi0]
    · apply mul_eq_zero_of_right
      let m : ℕ := k + 1 - i.val
      have hm : m < k + 1 := by omega
      have hU := Polynomial.Chebyshev.roots_U_real (k + 1)
      have hmem : Real.cos ((m + 1 : ℕ) * Real.pi / ((k + 1 : ℕ) + 1)) ∈
          (U ℝ ((k + 1 : ℕ) : ℤ)).roots := by
        rw [hU, Finset.mem_val, Finset.mem_image]
        exact ⟨m, Finset.mem_range.mpr hm, by push_cast; rfl⟩
      have hroot : (U ℝ ((k : ℤ) + 1)).eval
          (Real.cos ((m + 1 : ℕ) * Real.pi / ((k + 1 : ℕ) + 1))) = 0 := by
        have hne : U ℝ ((k + 1 : ℕ) : ℤ) ≠ 0 :=
          Polynomial.Chebyshev.U_ne_zero ℝ ((k + 1 : ℕ) : ℤ) (by omega)
        have hr := (Polynomial.mem_roots hne).mp hmem
        simpa [Nat.cast_add, Nat.cast_one] using hr
      have hcos : Real.cos ((m + 1 : ℕ) * Real.pi / ((k + 1 : ℕ) + 1)) = u i := by
        have hk : (k : ℝ) + 2 ≠ 0 := by positivity
        have hcast : ((m + 1 : ℕ) : ℝ) = (k : ℝ) + 2 - (i.val : ℝ) := by
          have : m + 1 = k + 2 - i.val := by omega
          rw [this, Nat.cast_sub (by omega : i.val ≤ k + 2)]
          push_cast
          ring
        have hden : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by push_cast; ring
        rw [hcast, hden, sub_mul, sub_div, mul_div_cancel_left₀ _ hk, Real.cos_pi_sub]
        rfl
      rwa [← hcos]
  have hcard : (nodePolynomial k (-1)).natDegree ≤ (Finset.univ.image u).card := by
    rw [natDegree_nodePolynomial, Finset.card_image_of_injective Finset.univ hu_mono.injective]
    simp
  have hroots : (nodePolynomial k (-1)).roots = (Finset.univ.image u).val :=
    roots_eq_of_natDegree_le_card_of_ne_zero hS hcard (nodePolynomial_ne_zero k (-1))
  exact congrFun (orderedNode_eq_of_strictMono_of_roots k (-1) u hu_mono hroots) j

/-- Exact values of the ordered nodes at `t = 1`: `u_j(1) = r_{j+1}`. -/
theorem orderedNode_one (k : ℕ) (j : Fin (k + 2)) :
    orderedNode k 1 j = chebyshevGrid k (j.val + 1) := by
  have h1 : (1 : ℝ) = -(-1) := by norm_num
  rw [h1, orderedNode_neg, orderedNode_neg_one]
  simp only [Fin.val_rev]
  have hj : j.val + 1 ≤ k + 2 := by omega
  rw [chebyshevGrid_reflect k (j.val + 1) hj, neg_neg]

/-- Exact values of the ordered nodes at `t = 0`: zeros of `U_{k+2}`. -/
theorem orderedNode_zero (k : ℕ) (j : Fin (k + 2)) :
    orderedNode k 0 j = -Real.cos (((j.val : ℝ) + 1) * Real.pi / ((k : ℝ) + 3)) := by
  let u : Fin (k + 2) → ℝ :=
    fun i => -Real.cos (((i.val : ℝ) + 1) * Real.pi / ((k : ℝ) + 3))
  have hu_mono : StrictMono u := by
    intro a b hab
    have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    have ha0 : 0 ≤ ((a.val : ℝ) + 1) * Real.pi / ((k : ℝ) + 3) := by positivity
    have hbpi : ((b.val : ℝ) + 1) * Real.pi / ((k : ℝ) + 3) ≤ Real.pi := by
      rw [div_le_iff₀ hk]
      have hb : (b.val : ℝ) + 1 ≤ (k : ℝ) + 3 := by
        exact_mod_cast (show b.val + 1 ≤ k + 3 by omega)
      nlinarith [Real.pi_pos]
    have hlt : ((a.val : ℝ) + 1) * Real.pi / ((k : ℝ) + 3) <
        ((b.val : ℝ) + 1) * Real.pi / ((k : ℝ) + 3) := by
      gcongr
      exact_mod_cast hab
    have hcos := Real.strictAntiOn_cos ⟨ha0, hlt.le.trans hbpi⟩ ⟨ha0.trans hlt.le, hbpi⟩ hlt
    exact neg_lt_neg hcos
  have hS : ∀ x ∈ Finset.univ.image u, (nodePolynomial k 0).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    rw [nodePolynomial_zero]
    let m : ℕ := k + 1 - i.val
    have hm : m < k + 2 := by omega
    have hU := Polynomial.Chebyshev.roots_U_real (k + 2)
    have hmem : Real.cos ((m + 1 : ℕ) * Real.pi / ((k + 2 : ℕ) + 1)) ∈
        (U ℝ ((k + 2 : ℕ) : ℤ)).roots := by
      rw [hU, Finset.mem_val, Finset.mem_image]
      exact ⟨m, Finset.mem_range.mpr hm, by push_cast; rfl⟩
    have hroot : (U ℝ ((k : ℤ) + 2)).eval
        (Real.cos ((m + 1 : ℕ) * Real.pi / ((k + 2 : ℕ) + 1))) = 0 := by
      have hne : U ℝ ((k + 2 : ℕ) : ℤ) ≠ 0 :=
        Polynomial.Chebyshev.U_ne_zero ℝ ((k + 2 : ℕ) : ℤ) (by omega)
      have hr := (Polynomial.mem_roots hne).mp hmem
      simpa [Nat.cast_add, Nat.cast_ofNat] using hr
    have hcos : Real.cos ((m + 1 : ℕ) * Real.pi / ((k + 2 : ℕ) + 1)) = u i := by
      have hk : (k : ℝ) + 3 ≠ 0 := by positivity
      have hcast : ((m + 1 : ℕ) : ℝ) = (k : ℝ) + 3 - ((i.val : ℝ) + 1) := by
        have : m + 1 = k + 3 - (i.val + 1) := by omega
        rw [this, Nat.cast_sub (by omega : i.val + 1 ≤ k + 3)]
        push_cast
        ring
      have hden : (((k + 2 : ℕ) : ℝ) + 1) = (k : ℝ) + 3 := by push_cast; ring
      rw [hcast, hden, sub_mul, sub_div, mul_div_cancel_left₀ _ hk, Real.cos_pi_sub]
    rwa [← hcos]
  have hcard : (nodePolynomial k 0).natDegree ≤ (Finset.univ.image u).card := by
    rw [natDegree_nodePolynomial, Finset.card_image_of_injective Finset.univ hu_mono.injective]
    simp
  have hroots : (nodePolynomial k 0).roots = (Finset.univ.image u).val :=
    roots_eq_of_natDegree_le_card_of_ne_zero hS hcard (nodePolynomial_ne_zero k 0)
  exact congrFun (orderedNode_eq_of_strictMono_of_roots k 0 u hu_mono hroots) j

/-- Every `orderedNode k · j` is continuous on all of `ℝ` (including the endpoints `±1`). -/
theorem continuous_orderedNode (k : ℕ) (j : Fin (k + 2)) :
    Continuous (fun t => orderedNode k t j) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  let y : Fin (k + 2) → ℝ := orderedNode k t
  have hy_mono : StrictMono y := orderedNode_strictMono k t
  let cand : Finset ℝ :=
    ({ε} : Finset ℝ) ∪
      ((Finset.univ.product Finset.univ).filter (fun p : Fin (k + 2) × Fin (k + 2) => p.1 < p.2)).image
        (fun p => (y p.2 - y p.1) / 3)
  have hcand_pos : ∀ c ∈ cand, 0 < c := by
    intro c hc
    simp only [cand, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_filter] at hc
    rcases hc with rfl | ⟨⟨a, b⟩, hab, rfl⟩
    · exact hε
    · exact div_pos (sub_pos.mpr (hy_mono hab.2)) (by norm_num)
  have hcand_ne : cand.Nonempty := ⟨ε, by simp [cand]⟩
  let ε' : ℝ := cand.min' hcand_ne
  have hε'_pos : 0 < ε' := hcand_pos ε' (Finset.min'_mem cand hcand_ne)
  have hε'_le : ε' ≤ ε := Finset.min'_le cand ε (by simp [cand])
  have hsep : ∀ a b : Fin (k + 2), a < b → y a + ε' < y b - ε' := by
    intro a b hab
    have hle : ε' ≤ (y b - y a) / 3 := by
      apply Finset.min'_le cand
      simp only [cand, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      right
      exact ⟨(a, b), ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hab⟩, rfl⟩
    linarith
  have hroots_y : (nodePolynomial k t).roots = Finset.univ.val.map y := by
    have h1 : (List.ofFn y : Multiset ℝ) = (nodePolynomial k t).roots := by
      rw [orderedNode_ofFn]
      simp [Multiset.sort_eq]
    rw [← h1, ← Fin.univ_val_map]
  have heval_prod (x : ℝ) :
      (nodePolynomial k t).eval x =
        (nodePolynomial k t).leadingCoeff * ∏ i : Fin (k + 2), (x - y i) := by
    rw [(nodePolynomial_splits k t).eval_eq_prod_roots, hroots_y, Multiset.map_map]
    congr 1
  have hsign_t : ∀ i : Fin (k + 2),
      (nodePolynomial k t).eval (y i - ε') * (nodePolynomial k t).eval (y i + ε') < 0 := by
    intro i
    rw [heval_prod (y i - ε'), heval_prod (y i + ε')]
    have hprod_eq :
        ((nodePolynomial k t).leadingCoeff * ∏ l : Fin (k + 2), (y i - ε' - y l)) *
          ((nodePolynomial k t).leadingCoeff * ∏ l : Fin (k + 2), (y i + ε' - y l)) =
        (nodePolynomial k t).leadingCoeff ^ 2 *
          ∏ l : Fin (k + 2), ((y i - ε' - y l) * (y i + ε' - y l)) := by
      rw [Finset.prod_mul_distrib]
      ring
    rw [hprod_eq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hself : (y i - ε' - y i) * (y i + ε' - y i) = -(ε' ^ 2) := by ring
    have hrest : 0 < ∏ l ∈ Finset.univ.erase i, ((y i - ε' - y l) * (y i + ε' - y l)) := by
      apply Finset.prod_pos
      intro l hl
      have hne : l ≠ i := (Finset.mem_erase.mp hl).1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hs := hsep l i hlt
        exact mul_pos (by linarith) (by linarith)
      · have hs := hsep i l hgt
        exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hlc : 0 < (nodePolynomial k t).leadingCoeff ^ 2 :=
      sq_pos_iff.mpr (leadingCoeff_ne_zero.mpr (nodePolynomial_ne_zero k t))
    have hneg : -(ε' ^ 2) * ∏ l ∈ Finset.univ.erase i, ((y i - ε' - y l) * (y i + ε' - y l)) < 0 :=
      mul_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos hε'_pos)) hrest
    rw [hself]
    exact mul_neg_of_pos_of_neg hlc hneg
  have hcont_eval (x : ℝ) : Continuous (fun s => (nodePolynomial k s).eval x) := by
    have hfun : (fun s => (nodePolynomial k s).eval x) =
        fun s => (U ℝ ((k : ℤ) + 2)).eval x - 2 * s * (U ℝ ((k : ℤ) + 1)).eval x +
          s ^ 2 * (U ℝ k).eval x := by
      funext s
      simp [nodePolynomial]
    rw [hfun]
    fun_prop
  have hev_sign : ∀ᶠ s in 𝓝 t, ∀ i : Fin (k + 2),
      (nodePolynomial k s).eval (y i - ε') * (nodePolynomial k s).eval (y i + ε') < 0 := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hc : Continuous (fun s =>
        (nodePolynomial k s).eval (y i - ε') * (nodePolynomial k s).eval (y i + ε')) :=
      (hcont_eval _).mul (hcont_eval _)
    exact hc.continuousAt.eventually (Iio_mem_nhds (hsign_t i))
  rcases Metric.mem_nhds_iff.mp hev_sign with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  have hsign_s := hball hs
  obtain ⟨r, hr_bounds, hr_anti, hr_roots⟩ :=
    roots_of_ordered_sign_change (nodePolynomial k s) (k + 2)
      (fun i => y i.rev - ε') (fun i => y i.rev + ε')
      (natDegree_nodePolynomial k s) (nodePolynomial_ne_zero k s)
      (fun i => by linarith)
      (fun a b hab => by simpa using hsep b.rev a.rev (Fin.rev_lt_rev.mpr hab))
      (fun i => hsign_s i.rev)
  let u : Fin (k + 2) → ℝ := fun i => r i.rev
  have hu_mono : StrictMono u := fun a b hab => hr_anti (Fin.rev_lt_rev.mpr hab)
  have hu_roots : (nodePolynomial k s).roots = (Finset.univ.image u).val := by
    rw [hr_roots]
    congr 1
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, u]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.rev, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.rev, rfl⟩
  have hord : orderedNode k s = u := orderedNode_eq_of_strictMono_of_roots k s u hu_mono hu_roots
  have hmem := hr_bounds j.rev
  rw [Fin.rev_rev] at hmem
  have hdiff : orderedNode k s j - orderedNode k t j = r j.rev - y j := by
    rw [hord]
  rw [Real.dist_eq, hdiff, abs_lt]
  exact ⟨by linarith [hmem.1], by linarith [hmem.2.1]⟩

theorem continuousOn_orderedNode (k : ℕ) (j : Fin (k + 2)) :
    ContinuousOn (fun t => orderedNode k t j) (Set.Icc (-1) 1) :=
  (continuous_orderedNode k j).continuousOn

theorem continuousAt_orderedNode_neg_one (k : ℕ) (j : Fin (k + 2)) :
    ContinuousAt (fun t => orderedNode k t j) (-1) :=
  (continuous_orderedNode k j).continuousAt

theorem continuousAt_orderedNode_one (k : ℕ) (j : Fin (k + 2)) :
    ContinuousAt (fun t => orderedNode k t j) 1 :=
  (continuous_orderedNode k j).continuousAt

/-- Speed symmetry on `(-1, 1)`: `u_j'(-t) = u_{n-j}'(t)`. -/
theorem hasDerivAt_orderedNode_neg (k : ℕ) {t : ℝ} (ht : |t| < 1) (j : Fin (k + 2)) :
    HasDerivAt (fun s => orderedNode k s j)
      (deriv (fun s => orderedNode k s j.rev) t) (-t) := by
  have hneg_t : |-t| < 1 := by simpa [abs_neg] using ht
  have hd_rev := hasDerivAt_orderedNode k ht j.rev
  have hd_neg := hasDerivAt_orderedNode k hneg_t j
  have hcomp : HasDerivAt (fun s => -orderedNode k s j.rev)
      (-(deriv (fun s => orderedNode k s j.rev) t)) t := by
    rw [hd_rev.deriv]
    exact hd_rev.neg
  have hcomp2 : HasDerivAt (fun s => orderedNode k (-s) j)
      (-deriv (fun s => orderedNode k s j) (-t)) t := by
    have hfun : (fun s => orderedNode k (-s) j) = (fun s => orderedNode k s j) ∘ (fun s => -s) := rfl
    rw [hfun, hd_neg.deriv]
    simpa using hd_neg.comp t (hasDerivAt_neg t)
  have heq : (fun s => orderedNode k (-s) j) = (fun s => -orderedNode k s j.rev) := by
    funext s
    exact orderedNode_neg k s j
  rw [heq] at hcomp2
  have hderiv_eq := hcomp.unique hcomp2
  have hv : deriv (fun s => orderedNode k s j) (-t) = deriv (fun s => orderedNode k s j.rev) t := by
    linarith
  rw [← hv]
  exact hd_neg.differentiableAt.hasDerivAt

theorem deriv_orderedNode_neg (k : ℕ) {t : ℝ} (ht : |t| < 1) (j : Fin (k + 2)) :
    deriv (fun s => orderedNode k s j) (-t) = deriv (fun s => orderedNode k s j.rev) t :=
  (hasDerivAt_orderedNode_neg k ht j).deriv

/-- Strict monotonicity extends from `(-1, 1)` to the closed interval `[-1, 1]`. -/
theorem orderedNode_strictMonoOn_Icc (k : ℕ) (j : Fin (k + 2)) :
    StrictMonoOn (fun t => orderedNode k t j) (Set.Icc (-1 : ℝ) 1) := by
  intro a ha b hb hab
  let m₁ : ℝ := (2 * a + b) / 3
  let m₂ : ℝ := (a + 2 * b) / 3
  have hm₁ : m₁ ∈ Set.Ioo (-1 : ℝ) 1 := by
    dsimp [m₁]
    exact ⟨by linarith [ha.1, hab], by linarith [hb.2, hab]⟩
  have hm₂ : m₂ ∈ Set.Ioo (-1 : ℝ) 1 := by
    dsimp [m₂]
    exact ⟨by linarith [ha.1, hab], by linarith [hb.2, hab]⟩
  have hm12 : m₁ < m₂ := by dsimp [m₁, m₂]; linarith
  have hmid : orderedNode k m₁ j < orderedNode k m₂ j :=
    orderedNode_strictMonoOn k j hm₁ hm₂ hm12
  have hleft : orderedNode k a j ≤ orderedNode k m₁ j := by
    have hcont : ContinuousWithinAt (fun t => orderedNode k t j) (Set.Ioi a) a :=
      (continuous_orderedNode k j).continuousAt.continuousWithinAt
    have hle : ∀ᶠ t in 𝓝[>] a, orderedNode k t j ≤ orderedNode k m₁ j := by
      filter_upwards [Ioo_mem_nhdsGT (show a < m₁ by dsimp [m₁]; linarith)] with t ht
      have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ha.1, ht.1], by linarith [hm₁.2, ht.2]⟩
      exact (orderedNode_strictMonoOn k j ht' hm₁ ht.2).le
    exact le_of_tendsto_of_tendsto hcont tendsto_const_nhds hle
  have hright : orderedNode k m₂ j ≤ orderedNode k b j := by
    have hcont : ContinuousWithinAt (fun t => orderedNode k t j) (Set.Iio b) b :=
      (continuous_orderedNode k j).continuousAt.continuousWithinAt
    have hle : ∀ᶠ t in 𝓝[<] b, orderedNode k m₂ j ≤ orderedNode k t j := by
      filter_upwards [Ioo_mem_nhdsLT (show m₂ < b by dsimp [m₂]; linarith)] with t ht
      have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hm₂.1, ht.1], by linarith [hb.2, ht.2]⟩
      exact (orderedNode_strictMonoOn k j hm₂ ht' ht.1).le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hcont hle
  linarith

/-- On `[-1, 1]`, each node `u_j(t)` stays inside `[r_j, r_{j+1}]`. -/
theorem orderedNode_mem_Icc (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (j : Fin (k + 2)) :
    orderedNode k t j ∈ Set.Icc (chebyshevGrid k j.val) (chebyshevGrid k (j.val + 1)) := by
  have hmono := orderedNode_strictMonoOn_Icc k j
  have h0 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  constructor
  · rw [← orderedNode_neg_one k j]
    exact hmono.monotoneOn h0 ht ht.1
  · rw [← orderedNode_one k j]
    exact hmono.monotoneOn ht h1 ht.2

/-- Each `orderedNode k · j` lies in `[-1, 1]` for `t ∈ [-1, 1]`. -/
theorem orderedNode_mem_Icc_unit (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (j : Fin (k + 2)) :
    orderedNode k t j ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := orderedNode_mem_Icc k ht j
  have hlo := chebyshevGrid_mem_Icc k j.val (by omega)
  have hhi := chebyshevGrid_mem_Icc k (j.val + 1) (by omega)
  exact ⟨hlo.1.trans h.1, h.2.trans hhi.2⟩

/-- On `(-1, 1)`, each node `u_j(t)` lies strictly inside `(r_j, r_{j+1})`. -/
theorem orderedNode_mem_Ioo (k : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (j : Fin (k + 2)) :
    orderedNode k t j ∈ Set.Ioo (chebyshevGrid k j.val) (chebyshevGrid k (j.val + 1)) := by
  have hmono := orderedNode_strictMonoOn_Icc k j
  have h0 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  constructor
  · rw [← orderedNode_neg_one k j]
    exact hmono h0 ht' ht.1
  · rw [← orderedNode_one k j]
    exact hmono ht' h1 ht.2

/-- Each `orderedNode k · j` is a strictly increasing bijection `[-1, 1] → [r_j, r_{j+1}]`. -/
theorem orderedNode_bijOn_Icc (k : ℕ) (j : Fin (k + 2)) :
    Set.BijOn (fun t => orderedNode k t j)
      (Set.Icc (-1 : ℝ) 1)
      (Set.Icc (chebyshevGrid k j.val) (chebyshevGrid k (j.val + 1))) := by
  refine ⟨fun t ht => orderedNode_mem_Icc k ht j,
    (orderedNode_strictMonoOn_Icc k j).injOn, ?_⟩
  have hiv := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) (continuousOn_orderedNode k j)
  rw [orderedNode_neg_one, orderedNode_one] at hiv
  exact hiv

/-- Monotonicity of `t ↦ t - u_j(t)` extends to the closed interval `[-1, 1]`. -/
theorem orderedNode_coefficient_monotoneOn_Icc (k : ℕ) (j : Fin (k + 2)) :
    MonotoneOn (fun t => t - orderedNode k t j) (Set.Icc (-1 : ℝ) 1) := by
  have hcont : ContinuousOn (fun t => t - orderedNode k t j) (Set.Icc (-1 : ℝ) 1) :=
    continuousOn_id.sub (continuousOn_orderedNode k j)
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  let m₁ : ℝ := (2 * a + b) / 3
  let m₂ : ℝ := (a + 2 * b) / 3
  have hm₁ : m₁ ∈ Set.Ioo (-1 : ℝ) 1 := by
    dsimp [m₁]
    exact ⟨by linarith [ha.1, hlt], by linarith [hb.2, hlt]⟩
  have hm₂ : m₂ ∈ Set.Ioo (-1 : ℝ) 1 := by
    dsimp [m₂]
    exact ⟨by linarith [ha.1, hlt], by linarith [hb.2, hlt]⟩
  have hmid : m₁ - orderedNode k m₁ j ≤ m₂ - orderedNode k m₂ j :=
    orderedNode_coefficient_monotoneOn k j hm₁ hm₂ (by dsimp [m₁, m₂]; linarith)
  have hleft : a - orderedNode k a j ≤ m₁ - orderedNode k m₁ j := by
    have hc : ContinuousWithinAt (fun t => t - orderedNode k t j) (Set.Ioi a) a :=
      (continuousAt_id.sub (continuous_orderedNode k j).continuousAt).continuousWithinAt
    have hle : ∀ᶠ t in 𝓝[>] a,
        t - orderedNode k t j ≤ m₁ - orderedNode k m₁ j := by
      filter_upwards [Ioo_mem_nhdsGT (show a < m₁ by dsimp [m₁]; linarith)] with t ht
      have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ha.1, ht.1], by linarith [hm₁.2, ht.2]⟩
      exact orderedNode_coefficient_monotoneOn k j ht' hm₁ ht.2.le
    exact le_of_tendsto_of_tendsto hc tendsto_const_nhds hle
  have hright : m₂ - orderedNode k m₂ j ≤ b - orderedNode k b j := by
    have hc : ContinuousWithinAt (fun t => t - orderedNode k t j) (Set.Iio b) b :=
      (continuousAt_id.sub (continuous_orderedNode k j).continuousAt).continuousWithinAt
    have hle : ∀ᶠ t in 𝓝[<] b,
        m₂ - orderedNode k m₂ j ≤ t - orderedNode k t j := by
      filter_upwards [Ioo_mem_nhdsLT (show m₂ < b by dsimp [m₂]; linarith)] with t ht
      have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hm₂.1, ht.1], by linarith [hb.2, ht.2]⟩
      exact orderedNode_coefficient_monotoneOn k j hm₂ ht' ht.1.le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hc hle
  linarith

/-- For `n = k + 1 ≥ 2` (`1 ≤ k`), the largest node at `t = 1 / 2` satisfies `u_n(1/2) > 1/2`. -/
theorem orderedNode_last_gt_half {k : ℕ} (hk : 1 ≤ k) :
    (1 / 2 : ℝ) < orderedNode k (1 / 2) (Fin.last (k + 1)) := by
  have hhalf_gt : (-1 : ℝ) < 1 / 2 := by norm_num
  have hlt : orderedNode k (-1) (Fin.last (k + 1)) < orderedNode k (1 / 2) (Fin.last (k + 1)) :=
    orderedNode_strictMonoOn_Icc k (Fin.last (k + 1))
      ⟨le_rfl, by norm_num⟩ ⟨by norm_num, by norm_num⟩ hhalf_gt
  rw [orderedNode_neg_one] at hlt
  have hge : (1 / 2 : ℝ) ≤ chebyshevGrid k (k + 1) := by
    have hle : k + 1 ≤ k + 2 := by omega
    rw [show k + 1 = k + 2 - 1 by omega, chebyshevGrid_reflect k 1 (by omega)]
    simp only [chebyshevGrid, Nat.cast_one, one_mul, neg_neg]
    have hangle : Real.pi / ((k : ℝ) + 2) ≤ Real.pi / 3 := by
      have hk3 : (3 : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 3 ≤ k + 2)
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hk3
    have hcos : Real.cos (Real.pi / 3) ≤ Real.cos (Real.pi / ((k : ℝ) + 2)) :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨by positivity, hangle.trans (by linarith [Real.pi_pos])⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩
        hangle
    rwa [Real.cos_pi_div_three] at hcos
  exact hge.trans_lt (by simpa using hlt)

end SharpL1
