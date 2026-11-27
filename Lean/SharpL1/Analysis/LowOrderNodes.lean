module

public import SharpL1.Chebyshev
public import SharpL1.Jacobi
public import SharpL1.Analysis.LowOrders
public import SharpL1.Analysis.ErrorValue
public import SharpL1.JacobiOrdered
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

/-!
# Explicit low-order Jacobi nodes and error-formula bridge

For orders `n = 1` (`nodePolynomial 0 t`) and `n = 2` (`nodePolynomial 1 t`), this file:

1. Gives the explicit strictly increasing root lists `nodes₁ t : Fin 2 → ℝ` and
   `nodes₂ t : Fin 3 → ℝ`, proves they are strictly increasing, and proves that they
   exhaust the full real-root multisets `(nodePolynomial 0 t).roots` and
   `(nodePolynomial 1 t).roots` (and hence the characteristic polynomial roots of
   `jacobiMatrix 0 t` and `jacobiMatrix 1 t`).
2. Evaluates `explicitError n u t` from equation `Eexplicit` of `paper.tex`, and
   proves that for `0 ≤ t ≤ 1`:
   - `explicitError 1 (nodes₁ t) t = e₁ t`,
   - `explicitError 2 (nodes₂ t) t = e₂ t`.
3. Proves uniqueness of strictly increasing enumerations of a finite root multiset,
   yielding `explicitError_eq_e₁_of_roots` and `explicitError_eq_e₂_of_roots` for
   direct connection to any global ordered-roots interface.
-/

namespace SharpL1.Analysis

open Polynomial
open Polynomial.Chebyshev (U)

/-! ### Explicit formulas for `nodePolynomial 0 t` and `nodePolynomial 1 t` -/

private theorem U_two_eval (y : ℝ) : (U ℝ 2).eval y = 4 * y ^ 2 - 1 := by
  have h2 : U ℝ ((0 : ℤ) + 2) = 2 * X * U ℝ ((0 : ℤ) + 1) - U ℝ 0 :=
    Polynomial.Chebyshev.U_add_two ℝ 0
  have h2' := congr_arg (fun P : ℝ[X] => P.eval y) h2
  simp only [zero_add, eval_sub, eval_mul, eval_ofNat, eval_X,
    Polynomial.Chebyshev.U_one, Polynomial.Chebyshev.U_zero, eval_one] at h2'
  linarith

private theorem U_three_eval (y : ℝ) : (U ℝ 3).eval y = 8 * y ^ 3 - 4 * y := by
  have h3 : U ℝ ((1 : ℤ) + 2) = 2 * X * U ℝ ((1 : ℤ) + 1) - U ℝ 1 :=
    Polynomial.Chebyshev.U_add_two ℝ 1
  have h3' := congr_arg (fun P : ℝ[X] => P.eval y) h3
  have h12 : (1 : ℤ) + 2 = 3 := by norm_num
  have h11 : (1 : ℤ) + 1 = 2 := by norm_num
  rw [h12, h11] at h3'
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X,
    U_two_eval, Polynomial.Chebyshev.U_one] at h3'
  linarith

/-- Explicit evaluation of `nodePolynomial 0 t` (order `n = 1`). -/
theorem nodePolynomial_zero_eval (t y : ℝ) :
    (nodePolynomial 0 t).eval y = 4 * y ^ 2 - 4 * t * y + t ^ 2 - 1 := by
  unfold nodePolynomial
  have h02 : ((0 : ℕ) : ℤ) + 2 = 2 := by norm_num
  have h01 : ((0 : ℕ) : ℤ) + 1 = 1 := by norm_num
  rw [h02, h01]
  simp only [eval_add, eval_sub, eval_mul, eval_C, Nat.cast_zero,
    U_two_eval, Polynomial.Chebyshev.U_one, Polynomial.Chebyshev.U_zero,
    eval_ofNat, eval_X, eval_one]
  ring

/-- Explicit evaluation of `nodePolynomial 1 t` (order `n = 2`). -/
theorem nodePolynomial_one_eval (t y : ℝ) :
    (nodePolynomial 1 t).eval y = 8 * y ^ 3 - 8 * t * y ^ 2 + (2 * t ^ 2 - 4) * y + 2 * t := by
  unfold nodePolynomial
  have h12 : ((1 : ℕ) : ℤ) + 2 = 3 := by norm_num
  have h11 : ((1 : ℕ) : ℤ) + 1 = 2 := by norm_num
  rw [h12, h11]
  simp only [eval_add, eval_sub, eval_mul, eval_C, Nat.cast_one,
    U_three_eval, U_two_eval, Polynomial.Chebyshev.U_one, eval_ofNat, eval_X]
  ring

/-! ### Order `n = 1` nodes (`nodePolynomial 0 t`) -/

/-- The two increasing real roots of `nodePolynomial 0 t` (order `n = 1`):
`(t - 1) / 2` and `(t + 1) / 2`. -/
@[expose] noncomputable def nodes₁ (t : ℝ) : Fin 2 → ℝ
  | ⟨0, _⟩ => (t - 1) / 2
  | ⟨1, _⟩ => (t + 1) / 2

@[simp] theorem nodes₁_zero (t : ℝ) : nodes₁ t 0 = (t - 1) / 2 := rfl
@[simp] theorem nodes₁_one (t : ℝ) : nodes₁ t 1 = (t + 1) / 2 := rfl

/-- The two order-1 roots are strictly increasing for every `t : ℝ`. -/
theorem nodes₁_strictMono (t : ℝ) : StrictMono (nodes₁ t) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [nodes₁]
  linarith

/-- Every `nodes₁ t i` is a root of `nodePolynomial 0 t`. -/
theorem nodePolynomial_zero_eval_nodes₁ (t : ℝ) (i : Fin 2) :
    (nodePolynomial 0 t).eval (nodes₁ t i) = 0 := by
  fin_cases i <;> simp [nodePolynomial_zero_eval] <;> ring

/-- `nodes₁ t` exhausts the complete real-root multiset of `nodePolynomial 0 t`. -/
theorem nodePolynomial_zero_roots (t : ℝ) :
    (nodePolynomial 0 t).roots = (Finset.univ.image (nodes₁ t)).val := by
  have hS : ∀ x ∈ Finset.univ.image (nodes₁ t), (nodePolynomial 0 t).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact nodePolynomial_zero_eval_nodes₁ t i
  have hcard : (nodePolynomial 0 t).natDegree ≤ (Finset.univ.image (nodes₁ t)).card := by
    rw [natDegree_nodePolynomial,
      Finset.card_image_of_injective Finset.univ (nodes₁_strictMono t).injective]
    simp
  exact roots_eq_of_natDegree_le_card_of_ne_zero hS hcard (nodePolynomial_ne_zero 0 t)

/-- `nodes₁ t` exhausts the characteristic polynomial roots of `jacobiMatrix 0 t`. -/
theorem jacobiMatrix_zero_charpoly_roots (t : ℝ) :
    (jacobiMatrix 0 t).charpoly.roots = (Finset.univ.image (nodes₁ t)).val := by
  rw [jacobi_charpoly, Polynomial.roots_C_mul _ (by positivity), nodePolynomial_zero_roots]

/-- For `0 ≤ t`, the smaller order-1 root satisfies `nodes₁ t 0 ≤ t`. -/
theorem nodes₁_zero_le {t : ℝ} (ht0 : 0 ≤ t) : nodes₁ t 0 ≤ t := by
  simp only [nodes₁_zero]
  linarith

/-- For `t ≤ 1`, the larger order-1 root satisfies `t ≤ nodes₁ t 1`. -/
theorem le_nodes₁_one {t : ℝ} (ht1 : t ≤ 1) : t ≤ nodes₁ t 1 := by
  simp only [nodes₁_one]
  linarith

/-- Substituting `nodes₁ t` into `Eexplicit` yields `e₁ t` for `0 ≤ t ≤ 1`. -/
theorem explicitError_nodes₁ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    explicitError 1 (nodes₁ t) t = e₁ t := by
  unfold explicitError e₁
  rw [Fin.sum_univ_two]
  have h0 : nodes₁ t 0 - t ≤ 0 := sub_nonpos.mpr (nodes₁_zero_le ht0)
  have h1 : 0 ≤ nodes₁ t 1 - t := sub_nonneg.mpr (le_nodes₁_one ht1)
  rw [max_eq_right h0, max_eq_left h1]
  simp only [Fin.val_zero, Fin.val_one, nodes₁_one]
  norm_num
  ring

/-! ### Order `n = 2` nodes (`nodePolynomial 1 t`) -/

/-- The three increasing real roots of `nodePolynomial 1 t` (order `n = 2`):
`(t - √(8 + t²)) / 4`, `t / 2`, and `(t + √(8 + t²)) / 4`. -/
@[expose] noncomputable def nodes₂ (t : ℝ) : Fin 3 → ℝ
  | ⟨0, _⟩ => (t - Real.sqrt (8 + t ^ 2)) / 4
  | ⟨1, _⟩ => t / 2
  | ⟨2, _⟩ => (t + Real.sqrt (8 + t ^ 2)) / 4

@[simp] theorem nodes₂_zero (t : ℝ) : nodes₂ t 0 = (t - Real.sqrt (8 + t ^ 2)) / 4 := rfl
@[simp] theorem nodes₂_one (t : ℝ) : nodes₂ t 1 = t / 2 := rfl
@[simp] theorem nodes₂_two (t : ℝ) : nodes₂ t 2 = (t + Real.sqrt (8 + t ^ 2)) / 4 := rfl

/-- Elementary bound `|t| < √(8 + t²)`, valid for all `t : ℝ`. -/
theorem abs_lt_sqrt_eight_add_sq (t : ℝ) : |t| < Real.sqrt (8 + t ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg t) (by linarith)

/-- The three order-2 roots are strictly increasing for every `t : ℝ`. -/
theorem nodes₂_strictMono (t : ℝ) : StrictMono (nodes₂ t) := by
  have habs := abs_lt_sqrt_eight_add_sq t
  have h1 : -t < Real.sqrt (8 + t ^ 2) := lt_of_le_of_lt (neg_le_abs t) habs
  have h2 : t < Real.sqrt (8 + t ^ 2) := lt_of_le_of_lt (le_abs_self t) habs
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [nodes₂] <;> linarith

/-- Every `nodes₂ t i` is a root of `nodePolynomial 1 t`. -/
theorem nodePolynomial_one_eval_nodes₂ (t : ℝ) (i : Fin 3) :
    (nodePolynomial 1 t).eval (nodes₂ t i) = 0 := by
  have hsq : Real.sqrt (8 + t ^ 2) ^ 2 = 8 + t ^ 2 := Real.sq_sqrt (by positivity)
  fin_cases i
  · simp only [nodePolynomial_one_eval, nodes₂]
    linear_combination (-t / 8 - Real.sqrt (8 + t ^ 2) / 8) * hsq
  · simp only [nodePolynomial_one_eval, nodes₂]
    ring
  · simp only [nodePolynomial_one_eval, nodes₂]
    linear_combination (-t / 8 + Real.sqrt (8 + t ^ 2) / 8) * hsq

/-- `nodes₂ t` exhausts the complete real-root multiset of `nodePolynomial 1 t`. -/
theorem nodePolynomial_one_roots (t : ℝ) :
    (nodePolynomial 1 t).roots = (Finset.univ.image (nodes₂ t)).val := by
  have hS : ∀ x ∈ Finset.univ.image (nodes₂ t), (nodePolynomial 1 t).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact nodePolynomial_one_eval_nodes₂ t i
  have hcard : (nodePolynomial 1 t).natDegree ≤ (Finset.univ.image (nodes₂ t)).card := by
    rw [natDegree_nodePolynomial,
      Finset.card_image_of_injective Finset.univ (nodes₂_strictMono t).injective]
    simp
  exact roots_eq_of_natDegree_le_card_of_ne_zero hS hcard (nodePolynomial_ne_zero 1 t)

/-- `nodes₂ t` exhausts the characteristic polynomial roots of `jacobiMatrix 1 t`. -/
theorem jacobiMatrix_one_charpoly_roots (t : ℝ) :
    (jacobiMatrix 1 t).charpoly.roots = (Finset.univ.image (nodes₂ t)).val := by
  rw [jacobi_charpoly, Polynomial.roots_C_mul _ (by positivity), nodePolynomial_one_roots]

/-- For `0 ≤ t ≤ 1`, `3 * t ≤ √(8 + t²)` (squaring gives `9 t² ≤ 8 + t² ↔ t² ≤ 1`). -/
theorem three_mul_le_sqrt_eight_add_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    3 * t ≤ Real.sqrt (8 + t ^ 2) := by
  rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 3 * t)]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- For `0 ≤ t`, the smallest order-2 root satisfies `nodes₂ t 0 ≤ t`. -/
theorem nodes₂_zero_le {t : ℝ} (ht0 : 0 ≤ t) : nodes₂ t 0 ≤ t := by
  simp only [nodes₂_zero]
  have hsqrt : 0 ≤ Real.sqrt (8 + t ^ 2) := Real.sqrt_nonneg _
  linarith

/-- For `0 ≤ t`, the middle order-2 root satisfies `nodes₂ t 1 ≤ t`. -/
theorem nodes₂_one_le {t : ℝ} (ht0 : 0 ≤ t) : nodes₂ t 1 ≤ t := by
  simp only [nodes₂_one]
  linarith

/-- For `0 ≤ t ≤ 1`, the largest order-2 root satisfies `t ≤ nodes₂ t 2`. -/
theorem le_nodes₂_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t ≤ nodes₂ t 2 := by
  simp only [nodes₂_two]
  linarith [three_mul_le_sqrt_eight_add_sq ht0 ht1]

/-- Substituting `nodes₂ t` into `Eexplicit` yields `e₂ t` for `0 ≤ t ≤ 1`. -/
theorem explicitError_nodes₂ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    explicitError 2 (nodes₂ t) t = e₂ t := by
  unfold explicitError e₂
  rw [Fin.sum_univ_three]
  have h0 : nodes₂ t 0 - t ≤ 0 := sub_nonpos.mpr (nodes₂_zero_le ht0)
  have h1 : nodes₂ t 1 - t ≤ 0 := sub_nonpos.mpr (nodes₂_one_le ht0)
  have h2 : 0 ≤ nodes₂ t 2 - t := sub_nonneg.mpr (le_nodes₂_two ht0 ht1)
  rw [max_eq_right h0, max_eq_right h1, max_eq_left h2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, nodes₂_two]
  have hsq : Real.sqrt (8 + t ^ 2) ^ 2 = 8 + t ^ 2 := Real.sq_sqrt (by positivity)
  linear_combination (Real.sqrt (8 + t ^ 2) / 24 - 3 * t / 8) * hsq

/-! ### Uniqueness of strictly increasing enumerations -/

/-- Any strictly increasing enumeration of `(nodePolynomial 0 t).roots` equals `nodes₁ t`. -/
theorem eq_nodes₁_of_strictMono_roots {t : ℝ} {u : Fin 2 → ℝ}
    (hmono : StrictMono u)
    (hroots : (nodePolynomial 0 t).roots = (Finset.univ.image u).val) :
    u = nodes₁ t :=
  (orderedNode_eq_of_strictMono_of_roots 0 t u hmono hroots).symm.trans
    (orderedNode_eq_of_strictMono_of_roots 0 t _ (nodes₁_strictMono t) (nodePolynomial_zero_roots t))

/-- Any strictly increasing enumeration of `(nodePolynomial 1 t).roots` equals `nodes₂ t`. -/
theorem eq_nodes₂_of_strictMono_roots {t : ℝ} {u : Fin 3 → ℝ}
    (hmono : StrictMono u)
    (hroots : (nodePolynomial 1 t).roots = (Finset.univ.image u).val) :
    u = nodes₂ t :=
  (orderedNode_eq_of_strictMono_of_roots 1 t u hmono hroots).symm.trans
    (orderedNode_eq_of_strictMono_of_roots 1 t _ (nodes₂_strictMono t) (nodePolynomial_one_roots t))

/-- Any strictly increasing enumeration of `(nodePolynomial 0 t).roots` yields `e₁ t`
when substituted into `explicitError 1 · t` on `[0, 1]`. -/
theorem explicitError_eq_e₁_of_roots {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {u : Fin 2 → ℝ} (hmono : StrictMono u)
    (hroots : (nodePolynomial 0 t).roots = (Finset.univ.image u).val) :
    explicitError 1 u t = e₁ t := by
  rw [eq_nodes₁_of_strictMono_roots hmono hroots]
  exact explicitError_nodes₁ ht0 ht1

/-- Any strictly increasing enumeration of `(nodePolynomial 1 t).roots` yields `e₂ t`
when substituted into `explicitError 2 · t` on `[0, 1]`. -/
theorem explicitError_eq_e₂_of_roots {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {u : Fin 3 → ℝ} (hmono : StrictMono u)
    (hroots : (nodePolynomial 1 t).roots = (Finset.univ.image u).val) :
    explicitError 2 u t = e₂ t := by
  rw [eq_nodes₂_of_strictMono_roots hmono hroots]
  exact explicitError_nodes₂ ht0 ht1

theorem explicitError_orderedNode_one_lt_center {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    explicitError 1 (orderedNode 0 t) t < explicitError 1 (orderedNode 0 0) 0 := by
  rw [orderedNode_eq_of_strictMono_of_roots 0 t _ (nodes₁_strictMono t) (nodePolynomial_zero_roots t),
    orderedNode_eq_of_strictMono_of_roots 0 0 _ (nodes₁_strictMono 0) (nodePolynomial_zero_roots 0),
    explicitError_nodes₁ ht0.le ht1, explicitError_nodes₁ (by norm_num) (by norm_num)]
  exact e₁_lt_e₁_zero ht0 ht1

theorem explicitError_orderedNode_two_lt_center {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    explicitError 2 (orderedNode 1 t) t < explicitError 2 (orderedNode 1 0) 0 := by
  rw [orderedNode_eq_of_strictMono_of_roots 1 t _ (nodes₂_strictMono t) (nodePolynomial_one_roots t),
    orderedNode_eq_of_strictMono_of_roots 1 0 _ (nodes₂_strictMono 0) (nodePolynomial_one_roots 0),
    explicitError_nodes₂ ht0.le ht1, explicitError_nodes₂ (by norm_num) (by norm_num)]
  exact e₂_lt_e₂_zero ht0 ht1

end SharpL1.Analysis
