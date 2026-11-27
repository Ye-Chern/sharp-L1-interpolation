module

public import SharpL1.Analysis.LowOrders
public import SharpL1.Analysis.LowOrderNodes
public import SharpL1.Analysis.ChordIntegral
public import SharpL1.Analysis.ChordBoundsN4
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Low-Order Strict Monotonicity (`n = 1, 2, 3`)

This file formalizes Section 7 and Appendix B.2 of `chebyshev_L1_complete.tex`:

1. `n = 1`: `E₁'(t) = -t < 0` on `(0, 1)` and strict anti-monotonicity of `E₁` on `[0, 1]`.
2. `n = 2`: `E₂'(t) < 0` on `(0, 1)` via the polynomial identity
   `(t + 16)^2 (t^2 + 8) - (7 t^2 + 38)^2 = 4 (t + 1) (151 - 87 t + 20 t^2 - 12 t^3)`
   and `151 - 87 t + 20 t^2 - 12 t^3 ≥ 52 > 0` on `[0, 1]`.
3. `n = 3`:
   - Explicit ordered nodes `nodes₃ t : Fin 4 → ℝ` for `nodePolynomial 2 t`,
     closed form `e₃ t = explicitError 3 (orderedNode 2 t) t` on `[0, 1/2]`,
     and elementary algebraic center bound `e₃ t - e₃ 0 ≤ -(11 / 32) t^2 < 0` on `(0, 1/2]`.
   - Kernel-verified 5-subinterval rational Riemann-sum certificate (`decide`) for `n = 3`,
     with exact `Real.sqrt` soundness lemmas for `sqrtRatUB` and `sqrtRatLB`.
-/

namespace SharpL1.Analysis

open Polynomial MeasureTheory
open Polynomial.Chebyshev (U)
open Set

/-! ### Order `n = 1`: strict monotonicity on `[0, 1]` -/

theorem hasDerivAt_e₁ (t : ℝ) : HasDerivAt e₁ (-t) t := by
  have hfn : e₁ = fun x : ℝ => (1 - x ^ 2) / 2 := rfl
  rw [hfn]
  have hd : HasDerivAt (fun x : ℝ => (1 - x ^ 2) / 2) ((0 - 2 * t) / 2) t :=
    ((hasDerivAt_pow 2 t).const_sub 1).div_const 2 |>.congr_deriv (by simp)
  exact hd.congr_deriv (by ring)

theorem e₁_strictAntiOn : StrictAntiOn e₁ (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · exact (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_e₁ x).continuousAt).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_e₁ x).deriv]
    linarith [hx.1]

theorem explicitError_orderedNode_one_eq_e₁ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    explicitError 1 (orderedNode 0 t) t = e₁ t := by
  rw [orderedNode_eq_of_strictMono_of_roots 0 t _ (nodes₁_strictMono t) (nodePolynomial_zero_roots t)]
  exact explicitError_nodes₁ ht0 ht1

theorem explicitError_orderedNode_one_strictAntiOn :
    StrictAntiOn (fun t => explicitError 1 (orderedNode 0 t) t) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  dsimp only
  rw [explicitError_orderedNode_one_eq_e₁ ha.1 ha.2, explicitError_orderedNode_one_eq_e₁ hb.1 hb.2]
  exact e₁_strictAntiOn ha hb hab

theorem hasDerivAt_explicitError_orderedNode_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun s => explicitError 1 (orderedNode 0 s) s) (-t) t ∧
      deriv (fun s => explicitError 1 (orderedNode 0 s) s) t < 0 := by
  have hev : (fun s => explicitError 1 (orderedNode 0 s) s) =ᶠ[nhds t] e₁ := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    exact explicitError_orderedNode_one_eq_e₁ hs.1.le hs.2.le
  have hd : HasDerivAt (fun s => explicitError 1 (orderedNode 0 s) s) (-t) t :=
    (hasDerivAt_e₁ t).congr_of_eventuallyEq hev
  exact ⟨hd, by rw [hd.deriv]; linarith⟩

/-! ### Order `n = 2`: strict monotonicity via Section 7 cubic bound -/

theorem e₂_deriv_poly_identity (t : ℝ) :
    (t + 16) ^ 2 * (t ^ 2 + 8) - (7 * t ^ 2 + 38) ^ 2 =
      4 * (t + 1) * (151 - 87 * t + 20 * t ^ 2 - 12 * t ^ 3) := by
  ring

theorem e₂_deriv_poly_ge_52 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    52 ≤ 151 - 87 * t + 20 * t ^ 2 - 12 * t ^ 3 := by
  have hdecomp : 151 - 87 * t + 20 * t ^ 2 - 12 * t ^ 3 =
      (151 - 99 * t) + 20 * t ^ 2 + 12 * t * (1 - t ^ 2) := by
    ring
  have h1 : 52 ≤ 151 - 99 * t := by linarith
  have h2 : 0 ≤ 20 * t ^ 2 := by positivity
  have h3 : 0 ≤ 12 * t * (1 - t ^ 2) := by nlinarith
  linarith

theorem six_mul_e₂_deriv_neg_paper {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    t * ((114 + 21 * t ^ 2) / Real.sqrt (8 + t ^ 2) - 48 - 3 * t) < 0 := by
  have h8 : (0 : ℝ) < 8 + t ^ 2 := by positivity
  have hs_pos : 0 < Real.sqrt (8 + t ^ 2) := Real.sqrt_pos.mpr h8
  have hs_sq : Real.sqrt (8 + t ^ 2) ^ 2 = 8 + t ^ 2 := Real.sq_sqrt h8.le
  have hpoly_pos : 0 < 4 * (t + 1) * (151 - 87 * t + 20 * t ^ 2 - 12 * t ^ 3) := by
    have h52 := e₂_deriv_poly_ge_52 ht0.le ht1.le
    positivity
  have hsq_diff : ((t + 16) * Real.sqrt (8 + t ^ 2)) ^ 2 - (7 * t ^ 2 + 38) ^ 2 =
      4 * (t + 1) * (151 - 87 * t + 20 * t ^ 2 - 12 * t ^ 3) := by
    rw [mul_pow, hs_sq]
    have h := e₂_deriv_poly_identity t
    linarith
  have hlt_sq : (7 * t ^ 2 + 38) ^ 2 < ((t + 16) * Real.sqrt (8 + t ^ 2)) ^ 2 := by linarith
  have hpos_lhs : 0 ≤ 7 * t ^ 2 + 38 := by positivity
  have hpos_rhs : 0 ≤ (t + 16) * Real.sqrt (8 + t ^ 2) := by positivity
  have hlt_sqrt : 7 * t ^ 2 + 38 < (t + 16) * Real.sqrt (8 + t ^ 2) := by nlinarith
  have heq : (114 + 21 * t ^ 2) / Real.sqrt (8 + t ^ 2) - 48 - 3 * t =
      3 * ((7 * t ^ 2 + 38) - (t + 16) * Real.sqrt (8 + t ^ 2)) / Real.sqrt (8 + t ^ 2) := by
    field_simp [hs_pos.ne']
    ring
  rw [heq]
  have hnum_neg : 3 * ((7 * t ^ 2 + 38) - (t + 16) * Real.sqrt (8 + t ^ 2)) < 0 := by linarith
  exact mul_neg_of_pos_of_neg ht0 (div_neg_of_neg_of_pos hnum_neg hs_pos)

theorem explicitError_orderedNode_two_eq_e₂ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    explicitError 2 (orderedNode 1 t) t = e₂ t := by
  rw [orderedNode_eq_of_strictMono_of_roots 1 t _ (nodes₂_strictMono t) (nodePolynomial_one_roots t)]
  exact explicitError_nodes₂ ht0 ht1

theorem explicitError_orderedNode_two_strictAntiOn :
    StrictAntiOn (fun t => explicitError 2 (orderedNode 1 t) t) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  dsimp only
  rw [explicitError_orderedNode_two_eq_e₂ ha.1 ha.2, explicitError_orderedNode_two_eq_e₂ hb.1 hb.2]
  exact e₂_strictAntiOn ha hb hab

theorem hasDerivAt_explicitError_orderedNode_two {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    deriv (fun s => explicitError 2 (orderedNode 1 s) s) t < 0 := by
  have hev : (fun s => explicitError 2 (orderedNode 1 s) s) =ᶠ[nhds t] e₂ := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    exact explicitError_orderedNode_two_eq_e₂ hs.1.le hs.2.le
  have hd : HasDerivAt (fun s => explicitError 2 (orderedNode 1 s) s)
      (t * ((114 + 21 * t ^ 2) / Real.sqrt (8 + t ^ 2) - 48 - 3 * t) / 6) t := by
    have h6 := (hasDerivAt_six_mul_e₂ t).const_mul (1 / 6 : ℝ)
    have h6' : (fun x => (1 / 6 : ℝ) * (6 * e₂ x)) = e₂ := by ext x; ring
    rw [h6'] at h6
    refine (h6.congr_of_eventuallyEq hev).congr_deriv ?_
    ring
  rw [hd.deriv]
  exact div_neg_of_neg_of_pos (six_mul_e₂_deriv_neg_paper ht0 ht1) (by norm_num)

/-! ### Order `n = 3`: explicit nodes, `e₃`, and algebraic center bound on `[0, 1/2]` -/

private theorem U_two_eval' (y : ℝ) : (U ℝ 2).eval y = 4 * y ^ 2 - 1 := by
  have h2 : U ℝ ((0 : ℤ) + 2) = 2 * X * U ℝ ((0 : ℤ) + 1) - U ℝ 0 :=
    Polynomial.Chebyshev.U_add_two ℝ 0
  have h2' := congr_arg (fun P : ℝ[X] => P.eval y) h2
  simp only [zero_add, eval_sub, eval_mul, eval_ofNat, eval_X,
    Polynomial.Chebyshev.U_one, Polynomial.Chebyshev.U_zero, eval_one] at h2'
  linarith

private theorem U_three_eval' (y : ℝ) : (U ℝ 3).eval y = 8 * y ^ 3 - 4 * y := by
  have h3 : U ℝ ((1 : ℤ) + 2) = 2 * X * U ℝ ((1 : ℤ) + 1) - U ℝ 1 :=
    Polynomial.Chebyshev.U_add_two ℝ 1
  have h3' := congr_arg (fun P : ℝ[X] => P.eval y) h3
  have h12 : (1 : ℤ) + 2 = 3 := by norm_num
  have h11 : (1 : ℤ) + 1 = 2 := by norm_num
  rw [h12, h11] at h3'
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X, U_two_eval',
    Polynomial.Chebyshev.U_one] at h3'
  linarith

private theorem U_four_eval (y : ℝ) : (U ℝ 4).eval y = 16 * y ^ 4 - 12 * y ^ 2 + 1 := by
  have h4 : U ℝ ((2 : ℤ) + 2) = 2 * X * U ℝ ((2 : ℤ) + 1) - U ℝ 2 :=
    Polynomial.Chebyshev.U_add_two ℝ 2
  have h4' := congr_arg (fun P : ℝ[X] => P.eval y) h4
  have h22 : (2 : ℤ) + 2 = 4 := by norm_num
  have h21 : (2 : ℤ) + 1 = 3 := by norm_num
  rw [h22, h21] at h4'
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X, U_three_eval', U_two_eval'] at h4'
  linarith

theorem nodePolynomial_two_eval (t y : ℝ) :
    (nodePolynomial 2 t).eval y =
      16 * y ^ 4 - 16 * t * y ^ 3 + (4 * t ^ 2 - 12) * y ^ 2 + 8 * t * y - t ^ 2 + 1 := by
  unfold nodePolynomial
  have h22 : ((2 : ℕ) : ℤ) + 2 = 4 := by norm_num
  have h21 : ((2 : ℕ) : ℤ) + 1 = 3 := by norm_num
  rw [h22, h21]
  simp only [eval_add, eval_sub, eval_mul, eval_C, Nat.cast_ofNat,
    U_four_eval, U_three_eval', U_two_eval']
  ring

/-- The four strictly increasing real roots of `nodePolynomial 2 t` (order `n = 3`). -/
noncomputable def nodes₃ (t : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => (t - 1 - Real.sqrt (5 + 2 * t + t ^ 2)) / 4
  | ⟨1, _⟩ => (t + 1 - Real.sqrt (5 - 2 * t + t ^ 2)) / 4
  | ⟨2, _⟩ => (t - 1 + Real.sqrt (5 + 2 * t + t ^ 2)) / 4
  | ⟨3, _⟩ => (t + 1 + Real.sqrt (5 - 2 * t + t ^ 2)) / 4

@[simp] theorem nodes₃_zero (t : ℝ) : nodes₃ t 0 = (t - 1 - Real.sqrt (5 + 2 * t + t ^ 2)) / 4 := rfl
@[simp] theorem nodes₃_one (t : ℝ) : nodes₃ t 1 = (t + 1 - Real.sqrt (5 - 2 * t + t ^ 2)) / 4 := rfl
@[simp] theorem nodes₃_two (t : ℝ) : nodes₃ t 2 = (t - 1 + Real.sqrt (5 + 2 * t + t ^ 2)) / 4 := rfl
@[simp] theorem nodes₃_three (t : ℝ) : nodes₃ t 3 = (t + 1 + Real.sqrt (5 - 2 * t + t ^ 2)) / 4 := rfl

theorem nodes₃_strictMono (t : ℝ) : StrictMono (nodes₃ t) := by
  let rp := Real.sqrt (5 + 2 * t + t ^ 2)
  let rm := Real.sqrt (5 - 2 * t + t ^ 2)
  have hrp2 : rp ^ 2 = 5 + 2 * t + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (t + 1)])
  have hrm2 : rm ^ 2 = 5 - 2 * t + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (t - 1)])
  have hrp_ge2 : 2 ≤ rp := by
    have : (2 : ℝ) ^ 2 ≤ 5 + 2 * t + t ^ 2 := by nlinarith [sq_nonneg (t + 1)]
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt this
  have hrm_ge2 : 2 ≤ rm := by
    have : (2 : ℝ) ^ 2 ≤ 5 - 2 * t + t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt this
  have hrp_abs : |t + 1| < rp := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hrm_abs : |1 - t| < rm := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have h01 : nodes₃ t 0 < nodes₃ t 1 := by
    simp only [nodes₃_zero, nodes₃_one]
    have ht1 : -(t + 1) < rp := lt_of_le_of_lt (neg_le_abs _) hrp_abs
    have hsq : rm ^ 2 < (rp + 2) ^ 2 := by nlinarith
    have hlt : rm < rp + 2 := by nlinarith
    linarith
  have h12 : nodes₃ t 1 < nodes₃ t 2 := by
    simp only [nodes₃_one, nodes₃_two]
    linarith
  have h23 : nodes₃ t 2 < nodes₃ t 3 := by
    simp only [nodes₃_two, nodes₃_three]
    have ht1 : -(1 - t) < rm := lt_of_le_of_lt (neg_le_abs _) hrm_abs
    have hsq : rp ^ 2 < (rm + 2) ^ 2 := by nlinarith
    have hlt : rp < rm + 2 := by nlinarith
    linarith
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith

theorem nodePolynomial_two_eval_nodes₃ (t : ℝ) (i : Fin 4) :
    (nodePolynomial 2 t).eval (nodes₃ t i) = 0 := by
  let rp := Real.sqrt (5 + 2 * t + t ^ 2)
  let rm := Real.sqrt (5 - 2 * t + t ^ 2)
  have hrp : rp ^ 2 = 5 + 2 * t + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (t + 1)])
  have hrm : rm ^ 2 = 5 - 2 * t + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (t - 1)])
  have hrp3 : rp ^ 3 = rp * rp ^ 2 := by ring
  have hrp4 : rp ^ 4 = (rp ^ 2) ^ 2 := by ring
  have hrm3 : rm ^ 3 = rm * rm ^ 2 := by ring
  have hrm4 : rm ^ 4 = (rm ^ 2) ^ 2 := by ring
  fin_cases i
  · simp only [nodePolynomial_two_eval]
    change 16 * ((t - 1 - rp) / 4) ^ 4 - 16 * t * ((t - 1 - rp) / 4) ^ 3 +
      (4 * t ^ 2 - 12) * ((t - 1 - rp) / 4) ^ 2 + 8 * t * ((t - 1 - rp) / 4) - t ^ 2 + 1 = 0
    ring_nf
    rw [hrp4, hrp3, hrp]
    ring
  · simp only [nodePolynomial_two_eval]
    change 16 * ((t + 1 - rm) / 4) ^ 4 - 16 * t * ((t + 1 - rm) / 4) ^ 3 +
      (4 * t ^ 2 - 12) * ((t + 1 - rm) / 4) ^ 2 + 8 * t * ((t + 1 - rm) / 4) - t ^ 2 + 1 = 0
    ring_nf
    rw [hrm4, hrm3, hrm]
    ring
  · simp only [nodePolynomial_two_eval]
    change 16 * ((t - 1 + rp) / 4) ^ 4 - 16 * t * ((t - 1 + rp) / 4) ^ 3 +
      (4 * t ^ 2 - 12) * ((t - 1 + rp) / 4) ^ 2 + 8 * t * ((t - 1 + rp) / 4) - t ^ 2 + 1 = 0
    ring_nf
    rw [hrp4, hrp3, hrp]
    ring
  · simp only [nodePolynomial_two_eval]
    change 16 * ((t + 1 + rm) / 4) ^ 4 - 16 * t * ((t + 1 + rm) / 4) ^ 3 +
      (4 * t ^ 2 - 12) * ((t + 1 + rm) / 4) ^ 2 + 8 * t * ((t + 1 + rm) / 4) - t ^ 2 + 1 = 0
    ring_nf
    rw [hrm4, hrm3, hrm]
    ring

theorem nodePolynomial_two_roots (t : ℝ) :
    (nodePolynomial 2 t).roots = (Finset.univ.image (nodes₃ t)).val := by
  have hS : ∀ x ∈ Finset.univ.image (nodes₃ t), (nodePolynomial 2 t).eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact nodePolynomial_two_eval_nodes₃ t i
  have hcard : (nodePolynomial 2 t).natDegree ≤ (Finset.univ.image (nodes₃ t)).card := by
    rw [natDegree_nodePolynomial,
      Finset.card_image_of_injective Finset.univ (nodes₃_strictMono t).injective]
    simp
  exact roots_eq_of_natDegree_le_card_of_ne_zero hS hcard (nodePolynomial_ne_zero 2 t)

/-- Explicit order-3 error function on `[0, 1/2]` from Section 7 of `chebyshev_L1_complete.tex`. -/
noncomputable def e₃ (t : ℝ) : ℝ :=
  ((3 + 13 * t + 17 * t ^ 2 + 15 * t ^ 3) * Real.sqrt (5 + 2 * t + t ^ 2) +
    (3 - 13 * t + 17 * t ^ 2 - 15 * t ^ 3) * Real.sqrt (5 - 2 * t + t ^ 2)) / 8 -
    1 - 12 * t ^ 2 - 2 * t ^ 4

theorem nodes₃_zero_le {t : ℝ} (ht0 : 0 ≤ t) : nodes₃ t 0 ≤ t := by
  simp only [nodes₃_zero]
  have hrp : 0 ≤ Real.sqrt (5 + 2 * t + t ^ 2) := Real.sqrt_nonneg _
  linarith

theorem nodes₃_one_le {t : ℝ} (ht0 : 0 ≤ t) : nodes₃ t 1 ≤ t := by
  simp only [nodes₃_one]
  have hrm : 2 ≤ Real.sqrt (5 - 2 * t + t ^ 2) := by
    nth_rw 1 [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (t - 1)])
  linarith

theorem le_nodes₃_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) : t ≤ nodes₃ t 2 := by
  simp only [nodes₃_two]
  have hsq : (1 + 3 * t) ^ 2 ≤ 5 + 2 * t + t ^ 2 := by
    have : 5 + 2 * t + t ^ 2 - (1 + 3 * t) ^ 2 = 4 * (1 + t) * (1 - 2 * t) := by ring
    nlinarith
  have hle : 1 + 3 * t ≤ Real.sqrt (5 + 2 * t + t ^ 2) := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1 + 3 * t by linarith)]
    exact Real.sqrt_le_sqrt hsq
  linarith

theorem le_nodes₃_three {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) : t ≤ nodes₃ t 3 :=
  (le_nodes₃_two ht0 ht1).trans (nodes₃_strictMono t (by decide : (2 : Fin 4) < 3)).le

theorem explicitError_nodes₃ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    explicitError 3 (nodes₃ t) t = e₃ t := by
  unfold explicitError e₃
  rw [Fin.sum_univ_four]
  have h0 : nodes₃ t 0 - t ≤ 0 := sub_nonpos.mpr (nodes₃_zero_le ht0)
  have h1 : nodes₃ t 1 - t ≤ 0 := sub_nonpos.mpr (nodes₃_one_le ht0)
  have h2 : 0 ≤ nodes₃ t 2 - t := sub_nonneg.mpr (le_nodes₃_two ht0 ht1)
  have h3 : 0 ≤ nodes₃ t 3 - t := sub_nonneg.mpr (le_nodes₃_three ht0 ht1)
  rw [max_eq_right h0, max_eq_right h1, max_eq_left h2, max_eq_left h3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, nodes₃_two, nodes₃_three]
  let rp := Real.sqrt (5 + 2 * t + t ^ 2)
  let rm := Real.sqrt (5 - 2 * t + t ^ 2)
  have hrp : rp ^ 2 = 5 + 2 * t + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (t + 1)])
  have hrm : rm ^ 2 = 5 - 2 * t + t ^ 2 := Real.sq_sqrt (by nlinarith [sq_nonneg (t - 1)])
  have hrp3 : rp ^ 3 = rp * rp ^ 2 := by ring
  have hrp4 : rp ^ 4 = (rp ^ 2) ^ 2 := by ring
  have hrm3 : rm ^ 3 = rm * rm ^ 2 := by ring
  have hrm4 : rm ^ 4 = (rm ^ 2) ^ 2 := by ring
  norm_num
  change 1 - t - 2 * (1 - t) ^ 4 +
      4 * (-(((t - 1 + rp) / 4 - t) ^ 4) + ((t + 1 + rm) / 4 - t) ^ 4) =
    ((3 + 13 * t + 17 * t ^ 2 + 15 * t ^ 3) * rp +
      (3 - 13 * t + 17 * t ^ 2 - 15 * t ^ 3) * rm) / 8 - 1 - 12 * t ^ 2 - 2 * t ^ 4
  ring_nf
  rw [hrp4, hrp3, hrp, hrm4, hrm3, hrm]
  ring

/-- Elementary algebraic bound `E₃(t) - E₃(0) ≤ -(11 / 32) t^2` on `[0, 1/2]`. -/
theorem e₃_sub_e₃_zero_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    e₃ t - e₃ 0 ≤ -(11 / 32 : ℝ) * t ^ 2 := by
  let s5 := Real.sqrt 5
  let rp := Real.sqrt (5 + 2 * t + t ^ 2)
  let rm := Real.sqrt (5 - 2 * t + t ^ 2)
  let Cp := 3 + 13 * t + 17 * t ^ 2 + 15 * t ^ 3
  let Cm := 3 - 13 * t + 17 * t ^ 2 - 15 * t ^ 3
  have hs5_pos : 0 < s5 := Real.sqrt_pos.mpr (by norm_num)
  have hs5_sq : s5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hrp_ub : rp ≤ s5 + (2 * t + t ^ 2) / (2 * s5) := by
    have hrhs_pos : 0 ≤ s5 + (2 * t + t ^ 2) / (2 * s5) := by positivity
    have hsq : 5 + 2 * t + t ^ 2 ≤ (s5 + (2 * t + t ^ 2) / (2 * s5)) ^ 2 := by
      have hid : (s5 + (2 * t + t ^ 2) / (2 * s5)) ^ 2 - (5 + 2 * t + t ^ 2) =
          (s5 ^ 2 - 5) + ((2 * t + t ^ 2) / (2 * s5)) ^ 2 := by
        field_simp [hs5_pos.ne']
        ring
      have hsq2 : 0 ≤ ((2 * t + t ^ 2) / (2 * s5)) ^ 2 := sq_nonneg _
      linarith
    have hle : Real.sqrt (5 + 2 * t + t ^ 2) ≤ Real.sqrt ((s5 + (2 * t + t ^ 2) / (2 * s5)) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hrhs_pos] at hle
  have hrm_ub : rm ≤ s5 + (-2 * t + t ^ 2) / (2 * s5) := by
    have hrhs_nonneg : 0 ≤ s5 + (-2 * t + t ^ 2) / (2 * s5) := by
      have hnum : 0 ≤ 2 * s5 ^ 2 + (-2 * t + t ^ 2) := by nlinarith
      rw [show s5 + (-2 * t + t ^ 2) / (2 * s5) = (2 * s5 ^ 2 + (-2 * t + t ^ 2)) / (2 * s5) by
        field_simp [hs5_pos.ne']]
      exact div_nonneg hnum (by positivity)
    have hsq : 5 - 2 * t + t ^ 2 ≤ (s5 + (-2 * t + t ^ 2) / (2 * s5)) ^ 2 := by
      have hid : (s5 + (-2 * t + t ^ 2) / (2 * s5)) ^ 2 - (5 - 2 * t + t ^ 2) =
          (s5 ^ 2 - 5) + ((-2 * t + t ^ 2) / (2 * s5)) ^ 2 := by
        field_simp [hs5_pos.ne']
        ring
      have hsq2 : 0 ≤ ((-2 * t + t ^ 2) / (2 * s5)) ^ 2 := sq_nonneg _
      linarith
    have hle : Real.sqrt (5 - 2 * t + t ^ 2) ≤ Real.sqrt ((s5 + (-2 * t + t ^ 2) / (2 * s5)) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hrhs_nonneg] at hle
  have hrm_lb : s5 - t / s5 ≤ rm := by
    have hlhs_nonneg : 0 ≤ s5 - t / s5 := by
      rw [show s5 - t / s5 = (s5 ^ 2 - t) / s5 by field_simp [hs5_pos.ne']]
      exact div_nonneg (by linarith) hs5_pos.le
    have hsq : (s5 - t / s5) ^ 2 ≤ 5 - 2 * t + t ^ 2 := by
      have hid : (5 - 2 * t + t ^ 2) - (s5 - t / s5) ^ 2 = (5 - s5 ^ 2) + (1 - 1 / s5 ^ 2) * t ^ 2 := by
        field_simp [hs5_pos.ne']
        ring
      have h1 : 1 - 1 / s5 ^ 2 = 4 / 5 := by rw [hs5_sq]; norm_num
      have hnonneg : 0 ≤ (1 - 1 / s5 ^ 2) * t ^ 2 := by rw [h1]; positivity
      linarith
    have hle : Real.sqrt ((s5 - t / s5) ^ 2) ≤ Real.sqrt (5 - 2 * t + t ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hlhs_nonneg] at hle
  have hCp_nonneg : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hCm_bound : -Cm ≤ 9 / 8 := by
    have hdiff : 9 / 8 - (-Cm) = (1 / 2 - t) * (33 / 4 - 19 / 2 * t + 15 * t ^ 2) := by
      dsimp [Cm]; ring
    have hq_nonneg : 0 ≤ 33 / 4 - 19 / 2 * t + 15 * t ^ 2 := by
      have : 33 / 4 - 19 / 2 * t + 15 * t ^ 2 = (33 / 4 - 19 / 4 : ℝ) + 19 / 2 * (1 / 2 - t) + 15 * t ^ 2 := by
        ring
      nlinarith [sq_nonneg t]
    have hnonneg : 0 ≤ (1 / 2 - t) * (33 / 4 - 19 / 2 * t + 15 * t ^ 2) :=
      mul_nonneg (by linarith) hq_nonneg
    linarith
  have hCm_term : Cm * rm ≤ Cm * (s5 + (-2 * t + t ^ 2) / (2 * s5)) + (3 / 8 : ℝ) * t ^ 2 := by
    by_cases hCm : 0 ≤ Cm
    · have h1 : Cm * rm ≤ Cm * (s5 + (-2 * t + t ^ 2) / (2 * s5)) :=
        mul_le_mul_of_nonneg_left hrm_ub hCm
      linarith [sq_nonneg t]
    · have hCm_neg : 0 ≤ -Cm := by linarith
      have h1 : Cm * rm ≤ Cm * (s5 - t / s5) := by
        have := mul_le_mul_of_nonneg_left hrm_lb hCm_neg
        linarith
      have h2 : Cm * (s5 - t / s5) - Cm * (s5 + (-2 * t + t ^ 2) / (2 * s5)) =
          (-Cm) * (t ^ 2 / (2 * s5)) := by
        field_simp [hs5_pos.ne']
        ring
      have hs5_ge2 : 2 ≤ s5 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by norm_num)
      have h3 : (-Cm) * (t ^ 2 / (2 * s5)) ≤ (3 / 8 : ℝ) * t ^ 2 := by
        calc
          (-Cm) * (t ^ 2 / (2 * s5)) ≤ (9 / 8 : ℝ) * (t ^ 2 / (2 * 2)) := by
            have : t ^ 2 / (2 * s5) ≤ t ^ 2 / (2 * 2) :=
              div_le_div_of_nonneg_left (sq_nonneg t) (by norm_num) (by linarith)
            exact mul_le_mul hCm_bound this (by positivity) (by norm_num)
          _ = (9 / 32 : ℝ) * t ^ 2 := by ring
          _ ≤ (3 / 8 : ℝ) * t ^ 2 := by nlinarith [sq_nonneg t]
      linarith
  have hCp_term : Cp * rp ≤ Cp * (s5 + (2 * t + t ^ 2) / (2 * s5)) :=
    mul_le_mul_of_nonneg_left hrp_ub hCp_nonneg
  have he₃_zero : e₃ 0 = 6 * s5 / 8 - 1 := by
    unfold e₃
    dsimp [s5]
    ring_nf
  have hlin_id :
      (Cp * (s5 + (2 * t + t ^ 2) / (2 * s5)) +
        Cm * (s5 + (-2 * t + t ^ 2) / (2 * s5)) + (3 / 8 : ℝ) * t ^ 2) / 8 -
        1 - 12 * t ^ 2 - 2 * t ^ 4 - (6 * s5 / 8 - 1) =
      ((199 * s5 / 40 - 12 + 3 / 64 : ℝ) * t ^ 2 + (47 * s5 / 40 - 2 : ℝ) * t ^ 4) := by
    dsimp [Cp, Cm]
    field_simp [hs5_pos.ne']
    ring_nf
    simp only [hs5_sq]
    ring
  have he_diff : e₃ t - e₃ 0 ≤
      (199 * s5 / 40 - 12 + 3 / 64 : ℝ) * t ^ 2 + (47 * s5 / 40 - 2 : ℝ) * t ^ 4 := by
    have he₃_eq : e₃ t = (Cp * rp + Cm * rm) / 8 - 1 - 12 * t ^ 2 - 2 * t ^ 4 := rfl
    rw [he₃_eq, he₃_zero]
    linarith [hCp_term, hCm_term, hlin_id]
  have hc4_pos : 0 ≤ 47 * s5 / 40 - 2 := by
    have : 80 ^ 2 ≤ (47 * s5) ^ 2 := by
      rw [mul_pow, hs5_sq]
      norm_num
    nlinarith
  have ht4_le : t ^ 4 ≤ (1 / 4 : ℝ) * t ^ 2 := by
    have : t ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [sq_nonneg t]
  have hquad_le : (47 * s5 / 40 - 2 : ℝ) * t ^ 4 ≤ (47 * s5 / 40 - 2 : ℝ) * ((1 / 4 : ℝ) * t ^ 2) :=
    mul_le_mul_of_nonneg_left ht4_le hc4_pos
  have hcoeff_lt : (199 * s5 / 40 - 12 + 3 / 64 : ℝ) + (47 * s5 / 40 - 2 : ℝ) / 4 ≤ -(11 / 32) := by
    -- `(843 * √5) / 160 ≤ 12 - 3/64 + 1/2 - 11/32 = 775 / 64`? Let's check exact:
    -- `843 * √5 / 160 ≤ 12 + 1/2 - 3/64 - 11/32 = 775/64` <=> `843 * √5 ≤ 1937.5` (`843^2 * 5 = 3553245 < 3753906.25`)!
    have hbound : 843 * s5 ≤ 1937 := by
      have : (843 * s5) ^ 2 ≤ 1937 ^ 2 := by
        rw [mul_pow, hs5_sq]
        norm_num
      nlinarith
    linarith
  calc
    e₃ t - e₃ 0
        ≤ (199 * s5 / 40 - 12 + 3 / 64 : ℝ) * t ^ 2 + (47 * s5 / 40 - 2 : ℝ) * t ^ 4 := he_diff
    _ ≤ ((199 * s5 / 40 - 12 + 3 / 64 : ℝ) + (47 * s5 / 40 - 2 : ℝ) / 4) * t ^ 2 := by linarith
    _ ≤ -(11 / 32 : ℝ) * t ^ 2 := mul_le_mul_of_nonneg_right hcoeff_lt (sq_nonneg t)

theorem explicitError_orderedNode_three_eq_e₃ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    explicitError 3 (orderedNode 2 t) t = e₃ t := by
  rw [orderedNode_eq_of_strictMono_of_roots 2 t _ (nodes₃_strictMono t) (nodePolynomial_two_roots t)]
  exact explicitError_nodes₃ ht0 ht1

theorem explicitError_orderedNode_three_lt_center {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    explicitError 3 (orderedNode 2 t) t < explicitError 3 (orderedNode 2 0) 0 := by
  rw [explicitError_orderedNode_three_eq_e₃ ht0.le ht1,
    explicitError_orderedNode_three_eq_e₃ (by norm_num) (by norm_num)]
  have h := e₃_sub_e₃_zero_le ht0.le ht1
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht0
  linarith

/-! ### Order `n = 3`: kernel-certified 5-subinterval rational Riemann-sum checker -/

/-- Structural-recursion binary search integer square root on `[0, 1000]`. -/
def natSqrtLoop (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo + 1 ≥ hi then lo
    else
      let mid := (lo + hi) / 2
      if mid * mid ≤ n then natSqrtLoop n fuel mid hi
      else natSqrtLoop n fuel lo mid

def natSqrt1000 (n : ℕ) : ℕ :=
  natSqrtLoop n 11 0 1001

private theorem natSqrtLoop_spec (n fuel lo hi : ℕ)
    (hlo : lo ^ 2 ≤ n) (hhi : n < hi ^ 2) (hlh : lo < hi) (hgap : hi - lo ≤ 2 ^ fuel) :
    (natSqrtLoop n fuel lo hi) ^ 2 ≤ n ∧ n < (natSqrtLoop n fuel lo hi + 1) ^ 2 := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [natSqrtLoop, pow_zero] at *
    have h1 : hi = lo + 1 := by omega
    subst h1
    exact ⟨hlo, hhi⟩
  | succ fuel ih =>
    simp only [natSqrtLoop]
    split_ifs with hstop hmid
    · have h1 : hi = lo + 1 := by omega
      subst h1
      exact ⟨hlo, hhi⟩
    · let mid := (lo + hi) / 2
      have hlm : lo < mid := by dsimp [mid]; omega
      have hmh : mid < hi := by dsimp [mid]; omega
      have h2pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ, Nat.mul_comm]
      have hgap' : hi - mid ≤ 2 ^ fuel := by dsimp [mid]; omega
      exact ih mid hi (by simpa [sq] using hmid) hhi hmh hgap'
    · let mid := (lo + hi) / 2
      have hlm : lo < mid := by dsimp [mid]; omega
      have hmh : mid < hi := by dsimp [mid]; omega
      have h2pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ, Nat.mul_comm]
      have hgap' : mid - lo ≤ 2 ^ fuel := by dsimp [mid]; omega
      have hmid_gt : n < mid ^ 2 := by
        rw [sq]
        exact lt_of_not_ge hmid
      exact ih lo mid hlo hmid_gt hlm hgap'

private theorem natSqrt1000_spec {n : ℕ} (hn : n ≤ 1000 * 1000) :
    (natSqrt1000 n) ^ 2 ≤ n ∧ n < (natSqrt1000 n + 1) ^ 2 :=
  natSqrtLoop_spec n 11 0 1001 (by norm_num) (by omega) (by omega) (by norm_num)

/-- Tight rational upper bound on `√q` with `10⁻³` grid (`q ≤ (sqrtRatUB q)^2` for `q ≤ 1`). -/
def sqrtRatUB (q : ℚ) : ℚ :=
  if q ≤ 0 then 0 else
  let scale : ℕ := 1000
  let n : ℕ := natSqrt1000 ((q.num.natAbs * scale * scale + q.den - 1) / q.den) + 1
  (n : ℚ) / scale

/-- Tight rational lower bound on `√q` with `10⁻³` grid (`(sqrtRatLB q)^2 ≤ q` for `0 ≤ q ≤ 1`). -/
def sqrtRatLB (q : ℚ) : ℚ :=
  if q ≤ 0 then 0 else
  let scale : ℕ := 1000
  let n : ℕ := natSqrt1000 ((q.num.natAbs * scale * scale) / q.den)
  (n : ℚ) / scale

theorem real_sqrt_le_sqrtRatUB {q : ℚ} (hq1 : q ≤ 1) : Real.sqrt (q : ℝ) ≤ (sqrtRatUB q : ℝ) := by
  unfold sqrtRatUB
  split_ifs with hq
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    rw [Real.sqrt_eq_zero_of_nonpos hq']
    norm_num
  · have hq_pos : 0 < q := lt_of_not_ge hq
    have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
    have hnum_le_den : q.num.natAbs ≤ q.den := by
      have h1 : q.num ≤ (q.den : ℤ) := by
        have hq' := hq1
        rw [Rat.le_iff] at hq'
        simpa using hq'
      omega
    have hq_eq : (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
      have h1 : q.num = (q.num.natAbs : ℤ) := (Int.natAbs_of_nonneg hnum_pos.le).symm
      rw [Rat.cast_def]
      nth_rw 1 [h1]
      simp
    let M : ℕ := (q.num.natAbs * 1000 * 1000 + q.den - 1) / q.den
    have hM_le_1000 : M ≤ 1000 * 1000 := by
      dsimp [M]
      rw [Nat.div_le_iff_le_mul_add_pred q.den_pos]
      have h1 : q.num.natAbs * 1000 * 1000 ≤ q.den * 1000000 := by nlinarith
      have hden1 : 1 ≤ q.den := q.den_pos
      omega
    have hM_lt : M < (natSqrt1000 M + 1) ^ 2 := (natSqrt1000_spec hM_le_1000).2
    have hdiv_le : q.num.natAbs * 1000 * 1000 ≤ M * q.den := by
      have hden_pos : 0 < q.den := q.den_pos
      have hdm : M * q.den + (q.num.natAbs * 1000 * 1000 + q.den - 1) % q.den =
          q.num.natAbs * 1000 * 1000 + q.den - 1 := by
        simpa [M, Nat.mul_comm] using Nat.div_add_mod (q.num.natAbs * 1000 * 1000 + q.den - 1) q.den
      have hmod := Nat.mod_lt (q.num.natAbs * 1000 * 1000 + q.den - 1) hden_pos
      have h1 : q.num.natAbs * 1000 * 1000 + q.den - 1 < M * q.den + q.den := by linarith
      omega
    have hnat_lt : q.num.natAbs * 1000 * 1000 < (natSqrt1000 M + 1) ^ 2 * q.den :=
      lt_of_le_of_lt hdiv_le (Nat.mul_lt_mul_of_pos_right hM_lt q.den_pos)
    have hreal_lt : (q : ℝ) < (((natSqrt1000 M + 1 : ℕ) : ℚ) / 1000 : ℝ) ^ 2 := by
      rw [hq_eq]
      have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      have hcast : ((q.num.natAbs * 1000 * 1000 : ℕ) : ℝ) <
          (((natSqrt1000 M + 1) ^ 2 * q.den : ℕ) : ℝ) := by exact_mod_cast hnat_lt
      push_cast at hcast ⊢
      rw [div_pow, div_lt_div_iff₀ hden_pos (by norm_num)]
      nlinarith
    have hnonneg : (0 : ℝ) ≤ (((natSqrt1000 M + 1 : ℕ) : ℚ) / 1000 : ℝ) := by positivity
    calc
      Real.sqrt (q : ℝ) ≤ Real.sqrt ((((natSqrt1000 M + 1 : ℕ) : ℚ) / 1000 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hreal_lt.le
      _ = (((natSqrt1000 M + 1 : ℕ) : ℚ) / 1000 : ℝ) := Real.sqrt_sq hnonneg
      _ = ((((natSqrt1000 M + 1 : ℕ) : ℚ) / 1000 : ℚ) : ℝ) := by push_cast; rfl

theorem sqrtRatLB_le_real_sqrt {q : ℚ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (sqrtRatLB q : ℝ) ≤ Real.sqrt (q : ℝ) := by
  unfold sqrtRatLB
  split_ifs with hq0
  · have h0 : q = 0 := le_antisymm hq0 hq
    subst h0
    norm_num
  · have hq_pos : 0 < q := lt_of_not_ge hq0
    have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
    have hnum_le_den : q.num.natAbs ≤ q.den := by
      have h1 : q.num ≤ (q.den : ℤ) := by
        have hq' := hq1
        rw [Rat.le_iff] at hq'
        simpa using hq'
      omega
    have hq_eq : (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
      have h1 : q.num = (q.num.natAbs : ℤ) := (Int.natAbs_of_nonneg hnum_pos.le).symm
      rw [Rat.cast_def]
      nth_rw 1 [h1]
      simp
    let M : ℕ := (q.num.natAbs * 1000 * 1000) / q.den
    have hM_le_1000 : M ≤ 1000 * 1000 := by
      dsimp [M]
      exact Nat.div_le_of_le_mul (by nlinarith)
    have hM_le : (natSqrt1000 M) ^ 2 ≤ M := (natSqrt1000_spec hM_le_1000).1
    have hdiv_le : M * q.den ≤ q.num.natAbs * 1000 * 1000 := Nat.div_mul_le_self _ _
    have hnat_le : (natSqrt1000 M) ^ 2 * q.den ≤ q.num.natAbs * 1000 * 1000 :=
      (Nat.mul_le_mul_right q.den hM_le).trans hdiv_le
    have hreal_le : (((natSqrt1000 M : ℕ) : ℚ) / 1000 : ℝ) ^ 2 ≤ (q : ℝ) := by
      rw [hq_eq]
      have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      have hcast : (((natSqrt1000 M) ^ 2 * q.den : ℕ) : ℝ) ≤
          ((q.num.natAbs * 1000 * 1000 : ℕ) : ℝ) := by exact_mod_cast hnat_le
      push_cast at hcast ⊢
      rw [div_pow, div_le_div_iff₀ (by norm_num) hden_pos]
      nlinarith
    have hnonneg : (0 : ℝ) ≤ (((natSqrt1000 M : ℕ) : ℚ) / 1000 : ℝ) := by positivity
    calc
      ((((natSqrt1000 M : ℕ) : ℚ) / 1000 : ℚ) : ℝ)
          = (((natSqrt1000 M : ℕ) : ℚ) / 1000 : ℝ) := by push_cast; rfl
      _ = Real.sqrt ((((natSqrt1000 M : ℕ) : ℚ) / 1000 : ℝ) ^ 2) := (Real.sqrt_sq hnonneg).symm
      _ ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hreal_le

/-- Unnormalized nonnegative fraction `(num, den)` representing `num / den`, with zero `gcd`
overhead so kernel `decide` reduces cleanly. -/
abbrev NFrac := ℕ × ℕ

noncomputable def nfVal (x : NFrac) : ℝ := (x.1 : ℝ) / (x.2 : ℝ)

def nfAdd (x y : NFrac) : NFrac := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)
def nfSub (x y : NFrac) : NFrac := (x.1 * y.2 - y.1 * x.2, x.2 * y.2)
def nfMul (x y : NFrac) : NFrac := (x.1 * y.1, x.2 * y.2)
def nfDiv (x y : NFrac) : NFrac := (x.1 * y.2, x.2 * y.1)
def nfPow (x : NFrac) (k : ℕ) : NFrac := (x.1 ^ k, x.2 ^ k)

/-- Ceiling of `(x.1 / x.2) * K` as a natural number (so `nfVal x ≤ nfCeil K x / K`). -/
def nfCeil (K : ℕ) (x : NFrac) : ℕ :=
  (x.1 * K + x.2 - 1) / x.2

/-- Upper bound `√(x.1 / x.2)` on `[0, 1]` using `natSqrt1000` in units of `10⁻³`. -/
def nfSqrtUB (x : NFrac) : NFrac :=
  if x.1 = 0 then (0, 1)
  else (natSqrt1000 ((x.1 * 1000 * 1000 + x.2 - 1) / x.2) + 1, 1000)

/-- Lower bound `√(x.1 / x.2)` on `[0, 1]` using `natSqrt1000` in units of `10⁻³`. -/
def nfSqrtLB (x : NFrac) : NFrac :=
  (natSqrt1000 ((x.1 * 1000 * 1000) / x.2), 1000)

theorem nfVal_le_nfCeil (K : ℕ) (hK : 0 < K) (x : NFrac) (hx : 0 < x.2) :
    nfVal x ≤ (nfCeil K x : ℝ) / (K : ℝ) := by
  unfold nfVal nfCeil
  have hx' : (0 : ℝ) < x.2 := by exact_mod_cast hx
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_div_iff₀ hx' hK']
  have hdm : ((x.1 * K + x.2 - 1) / x.2) * x.2 + (x.1 * K + x.2 - 1) % x.2 =
      x.1 * K + x.2 - 1 := by
    simpa [Nat.mul_comm] using Nat.div_add_mod (x.1 * K + x.2 - 1) x.2
  have hmod := Nat.mod_lt (x.1 * K + x.2 - 1) hx
  have hnat : x.1 * K ≤ ((x.1 * K + x.2 - 1) / x.2) * x.2 := by omega
  exact_mod_cast hnat

theorem real_sqrt_nfVal_le_nfSqrtUB {x : NFrac} (hx : 0 < x.2) (hx1 : x.1 ≤ x.2) :
    Real.sqrt (nfVal x) ≤ nfVal (nfSqrtUB x) := by
  unfold nfSqrtUB nfVal
  by_cases hx0 : x.1 = 0
  · simp [hx0]
  · simp only [hx0, ↓reduceIte]
    let M : ℕ := (x.1 * 1000 * 1000 + x.2 - 1) / x.2
    have hM_le : M ≤ 1000 * 1000 := by
      dsimp [M]
      rw [Nat.div_le_iff_le_mul_add_pred hx]
      have h1 : x.1 * 1000 * 1000 ≤ x.2 * 1000000 := by nlinarith
      omega
    have hM_lt : M < (natSqrt1000 M + 1) ^ 2 := (natSqrt1000_spec hM_le).2
    have hdm : M * x.2 + (x.1 * 1000 * 1000 + x.2 - 1) % x.2 =
        x.1 * 1000 * 1000 + x.2 - 1 := by
      simpa [M, Nat.mul_comm] using Nat.div_add_mod (x.1 * 1000 * 1000 + x.2 - 1) x.2
    have hmod := Nat.mod_lt (x.1 * 1000 * 1000 + x.2 - 1) hx
    have hdiv_le : x.1 * 1000 * 1000 ≤ M * x.2 := by omega
    have hnat_lt : x.1 * 1000 * 1000 < (natSqrt1000 M + 1) ^ 2 * x.2 :=
      lt_of_le_of_lt hdiv_le (Nat.mul_lt_mul_of_pos_right hM_lt hx)
    have hreal_lt : (x.1 : ℝ) / (x.2 : ℝ) < ((natSqrt1000 M + 1 : ℕ) : ℝ) ^ 2 / 1000 ^ 2 := by
      have hx' : (0 : ℝ) < x.2 := by exact_mod_cast hx
      rw [div_lt_div_iff₀ hx' (by norm_num)]
      have hcast : ((x.1 * 1000 * 1000 : ℕ) : ℝ) < (((natSqrt1000 M + 1) ^ 2 * x.2 : ℕ) : ℝ) := by
        exact_mod_cast hnat_lt
      push_cast at hcast ⊢
      nlinarith
    have hnonneg : (0 : ℝ) ≤ ((natSqrt1000 M + 1 : ℕ) : ℝ) / 1000 := by positivity
    calc
      Real.sqrt ((x.1 : ℝ) / (x.2 : ℝ))
          ≤ Real.sqrt ((((natSqrt1000 M + 1 : ℕ) : ℝ) / 1000) ^ 2) := by
            apply Real.sqrt_le_sqrt
            rw [div_pow]
            exact hreal_lt.le
      _ = ((natSqrt1000 M + 1 : ℕ) : ℝ) / (1000 : ℕ) := by
            rw [Real.sqrt_sq hnonneg]; norm_num

theorem nfSqrtLB_le_real_sqrt_nfVal {x : NFrac} (hx : 0 < x.2) (hx1 : x.1 ≤ x.2) :
    nfVal (nfSqrtLB x) ≤ Real.sqrt (nfVal x) := by
  unfold nfSqrtLB nfVal
  let M : ℕ := (x.1 * 1000 * 1000) / x.2
  have hM_le_1000 : M ≤ 1000 * 1000 := by
    dsimp [M]
    exact Nat.div_le_of_le_mul (by nlinarith)
  have hM_le : (natSqrt1000 M) ^ 2 ≤ M := (natSqrt1000_spec hM_le_1000).1
  have hdiv_le : M * x.2 ≤ x.1 * 1000 * 1000 := Nat.div_mul_le_self _ _
  have hnat_le : (natSqrt1000 M) ^ 2 * x.2 ≤ x.1 * 1000 * 1000 :=
    (Nat.mul_le_mul_right x.2 hM_le).trans hdiv_le
  have hreal_le : ((natSqrt1000 M : ℕ) : ℝ) ^ 2 / 1000 ^ 2 ≤ (x.1 : ℝ) / (x.2 : ℝ) := by
    have hx' : (0 : ℝ) < x.2 := by exact_mod_cast hx
    rw [div_le_div_iff₀ (by norm_num) hx']
    have hcast : (((natSqrt1000 M) ^ 2 * x.2 : ℕ) : ℝ) ≤ ((x.1 * 1000 * 1000 : ℕ) : ℝ) := by
      exact_mod_cast hnat_le
    push_cast at hcast ⊢
    nlinarith
  have hnonneg : (0 : ℝ) ≤ ((natSqrt1000 M : ℕ) : ℝ) / 1000 := by positivity
  calc
    ((natSqrt1000 M : ℕ) : ℝ) / (1000 : ℕ)
        = Real.sqrt ((((natSqrt1000 M : ℕ) : ℝ) / 1000) ^ 2) := by
          rw [Real.sqrt_sq hnonneg]; norm_num
    _ ≤ Real.sqrt ((x.1 : ℝ) / (x.2 : ℝ)) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow]
          exact hreal_le

def nfFloor (K : ℕ) (x : NFrac) : ℕ :=
  (x.1 * K) / x.2

theorem nfFloor_le_nfVal (K : ℕ) (hK : 0 < K) (x : NFrac) (hx : 0 < x.2) :
    (nfFloor K x : ℝ) / (K : ℝ) ≤ nfVal x := by
  unfold nfVal nfFloor
  have hx' : (0 : ℝ) < x.2 := by exact_mod_cast hx
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_div_iff₀ hK' hx']
  have hnat : ((x.1 * K) / x.2) * x.2 ≤ x.1 * K := Nat.div_mul_le_self _ _
  exact_mod_cast hnat

/-- Fixed-point `10⁻⁶`/`10⁻⁹` upper-bound box contribution for `R_3` over `[t_0, t_1]`
with zero denominator growth so kernel `decide` reduces instantaneously. -/
def sumNatRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumNatRange f k + f k

def natCeil (K a b : ℕ) : ℕ := (a * K + b - 1) / b
def natFloor (K a b : ℕ) : ℕ := (a * K) / b

theorem natDiv_le_natCeil (K a b : ℕ) (hK : 0 < K) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (natCeil K a b : ℝ) / (K : ℝ) :=
  nfVal_le_nfCeil K hK (a, b) hb

theorem natFloor_le_natDiv (K a b : ℕ) (hK : 0 < K) (hb : 0 < b) :
    (natFloor K a b : ℝ) / (K : ℝ) ≤ (a : ℝ) / (b : ℝ) :=
  nfFloor_le_nfVal K hK (a, b) hb

def n3QHi (diff_n Dx : ℕ) : ℕ :=
  natSqrt1000 ((diff_n * 1000 * 1000 + Dx - 1) / Dx) + 1

def n3RLo (a2_1_n s1_d : ℕ) : ℕ :=
  natSqrt1000 ((a2_1_n * 1000 * 1000) / s1_d)

def n3BoxDensityUB (p0 q0 p1 q1 Nx k : ℕ) : ℕ :=
  let K6 : ℕ := 1000000
  let K9 : ℕ := 1000000000
  let s0_n := p0 * p0
  let s0_d := q0 * q0
  let s1_n := p1 * p1
  let s1_d := q1 * q1
  let Dx := s0_d * Nx
  let dx_n := s0_d - s0_n
  let xL_n := s0_n * Nx + k * dx_n
  let xR_n := xL_n + dx_n
  let diff_n := (k + 1) * dx_n
  let q_hi_n := n3QHi diff_n Dx
  let D0_lo_n := s0_d * Dx - (2 * Dx - xL_n) * s0_n
  let D0_hi_n := s0_d * Dx - (2 * Dx - xR_n) * s0_n
  let D1_lo_n := s1_d * Dx - (2 * Dx - xL_n) * s1_n
  let phi2_hi_6 := natCeil K6 (diff_n * s0_d) D0_lo_n
  let xL_6 := natFloor K6 xL_n Dx
  let xL2_6 := (xL_6 * xL_6) / K6
  let xL3_6 := (xL2_6 * xL_6) / K6
  let xL4_6 := (xL2_6 * xL2_6) / K6
  let fac_6 := natFloor K6 (dx_n * Dx) D0_hi_n
  let S_eff_lo_6 := K6 + xL_6 + xL2_6 + xL3_6 + (xL4_6 * fac_6) / K6
  let xR_6 := natCeil K6 xR_n Dx
  let xR2_6 := natCeil K6 (xR_6 * xR_6) (K6 * K6)
  let xR4_6 := natCeil K6 (xR2_6 * xR2_6) (K6 * K6)
  let omxL_6 := natCeil K6 (Dx - xL_n) Dx
  let D1_lo_6 := natFloor K6 D1_lo_n (s1_d * Dx)
  let t1_9 := natCeil K9 (omxL_6 * omxL_6 * xR4_6 * phi2_hi_6 * q_hi_n)
    (2 * D1_lo_6 * S_eff_lo_6 * K6 * K6 * 1000)
  let t2_9 := natCeil K9 (4 * omxL_6 * xR4_6 * (s1_d - s1_n) * q_hi_n * K6 * K6)
    (D1_lo_6 * D1_lo_6 * S_eff_lo_6 * S_eff_lo_6 * s1_d * 1000)
  t1_9 + t2_9

def n3BlockBoxCeil (p0 q0 p1 q1 Nx k : ℕ) : ℕ :=
  let K9 : ℕ := 1000000000
  let Dx := q0 * q0 * Nx
  let dx_n := q0 * q0 - p0 * p0
  natCeil K9 (dx_n * n3BoxDensityUB p0 q0 p1 q1 Nx k) (Dx * K9)

/-- Binary-tree sum `∑_{k=0}^{2^d-1} f k` on `ℕ` (depth `d` instead of `2^d`) for fast kernel `decide`. -/
def sumNatPow2 (f : ℕ → ℕ) (lo : ℕ) : ℕ → ℕ
  | 0 => f lo
  | d + 1 => sumNatPow2 f lo d + sumNatPow2 f (lo + 2 ^ d) d

theorem sumNatPow2_eq_sum (f : ℕ → ℕ) (lo d : ℕ) :
    sumNatPow2 f lo d = ∑ k ∈ Finset.range (2 ^ d), f (lo + k) := by
  induction d generalizing lo with
  | zero => simp [sumNatPow2]
  | succ d ih =>
    rw [sumNatPow2, ih lo, ih (lo + 2 ^ d), show 2 ^ (d + 1) = 2 ^ d + 2 ^ d by ring,
      Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_assoc]

/-- Kernel-computable checker for `[p0/q0, p1/q1]` with `2^d` uniform `x`-subintervals. -/
def checkN3BlockPow2 (p0 q0 p1 q1 d : ℕ) : Bool :=
  let K9 : ℕ := 1000000000
  let s1_n := p1 * p1
  let s1_d := q1 * q1
  let r_sum : ℕ := sumNatPow2 (n3BlockBoxCeil p0 q0 p1 q1 (2 ^ d)) 0 d
  let a2_1_n := s1_d - s1_n
  let r_lo_n := n3RLo a2_1_n s1_d
  let mlb_n := 176 * a2_1_n ^ 3 * r_lo_n * s1_d
  let mlb_d := 315 * s1_d ^ 3 * 1000 * (11 * s1_d - 8 * s1_n)
  decide (r_sum * mlb_d < mlb_n * K9)

theorem n3_block0_certified : checkN3BlockPow2 0 1 1 4 4 = true := by decide
theorem n3_block1_certified : checkN3BlockPow2 1 4 7 20 4 = true := by decide
theorem n3_block2_certified : checkN3BlockPow2 7 20 21 50 5 = true := by decide
theorem n3_block3_certified : checkN3BlockPow2 21 50 23 50 5 = true := by decide
theorem n3_block4_certified : checkN3BlockPow2 23 50 1 2 7 = true := by decide

/-! ### Soundness of the 5-block certificate and `0 < chordDelta 3 t` -/

private theorem mainTerm_three_monotone_s {s s1 : ℝ} (_hs : 0 ≤ s) (hs1 : s ≤ s1) (hs1_le : s1 ≤ 1 / 4) :
    (1 - s1) ^ 3 * Real.sqrt (1 - s1) / (11 - 8 * s1) ≤
      (1 - s) ^ 3 * Real.sqrt (1 - s) / (11 - 8 * s) := by
  have h1s1 : 0 < 1 - s1 := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hden1 : 0 < 11 - 8 * s1 := by linarith
  have hden : 0 < 11 - 8 * s := by linarith
  have hfrac : (1 - s1) / (11 - 8 * s1) ≤ (1 - s) / (11 - 8 * s) := by
    rw [div_le_div_iff₀ hden1 hden]
    nlinarith
  have hsq : (1 - s1) ^ 2 ≤ (1 - s) ^ 2 := by nlinarith
  have hrt : Real.sqrt (1 - s1) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
  have hmul : (1 - s1) ^ 2 * Real.sqrt (1 - s1) ≤ (1 - s) ^ 2 * Real.sqrt (1 - s) :=
    mul_le_mul hsq hrt (Real.sqrt_nonneg _) (by positivity)
  have hdiv : ((1 - s1) / (11 - 8 * s1)) * ((1 - s1) ^ 2 * Real.sqrt (1 - s1)) ≤
      ((1 - s) / (11 - 8 * s)) * ((1 - s) ^ 2 * Real.sqrt (1 - s)) :=
    mul_le_mul hfrac hmul (by positivity) (by positivity)
  calc
    (1 - s1) ^ 3 * Real.sqrt (1 - s1) / (11 - 8 * s1)
        = ((1 - s1) / (11 - 8 * s1)) * ((1 - s1) ^ 2 * Real.sqrt (1 - s1)) := by ring
    _ ≤ ((1 - s) / (11 - 8 * s)) * ((1 - s) ^ 2 * Real.sqrt (1 - s)) := hdiv
    _ = (1 - s) ^ 3 * Real.sqrt (1 - s) / (11 - 8 * s) := by ring

private theorem mainTerm_three_ge_block {t t1 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ t1) (ht1_half : t1 ≤ 1 / 2) :
    (176 / 315 : ℝ) * (1 - t1 ^ 2) ^ 3 * Real.sqrt (1 - t1 ^ 2) / (11 - 8 * t1 ^ 2) ≤
      ∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2),
        (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v) := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ht_half : t ≤ 1 / 2 := ht1.trans ht1_half
  have ha2_eq : a ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  have hsub : (∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) =
      a ^ 7 * ∫ w in (0 : ℝ)..1, ((1 - w ^ 2) ^ 3 * w ^ 2) / (a ^ 2 + t ^ 2 * w ^ 2) := by
    have hcomp := intervalIntegral.integral_comp_mul_left
      (fun v => (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) ha_pos.ne' (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at hcomp
    have hleft : (∫ w in (0 : ℝ)..1, (1 - chordX t (a * w)) ^ 3 * ((a * w) ^ 2 / chordD t (a * w))) =
        a ^ 6 * ∫ w in (0 : ℝ)..1, ((1 - w ^ 2) ^ 3 * w ^ 2) / (a ^ 2 + t ^ 2 * w ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun w _ => ?_
      have h1x : 1 - chordX t (a * w) = a ^ 2 * (1 - w ^ 2) := by
        unfold chordX; rw [mul_pow, ha2_eq]; ring
      have hD_eq : chordD t (a * w) = a ^ 2 * (a ^ 2 + t ^ 2 * w ^ 2) := by
        unfold chordD; rw [← ha2_eq]; ring
      rw [h1x, hD_eq, mul_pow]
      have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha_pos.ne'
      field_simp [ha2_ne]
    have hcomp' : (∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) =
        a * ∫ w in (0 : ℝ)..1, (1 - chordX t (a * w)) ^ 3 * ((a * w) ^ 2 / chordD t (a * w)) := by
      rw [hcomp, smul_eq_mul]
      field_simp [ha_pos.ne']
    rw [hcomp', hleft]
    ring
  let f : ℝ → ℝ := fun w => (1 - w ^ 2) ^ 3 * w ^ 2
  let g : ℝ → ℝ := fun w => a ^ 2 + t ^ 2 * w ^ 2
  have hf_cont : ContinuousOn f (Icc 0 1) :=
    (((continuous_const.sub (continuous_pow 2)).pow 3).mul (continuous_pow 2)).continuousOn
  have hg_cont : ContinuousOn g (Icc 0 1) :=
    (continuous_const.add (continuous_const.mul (continuous_pow 2))).continuousOn
  have hf_nonneg : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ f w := by
    intro w hw
    have h1w : 0 ≤ 1 - w ^ 2 := by nlinarith [hw.1, hw.2]
    exact mul_nonneg (pow_nonneg h1w 3) (sq_nonneg w)
  have hg_pos : ∀ w ∈ Icc (0 : ℝ) 1, 0 < g w := fun w _ => by dsimp [g]; positivity
  have hJ : wallisJ 3 = (3 / 11 : ℝ) * wallisI 3 := by
    have h := wallisJ_eq_mul_wallisI 3
    norm_num at h
    linarith
  have hI3 : wallisI 3 = 16 / 315 := by
    rw [wallisI_eq_rat 3]
    norm_num [wallisIRat]
  have hA_eq : (∫ w in (0 : ℝ)..1, f w * g w) = (a ^ 2 + 3 * t ^ 2 / 11) * wallisI 3 := by
    have hcongr : (fun w => f w * g w) =
        fun w => a ^ 2 * ((1 - w ^ 2) ^ 3 * w ^ 2) + t ^ 2 * ((1 - w ^ 2) ^ 3 * w ^ 4) := by
      ext w; dsimp [f, g]; ring
    rw [hcongr, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · change a ^ 2 * wallisI 3 + t ^ 2 * wallisJ 3 = _
      rw [hJ]
      ring
    · exact (hf_cont.const_mul (a ^ 2)).intervalIntegrable_of_Icc zero_le_one
    · exact (((continuous_const.sub (continuous_pow 2)).pow 3 |>.mul (continuous_pow 4)).continuousOn.const_mul
        (t ^ 2)).intervalIntegrable_of_Icc zero_le_one
  have hA_pos : 0 < ∫ w in (0 : ℝ)..1, f w * g w := by
    rw [hA_eq, hI3]
    have hden : 0 < a ^ 2 + 3 * t ^ 2 / 11 := by positivity
    positivity
  have hCS := cauchy_schwarz_div_le hf_cont hg_cont hf_nonneg hg_pos hA_pos
  have hB_eq : (∫ w in (0 : ℝ)..1, f w) = wallisI 3 := rfl
  rw [hB_eq, hA_eq] at hCS
  have hden_eq : a ^ 2 + 3 * t ^ 2 / 11 = (11 - 8 * t ^ 2) / 11 := by rw [ha2_eq]; ring
  have hden_pos : 0 < 11 - 8 * t ^ 2 := by nlinarith
  have ha7 : a ^ 7 = (1 - t ^ 2) ^ 3 * a := by
    calc
      a ^ 7 = (a ^ 2) ^ 3 * a := by ring
      _ = (1 - t ^ 2) ^ 3 * a := by rw [ha2_eq]
  have hCS' : (16 / 315 : ℝ) / ((11 - 8 * t ^ 2) / 11) ≤ ∫ w in (0 : ℝ)..1, f w / g w := by
    rw [hI3, hden_eq] at hCS
    have heq : (16 / 315 : ℝ) ^ 2 / ((11 - 8 * t ^ 2) / 11 * (16 / 315)) =
        (16 / 315 : ℝ) / ((11 - 8 * t ^ 2) / 11) := by
      field_simp [hden_pos.ne']
    linarith
  have hbound : (176 / 315 : ℝ) * (1 - t ^ 2) ^ 3 * a / (11 - 8 * t ^ 2) ≤
      a ^ 7 * ∫ w in (0 : ℝ)..1, f w / g w := by
    have hmul := mul_le_mul_of_nonneg_left hCS' (pow_nonneg ha_pos.le 7)
    calc
      (176 / 315 : ℝ) * (1 - t ^ 2) ^ 3 * a / (11 - 8 * t ^ 2)
          = ((1 - t ^ 2) ^ 3 * a) * ((16 / 315 : ℝ) / ((11 - 8 * t ^ 2) / 11)) := by
            field_simp [hden_pos.ne']; ring
      _ = a ^ 7 * ((16 / 315 : ℝ) / ((11 - 8 * t ^ 2) / 11)) := by rw [ha7]
      _ ≤ a ^ 7 * ∫ w in (0 : ℝ)..1, f w / g w := hmul
  have hs_le : t ^ 2 ≤ t1 ^ 2 := by nlinarith
  have hs1_le : t1 ^ 2 ≤ 1 / 4 := by nlinarith
  have hmono := mainTerm_three_monotone_s (sq_nonneg t) hs_le hs1_le
  have hmono' : (176 / 315 : ℝ) * (1 - t1 ^ 2) ^ 3 * Real.sqrt (1 - t1 ^ 2) / (11 - 8 * t1 ^ 2) ≤
      (176 / 315 : ℝ) * (1 - t ^ 2) ^ 3 * a / (11 - 8 * t ^ 2) := by
    dsimp [a]
    calc
      (176 / 315 : ℝ) * (1 - t1 ^ 2) ^ 3 * Real.sqrt (1 - t1 ^ 2) / (11 - 8 * t1 ^ 2)
          = (176 / 315 : ℝ) * ((1 - t1 ^ 2) ^ 3 * Real.sqrt (1 - t1 ^ 2) / (11 - 8 * t1 ^ 2)) := by ring
      _ ≤ (176 / 315 : ℝ) * ((1 - t ^ 2) ^ 3 * Real.sqrt (1 - t ^ 2) / (11 - 8 * t ^ 2)) := by
          gcongr
      _ = (176 / 315 : ℝ) * (1 - t ^ 2) ^ 3 * Real.sqrt (1 - t ^ 2) / (11 - 8 * t ^ 2) := by ring
  calc
    (176 / 315 : ℝ) * (1 - t1 ^ 2) ^ 3 * Real.sqrt (1 - t1 ^ 2) / (11 - 8 * t1 ^ 2)
        ≤ (176 / 315 : ℝ) * (1 - t ^ 2) ^ 3 * a / (11 - 8 * t ^ 2) := hmono'
    _ ≤ a ^ 7 * ∫ w in (0 : ℝ)..1, f w / g w := hbound
    _ = ∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v) := hsub.symm

private theorem one_sub_div_chordD_sq_antitone {s s1 x : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ s1) (hs1_le : s1 ≤ 1 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - s) / (1 - (2 - x) * s) ^ 2 ≤ (1 - s1) / (1 - (2 - x) * s1) ^ 2 := by
  have hD0 : 0 < 1 - (2 - x) * s := by nlinarith
  have hD1 : 0 < 1 - (2 - x) * s1 := by nlinarith
  rw [div_le_div_iff₀ (sq_pos_of_pos hD0) (sq_pos_of_pos hD1)]
  let k : ℝ := 2 - x
  have hk1 : 1 ≤ k := by dsimp [k]; linarith
  have hk2 : k ≤ 2 := by dsimp [k]; linarith
  have hprod : s + s1 - s * s1 ≤ 7 / 16 := by nlinarith
  have hquad : 0 ≤ 2 * k - 1 - k ^ 2 * (s + s1 - s * s1) := by
    have hk_sq : k ^ 2 * (s + s1 - s * s1) ≤ k ^ 2 * (7 / 16) :=
      mul_le_mul_of_nonneg_left hprod (sq_nonneg k)
    have hpoly : 0 ≤ 2 * k - 1 - k ^ 2 * (7 / 16) := by nlinarith
    linarith
  have hdiff : (1 - s1) * (1 - k * s) ^ 2 - (1 - s) * (1 - k * s1) ^ 2 =
      (s1 - s) * (2 * k - 1 - k ^ 2 * (s + s1 - s * s1)) := by ring
  have hnonneg : 0 ≤ (s1 - s) * (2 * k - 1 - k ^ 2 * (s + s1 - s * s1)) :=
    mul_nonneg (by linarith) hquad
  change (1 - s) * (1 - k * s1) ^ 2 ≤ (1 - s1) * (1 - k * s) ^ 2
  linarith

private theorem one_sub_div_chordD_ge {s0 s x : ℝ}
    (hs0 : 0 ≤ s0) (hs : s0 ≤ s) (hs_le : s ≤ 1 / 4) (hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    (1 - s0) / (1 - (2 - x) * s0) ≤ (1 - s) / (1 - (2 - x) * s) := by
  have hD0 : 0 < 1 - (2 - x) * s0 := by nlinarith
  have hD : 0 < 1 - (2 - x) * s := by nlinarith
  rw [div_le_div_iff₀ hD0 hD]
  nlinarith

private theorem sub_div_chordD_le {s0 s x : ℝ}
    (hs0 : 0 ≤ s0) (hs : s0 ≤ s) (hs_le : s ≤ 1 / 4) (hsx : s ≤ x) (_hx1 : x ≤ 1) :
    (x - s) / (1 - (2 - x) * s) ≤ (x - s0) / (1 - (2 - x) * s0) := by
  have hD : 0 < 1 - (2 - x) * s := by nlinarith
  have hD0 : 0 < 1 - (2 - x) * s0 := by nlinarith
  rw [div_le_div_iff₀ hD hD0]
  have hsq : 0 ≤ (s - s0) * (1 - x) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hid : (x - s0) * (1 - (2 - x) * s) - (x - s) * (1 - (2 - x) * s0) =
      (s - s0) * (1 - x) ^ 2 := by ring
  linarith

private theorem chordD_eq_one_sub_chordX (t v : ℝ) :
    chordD t v = 1 - (2 - chordX t v) * t ^ 2 := by
  unfold chordD chordX
  ring

private noncomputable def rem3ActS (t v : ℝ) : ℝ :=
  let x := chordX t v
  1 + x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - t ^ 2) / chordD t v)

private theorem rem3ActS_ge_one {t v : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    1 ≤ rem3ActS t v := by
  unfold rem3ActS
  have hx : 0 ≤ chordX t v := by unfold chordX; positivity
  have hD : 0 < chordD t v := chordD_pos ht1 ht0 v
  have ht1_nn : 0 ≤ 1 - t ^ 2 := by nlinarith
  have : 0 ≤ chordX t v + chordX t v ^ 2 + chordX t v ^ 3 +
      chordX t v ^ 4 * ((1 - t ^ 2) / chordD t v) := by positivity
  linarith

private theorem one_sub_zNorm_three_eq {t v : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    1 - ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * 3 + 2) *
        (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖ =
      (1 - chordX t v) * rem3ActS t v := by
  rw [norm_reflection_z_eq t 3 v]
  have hD : (chordD t v : ℝ) ≠ 0 := (chordD_pos ht1 ht0 v).ne'
  unfold rem3ActS
  field_simp [hD]
  unfold chordD chordX
  ring

private noncomputable def rem3Clean (t v : ℝ) : ℝ :=
  let x := chordX t v
  let D := chordD t v
  let S := rem3ActS t v
  (1 - x) ^ 2 * x ^ 4 * (v ^ 2 / D) ^ 2 / S +
    8 * (1 - x) * x ^ 4 * ((1 - t ^ 2) / D ^ 2) * v ^ 2 / S ^ 2

private noncomputable def rem3Upper (s0 s1 x : ℝ) : ℝ :=
  let D0 := 1 - (2 - x) * s0
  let D1 := 1 - (2 - x) * s1
  let S := 1 + x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - s0) / D0)
  (1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0) * Real.sqrt (x - s0) / (2 * D1 * S) +
    4 * (1 - x) * x ^ 4 * (1 - s1) * Real.sqrt (x - s0) / (D1 ^ 2 * S ^ 2)

private theorem continuousOn_rem3Upper {s0 s1 : ℝ} (hs0 : 0 ≤ s0) (hs0_lt : s0 ≤ 1 / 4)
    (hs1 : 0 ≤ s1) (hs1_le : s1 ≤ 1 / 4) :
    ContinuousOn (rem3Upper s0 s1) (Icc 0 1) := by
  let D0 : ℝ → ℝ := fun x => 1 - (2 - x) * s0
  let D1 : ℝ → ℝ := fun x => 1 - (2 - x) * s1
  let S : ℝ → ℝ := fun x => 1 + x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - s0) / D0 x)
  have hD0_cont : ContinuousOn D0 (Icc 0 1) :=
    (continuous_const.sub ((continuous_const.sub continuous_id).mul continuous_const)).continuousOn
  have hD1_cont : ContinuousOn D1 (Icc 0 1) :=
    (continuous_const.sub ((continuous_const.sub continuous_id).mul continuous_const)).continuousOn
  have hD0_pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < D0 x := fun x hx => by
    dsimp [D0]; nlinarith [hx.1, hx.2]
  have hD1_pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < D1 x := fun x hx => by
    dsimp [D1]; nlinarith [hx.1, hx.2]
  have hS_cont : ContinuousOn S (Icc 0 1) :=
    ((((continuous_const.add continuous_id).add (continuous_pow 2)).add (continuous_pow 3)).continuousOn).add
      ((continuous_pow 4).continuousOn.mul (continuousOn_const.div hD0_cont fun x hx => (hD0_pos x hx).ne'))
  have hS_pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < S x := fun x hx => by
    dsimp [S]
    have hD0p := hD0_pos x hx
    have h1s0 : 0 ≤ 1 - s0 := by linarith
    have hx0 : 0 ≤ x := hx.1
    positivity
  have hsqrt_cont : ContinuousOn (fun x => Real.sqrt (x - s0)) (Icc 0 1) :=
    (continuous_id.sub continuous_const).sqrt.continuousOn
  have hnum1 : ContinuousOn (fun x => (1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0 x) * Real.sqrt (x - s0)) (Icc 0 1) :=
    ((((continuous_const.sub continuous_id).pow 2).continuousOn.mul (continuous_pow 4).continuousOn).mul
      ((continuous_id.sub continuous_const).continuousOn.div hD0_cont fun x hx => (hD0_pos x hx).ne')).mul
      hsqrt_cont
  have hden1 : ContinuousOn (fun x => 2 * D1 x * S x) (Icc 0 1) :=
    (continuousOn_const.mul hD1_cont).mul hS_cont
  have hnum2 : ContinuousOn (fun x => 4 * (1 - x) * x ^ 4 * (1 - s1) * Real.sqrt (x - s0)) (Icc 0 1) :=
    (((continuousOn_const.mul (continuous_const.sub continuous_id).continuousOn).mul
      (continuous_pow 4).continuousOn).mul continuousOn_const).mul hsqrt_cont
  have hden2 : ContinuousOn (fun x => (D1 x) ^ 2 * (S x) ^ 2) (Icc 0 1) :=
    (hD1_cont.pow 2).mul (hS_cont.pow 2)
  exact (hnum1.div hden1 fun x hx => by
      have hD1p := hD1_pos x hx; have hSp := hS_pos x hx; positivity).add
    (hnum2.div hden2 fun x hx => by
      have hD1p := hD1_pos x hx; have hSp := hS_pos x hx; positivity)

private theorem rem3Clean_continuousOn {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    ContinuousOn (rem3Clean t) (Icc 0 (Real.sqrt (1 - t ^ 2))) := by
  have hD_cont : Continuous (chordD t) := by
    unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
  have hx_cont : Continuous (chordX t) := by
    unfold chordX; exact continuous_const.add (continuous_pow 2)
  have hD_ne : ∀ v : ℝ, chordD t v ≠ 0 := fun v => (chordD_pos ht1 ht0 v).ne'
  have hS_cont : Continuous (rem3ActS t) := by
    unfold rem3ActS
    exact ((((continuous_const.add hx_cont).add (hx_cont.pow 2)).add (hx_cont.pow 3))).add
      ((hx_cont.pow 4).mul (continuous_const.div hD_cont hD_ne))
  have hS_ne : ∀ v : ℝ, rem3ActS t v ≠ 0 := fun v =>
    (lt_of_lt_of_le zero_lt_one (rem3ActS_ge_one ht0 ht1)).ne'
  have h1 : Continuous (fun v => (1 - chordX t v) ^ 2 * (chordX t v) ^ 4 *
      (v ^ 2 / chordD t v) ^ 2 / rem3ActS t v) :=
    ((((continuous_const.sub hx_cont).pow 2).mul (hx_cont.pow 4)).mul
      (((continuous_pow 2).div hD_cont hD_ne).pow 2)).div hS_cont hS_ne
  have h2 : Continuous (fun v => 8 * (1 - chordX t v) * (chordX t v) ^ 4 *
      ((1 - t ^ 2) / (chordD t v) ^ 2) * v ^ 2 / (rem3ActS t v) ^ 2) :=
    (((((continuous_const.mul (continuous_const.sub hx_cont)).mul (hx_cont.pow 4)).mul
      (continuous_const.div (hD_cont.pow 2) fun v => pow_ne_zero 2 (hD_ne v))).mul
      (continuous_pow 2))).div (hS_cont.pow 2) fun v => pow_ne_zero 2 (hS_ne v)
  exact (h1.add h2).continuousOn

private theorem chordIntegrand_three_ge_clean {t v : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hv0 : 0 < v) (hva : v < Real.sqrt (1 - t ^ 2)) :
    t * ((1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v) - rem3Clean t v) ≤
      chordIntegrand 3 t v := by
  have ht_m1 : -1 < t := by linarith
  have hge := chordIntegrand_ge 3 ht0 ht1 hv0 hva
  dsimp only at hge
  set x := chordX t v
  set D := chordD t v
  set zNorm := ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * 3 + 2) *
    (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖
  have hx_lt : x < 1 := chordX_lt_one ht0.le ht1 hv0.le hva
  have h1x_ne : 1 - x ≠ 0 := (sub_pos.mpr hx_lt).ne'
  have hS_ne : rem3ActS t v ≠ 0 := (lt_of_lt_of_le zero_lt_one (rem3ActS_ge_one ht_m1 ht1)).ne'
  have hz_eq : zNorm = x ^ 4 * (v ^ 2 / D) := norm_reflection_z_eq t 3 v
  have h1z_eq : 1 - zNorm = (1 - x) * rem3ActS t v := one_sub_zNorm_three_eq ht_m1 ht1
  have hD_ne : D ≠ 0 := (chordD_pos ht1 ht_m1 v).ne'
  have hrem_eq : (1 - x) ^ 3 * (v ^ 2 / D) * (zNorm / (1 - zNorm)) +
      (2 * ((3 : ℕ) : ℝ) + 2) * (1 - x) ^ 3 * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2) =
      rem3Clean t v := by
    unfold rem3Clean
    change (1 - x) ^ 3 * (v ^ 2 / D) * (zNorm / (1 - zNorm)) +
        (2 * ((3 : ℕ) : ℝ) + 2) * (1 - x) ^ 3 * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2) =
      (1 - x) ^ 2 * x ^ 4 * (v ^ 2 / D) ^ 2 / rem3ActS t v +
        8 * (1 - x) * x ^ 4 * ((1 - t ^ 2) / D ^ 2) * v ^ 2 / (rem3ActS t v) ^ 2
    rw [h1z_eq, hz_eq]
    norm_num
    field_simp [h1x_ne, hS_ne, hD_ne]
  have hsub : (1 - x) ^ 3 * (v ^ 2 / D) - (1 - x) ^ 3 * (v ^ 2 / D) * (zNorm / (1 - zNorm)) -
      (2 * ((3 : ℕ) : ℝ) + 2) * (1 - x) ^ 3 * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2) =
      (1 - x) ^ 3 * (v ^ 2 / D) - rem3Clean t v := by
    linarith only [hrem_eq]
  rw [hsub] at hge
  exact hge

private theorem rem3Clean_le_two_mul_rem3Upper {s0 s1 t v : ℝ}
    (hs0 : 0 ≤ s0) (hs0_t : s0 ≤ t ^ 2) (ht_s1 : t ^ 2 ≤ s1) (hs1_le : s1 ≤ 1 / 4)
    (hv0 : 0 ≤ v) (hva : v ≤ Real.sqrt (1 - t ^ 2)) :
    rem3Clean t v ≤ 2 * v * rem3Upper s0 s1 (chordX t v) := by
  let x := chordX t v
  let D := chordD t v
  let s := t ^ 2
  have hs0_le : s0 ≤ 1 / 4 := hs0_t.trans (ht_s1.trans hs1_le)
  have hs_nn : 0 ≤ s := sq_nonneg t
  have hs_le : s ≤ 1 / 4 := ht_s1.trans hs1_le
  have ht_lt1 : t < 1 := by nlinarith [show s ≤ 1 / 4 from hs_le]
  have ht_m1 : -1 < t := by nlinarith [show s ≤ 1 / 4 from hs_le]
  have hx_ge_s : s ≤ x := by dsimp [x, s, chordX]; nlinarith
  have hx_ge0 : 0 ≤ x := hs_nn.trans hx_ge_s
  have hx_le1 : x ≤ 1 := by
    have hv2 : v ^ 2 ≤ 1 - t ^ 2 := by
      have h := pow_le_pow_left₀ hv0 hva 2
      rwa [Real.sq_sqrt (by nlinarith)] at h
    dsimp [x, chordX]
    linarith
  have h1x_nn : 0 ≤ 1 - x := by linarith
  have hD_eq : D = 1 - (2 - x) * s := chordD_eq_one_sub_chordX t v
  let D0 := 1 - (2 - x) * s0
  let D1 := 1 - (2 - x) * s1
  let S_eff := 1 + x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - s0) / D0)
  have hD0_pos : 0 < D0 := by dsimp [D0]; nlinarith
  have hD1_pos : 0 < D1 := by dsimp [D1]; nlinarith
  have hD_pos : 0 < D := by rw [hD_eq]; nlinarith
  have hD1_le_D : D1 ≤ D := by
    rw [hD_eq]
    dsimp [D1]
    have : (2 - x) * s ≤ (2 - x) * s1 := mul_le_mul_of_nonneg_left ht_s1 (by linarith)
    linarith
  have hS_eff_ge1 : 1 ≤ S_eff := by
    dsimp [S_eff]
    have : 0 ≤ x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - s0) / D0) := by
      have h1s0 : 0 ≤ 1 - s0 := by linarith
      positivity
    linarith
  have hS_eff_le_S : S_eff ≤ rem3ActS t v := by
    unfold rem3ActS
    dsimp only [S_eff]
    rw [chordD_eq_one_sub_chordX t v]
    have hfrac := one_sub_div_chordD_ge hs0 hs0_t hs_le hx_ge0 hx_le1
    have hx4 : 0 ≤ x ^ 4 := pow_nonneg hx_ge0 4
    nlinarith
  have hv_eq : v = Real.sqrt (x - s) := by
    dsimp [x, s, chordX]
    rw [add_sub_cancel_left, Real.sqrt_sq hv0]
  have hv_le_sqrt : v ≤ Real.sqrt (x - s0) := by
    rw [hv_eq]
    exact Real.sqrt_le_sqrt (by linarith)
  have hv2_eq : v ^ 2 = x - s := by dsimp [x, s, chordX]; ring
  have hphi2_le : v ^ 2 / D ≤ (x - s0) / D0 := by
    rw [hv2_eq, hD_eq]
    exact sub_div_chordD_le hs0 hs0_t hs_le hx_ge_s hx_le1
  have hD2_le : (1 - t ^ 2) / D ^ 2 ≤ (1 - s1) / D1 ^ 2 := by
    rw [hD_eq]
    exact one_sub_div_chordD_sq_antitone hs_nn ht_s1 hs1_le hx_ge0 hx_le1
  have h1t2_nn : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hphi_nn : 0 ≤ (x - s0) / D0 := div_nonneg (by linarith) hD0_pos.le
  have hterm1 : (1 - x) ^ 2 * x ^ 4 * (v ^ 2 / D) ^ 2 / rem3ActS t v ≤
      2 * v * ((1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0) * Real.sqrt (x - s0) / (2 * D1 * S_eff)) := by
    have hS_pos : 0 < S_eff := by linarith
    have hSact_pos : 0 < rem3ActS t v := by linarith
    calc
      (1 - x) ^ 2 * x ^ 4 * (v ^ 2 / D) ^ 2 / rem3ActS t v
          = ((1 - x) ^ 2 * x ^ 4 * (v ^ 2 / D) * v / (D * rem3ActS t v)) * v := by ring
      _ ≤ ((1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0) * Real.sqrt (x - s0) / (D1 * S_eff)) * v := by
            have hnum : (1 - x) ^ 2 * x ^ 4 * (v ^ 2 / D) * v ≤
                (1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0) * Real.sqrt (x - s0) := by
              gcongr
            have hden : D1 * S_eff ≤ D * rem3ActS t v :=
              mul_le_mul hD1_le_D hS_eff_le_S (by linarith) (by linarith)
            have hdiv : (1 - x) ^ 2 * x ^ 4 * (v ^ 2 / D) * v / (D * rem3ActS t v) ≤
                (1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0) * Real.sqrt (x - s0) / (D1 * S_eff) :=
              div_le_div₀ (by positivity) hnum (mul_pos hD1_pos hS_pos) hden
            exact mul_le_mul_of_nonneg_right hdiv hv0
      _ = 2 * v * ((1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0) * Real.sqrt (x - s0) / (2 * D1 * S_eff)) := by
            ring
  have hterm2 : 8 * (1 - x) * x ^ 4 * ((1 - t ^ 2) / D ^ 2) * v ^ 2 / (rem3ActS t v) ^ 2 ≤
      2 * v * (4 * (1 - x) * x ^ 4 * (1 - s1) * Real.sqrt (x - s0) / (D1 ^ 2 * S_eff ^ 2)) := by
    have hS_pos : 0 < S_eff := by linarith
    have h1s1 : 0 ≤ 1 - s1 := by linarith
    have h1 : (1 - t ^ 2) / D ^ 2 / (rem3ActS t v) ^ 2 ≤ ((1 - s1) / D1 ^ 2) / S_eff ^ 2 := by
      have hnum : (1 - t ^ 2) / D ^ 2 ≤ (1 - s1) / D1 ^ 2 := hD2_le
      have hS2 : S_eff ^ 2 ≤ (rem3ActS t v) ^ 2 := by gcongr
      exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hS_pos) hS2
    have h2 : ((1 - s1) / D1 ^ 2) / S_eff ^ 2 = (1 - s1) / (D1 ^ 2 * S_eff ^ 2) := by ring
    rw [h2] at h1
    calc
      8 * (1 - x) * x ^ 4 * ((1 - t ^ 2) / D ^ 2) * v ^ 2 / (rem3ActS t v) ^ 2
          = (8 * (1 - x) * x ^ 4 * ((1 - t ^ 2) / D ^ 2 / (rem3ActS t v) ^ 2) * v) * v := by ring
      _ ≤ (8 * (1 - x) * x ^ 4 * ((1 - s1) / (D1 ^ 2 * S_eff ^ 2)) * Real.sqrt (x - s0)) * v := by
            have hleft : 8 * (1 - x) * x ^ 4 * ((1 - t ^ 2) / D ^ 2 / (rem3ActS t v) ^ 2) * v ≤
                8 * (1 - x) * x ^ 4 * ((1 - s1) / (D1 ^ 2 * S_eff ^ 2)) * Real.sqrt (x - s0) := by
              gcongr
            exact mul_le_mul_of_nonneg_right hleft hv0
      _ = 2 * v * (4 * (1 - x) * x ^ 4 * (1 - s1) * Real.sqrt (x - s0) / (D1 ^ 2 * S_eff ^ 2)) := by
            ring
  unfold rem3Clean rem3Upper
  dsimp only [x, D, D0, D1, S_eff] at hterm1 hterm2 ⊢
  linarith

private theorem rem3Upper_nonneg {s0 s1 x : ℝ} (hs0 : 0 ≤ s0) (hs0_le : s0 ≤ 1 / 4)
    (hs1_le : s1 ≤ 1 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ rem3Upper s0 s1 x := by
  unfold rem3Upper
  have h1x : 0 ≤ 1 - x := by linarith
  have h1s1 : 0 ≤ 1 - s1 := by linarith
  have hD0 : 0 < 1 - (2 - x) * s0 := by nlinarith
  have hD1 : 0 < 1 - (2 - x) * s1 := by nlinarith
  have hS : 0 < 1 + x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - s0) / (1 - (2 - x) * s0)) := by
    have h1s0 : 0 ≤ 1 - s0 := by linarith
    positivity
  by_cases hxs : s0 ≤ x
  · have hxs0 : 0 ≤ x - s0 := by linarith
    positivity
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
    simp

private theorem rem3Clean_integral_le_rem3Upper {s0 s1 t : ℝ}
    (hs0 : 0 ≤ s0) (hs0_t : s0 ≤ t ^ 2) (ht_s1 : t ^ 2 ≤ s1) (hs1_le : s1 ≤ 1 / 4) :
    (∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), rem3Clean t v) ≤
      ∫ x in s0..1, rem3Upper s0 s1 x := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have hs0_le : s0 ≤ 1 / 4 := hs0_t.trans (ht_s1.trans hs1_le)
  have hs1_nn : 0 ≤ s1 := hs0.trans (hs0_t.trans ht_s1)
  have ht_lt1 : t < 1 := by nlinarith [show t ^ 2 ≤ 1 / 4 by linarith]
  have ht_m1 : -1 < t := by nlinarith [show t ^ 2 ≤ 1 / 4 by linarith]
  have ha2 : a ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  have hrem_cont := rem3Clean_continuousOn ht_m1 ht_lt1
  have hu_cont := continuousOn_rem3Upper hs0 hs0_le hs1_nn hs1_le
  have hcomp_cont : ContinuousOn (fun v => 2 * v * rem3Upper s0 s1 (chordX t v)) (Icc 0 a) := by
    have hx_sub : MapsTo (chordX t) (Icc 0 a) (Icc 0 1) := by
      intro v hv
      have hv2 : v ^ 2 ≤ 1 - t ^ 2 := by
        have h := pow_le_pow_left₀ hv.1 hv.2 2
        rwa [ha2] at h
      unfold chordX
      exact ⟨by positivity, by linarith⟩
    exact (continuous_const.mul continuous_id).continuousOn.mul (hu_cont.comp (by
      unfold chordX; exact (continuous_const.add (continuous_pow 2)).continuousOn) hx_sub)
  have hle_pt : ∀ v ∈ Icc (0 : ℝ) a, rem3Clean t v ≤ 2 * v * rem3Upper s0 s1 (chordX t v) :=
    fun v hv => rem3Clean_le_two_mul_rem3Upper hs0 hs0_t ht_s1 hs1_le hv.1 hv.2
  have hmono : (∫ v in (0 : ℝ)..a, rem3Clean t v) ≤
      ∫ v in (0 : ℝ)..a, 2 * v * rem3Upper s0 s1 (chordX t v) :=
    intervalIntegral.integral_mono_on ha_pos.le
      (hrem_cont.intervalIntegrable_of_Icc ha_pos.le)
      (hcomp_cont.intervalIntegrable_of_Icc ha_pos.le) hle_pt
  have hsub : (∫ v in (0 : ℝ)..a, 2 * v * rem3Upper s0 s1 (chordX t v)) =
      ∫ x in (t ^ 2)..1, rem3Upper s0 s1 x := by
    have hx_cont : Continuous (chordX t) := by
      unfold chordX; exact continuous_const.add (continuous_pow 2)
    have hcomp := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := chordX t) (f' := fun v => 2 * v) (g := rem3Upper s0 s1) (a := 0) (b := a)
      hx_cont.continuousOn
      (fun v _ => by
        unfold chordX
        simpa using ((hasDerivAt_pow 2 v).const_add (t ^ 2)).congr_deriv (by simp))
      (fun v hv => by rw [min_eq_left ha_pos.le] at hv; linarith [hv.1])
    have heq : (∫ v in (0 : ℝ)..a, (rem3Upper s0 s1 ∘ chordX t) v * (2 * v)) =
        ∫ v in (0 : ℝ)..a, 2 * v * rem3Upper s0 s1 (chordX t v) := by
      refine intervalIntegral.integral_congr fun v _ => ?_
      dsimp only [Function.comp_def]
      ring
    have hg0 : chordX t 0 = t ^ 2 := by unfold chordX; ring
    have hga : chordX t a = 1 := by unfold chordX; rw [ha2]; ring
    rw [hg0, hga] at hcomp
    rw [← heq, hcomp]
  have hs0_t2_int : IntervalIntegrable (rem3Upper s0 s1) volume s0 (t ^ 2) :=
    (hu_cont.mono (Icc_subset_Icc hs0 (by nlinarith))).intervalIntegrable_of_Icc hs0_t
  have ht2_1_int : IntervalIntegrable (rem3Upper s0 s1) volume (t ^ 2) 1 :=
    (hu_cont.mono (Icc_subset_Icc (sq_nonneg t) le_rfl)).intervalIntegrable_of_Icc (by nlinarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs0_t2_int ht2_1_int
  have hnn : 0 ≤ ∫ x in s0..(t ^ 2), rem3Upper s0 s1 x := by
    apply intervalIntegral.integral_nonneg hs0_t
    intro x hx
    exact rem3Upper_nonneg hs0 hs0_le hs1_le (hs0.trans hx.1) (hx.2.trans (by nlinarith))
  linarith

private theorem rem3Upper_box_le (p0 q0 p1 q1 d k : ℕ)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hle : p0 * q1 < p1 * q0) (hp1 : 2 * p1 ≤ q1)
    (hk : k < 2 ^ d) :
    let Nx : ℕ := 2 ^ d
    let s0 : ℝ := ((p0 * p0 : ℕ) : ℝ) / ((q0 * q0 : ℕ) : ℝ)
    let s1 : ℝ := ((p1 * p1 : ℕ) : ℝ) / ((q1 * q1 : ℕ) : ℝ)
    let dx : ℝ := (1 - s0) / (Nx : ℝ)
    let xL : ℝ := s0 + (k : ℝ) * dx
    let xR : ℝ := s0 + ((k + 1 : ℕ) : ℝ) * dx
    ∀ x ∈ Icc xL xR,
      rem3Upper s0 s1 x ≤ (n3BoxDensityUB p0 q0 p1 q1 Nx k : ℝ) / (1000000000 : ℝ) := by
  intro Nx s0 s1 dx xL xR x hx
  let K6 : ℕ := 1000000
  let K9 : ℕ := 1000000000
  let s0_n : ℕ := p0 * p0
  let s0_d : ℕ := q0 * q0
  let s1_n : ℕ := p1 * p1
  let s1_d : ℕ := q1 * q1
  let Dx : ℕ := s0_d * Nx
  let dx_n : ℕ := s0_d - s0_n
  let xL_n : ℕ := s0_n * Nx + k * dx_n
  let xR_n : ℕ := xL_n + dx_n
  let diff_n : ℕ := (k + 1) * dx_n
  let q_hi_n : ℕ := n3QHi diff_n Dx
  let D0_lo_n : ℕ := s0_d * Dx - (2 * Dx - xL_n) * s0_n
  let D0_hi_n : ℕ := s0_d * Dx - (2 * Dx - xR_n) * s0_n
  let D1_lo_n : ℕ := s1_d * Dx - (2 * Dx - xL_n) * s1_n
  let phi2_hi_6 : ℕ := natCeil K6 (diff_n * s0_d) D0_lo_n
  let xL_6 : ℕ := natFloor K6 xL_n Dx
  let xL2_6 : ℕ := (xL_6 * xL_6) / K6
  let xL3_6 : ℕ := (xL2_6 * xL_6) / K6
  let xL4_6 : ℕ := (xL2_6 * xL2_6) / K6
  let fac_6 : ℕ := natFloor K6 (dx_n * Dx) D0_hi_n
  let S_eff_lo_6 : ℕ := K6 + xL_6 + xL2_6 + xL3_6 + (xL4_6 * fac_6) / K6
  let xR_6 : ℕ := natCeil K6 xR_n Dx
  let xR2_6 : ℕ := natCeil K6 (xR_6 * xR_6) (K6 * K6)
  let xR4_6 : ℕ := natCeil K6 (xR2_6 * xR2_6) (K6 * K6)
  let omxL_6 : ℕ := natCeil K6 (Dx - xL_n) Dx
  let D1_lo_6 : ℕ := natFloor K6 D1_lo_n (s1_d * Dx)
  let t1_9 : ℕ := natCeil K9 (omxL_6 * omxL_6 * xR4_6 * phi2_hi_6 * q_hi_n)
    (2 * D1_lo_6 * S_eff_lo_6 * K6 * K6 * 1000)
  let t2_9 : ℕ := natCeil K9 (4 * omxL_6 * xR4_6 * (s1_d - s1_n) * q_hi_n * K6 * K6)
    (D1_lo_6 * D1_lo_6 * S_eff_lo_6 * S_eff_lo_6 * s1_d * 1000)
  change rem3Upper s0 s1 x ≤ ((t1_9 + t2_9 : ℕ) : ℝ) / (K9 : ℝ)
  have hNx_pos : 0 < Nx := Nat.two_pow_pos d
  have hs0d_pos : 0 < s0_d := Nat.mul_pos hq0 hq0
  have hs1d_pos : 0 < s1_d := Nat.mul_pos hq1 hq1
  have hDx_pos : 0 < Dx := Nat.mul_pos hs0d_pos hNx_pos
  have hp0_lt : 2 * p0 < q0 := by nlinarith only [hle, hp1, hq0, hq1]
  have hs0_lt_quarter : 4 * s0_n < s0_d := by dsimp [s0_n, s0_d]; nlinarith only [hp0_lt]
  have hs1_le_quarter : 4 * s1_n ≤ s1_d := by dsimp [s1_n, s1_d]; nlinarith only [hp1]
  have hs0_lt : s0_n < s0_d := by nlinarith only [hs0_lt_quarter, hs0d_pos]
  have hs1_lt : s1_n < s1_d := by nlinarith only [hs1_le_quarter, hs1d_pos]
  have hdx_pos : 0 < dx_n := by dsimp [dx_n]; omega
  have hxR_le_Dx : xR_n ≤ Dx := by
    dsimp [xR_n, xL_n, Dx, dx_n]
    have hk1 : k + 1 ≤ Nx := hk
    calc
      s0_n * Nx + k * (s0_d - s0_n) + (s0_d - s0_n)
          = s0_n * Nx + (k + 1) * (s0_d - s0_n) := by ring
      _ ≤ s0_n * Nx + Nx * (s0_d - s0_n) := by gcongr
      _ = s0_d * Nx := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_comm Nx s0_d, Nat.mul_comm Nx s0_n]
            have : s0_n * Nx ≤ s0_d * Nx := Nat.mul_le_mul_right Nx hs0_lt.le
            omega
  have hxL_le_xR : xL_n ≤ xR_n := by dsimp [xR_n]; omega
  have hxL_le_Dx : xL_n ≤ Dx := hxL_le_xR.trans hxR_le_Dx
  have hdiff_le_Dx : diff_n ≤ Dx := by
    dsimp [diff_n, Dx, dx_n]
    have hk1 : k + 1 ≤ Nx := hk
    calc
      (k + 1) * (s0_d - s0_n) ≤ Nx * (s0_d - s0_n) := by gcongr
      _ ≤ Nx * s0_d := Nat.mul_le_mul_left Nx (Nat.sub_le _ _)
      _ = s0_d * Nx := Nat.mul_comm _ _
  have hdiff_pos : 0 < diff_n := Nat.mul_pos (Nat.succ_pos k) hdx_pos
  have h2Dx_xL : xL_n ≤ 2 * Dx := by omega
  have h2Dx_xR : xR_n ≤ 2 * Dx := by omega
  have hD0_lo_bound : (2 * Dx - xL_n) * s0_n * 2 ≤ s0_d * Dx := by
    have h1 : 2 * Dx - xL_n ≤ 2 * Dx := Nat.sub_le _ _
    calc
      (2 * Dx - xL_n) * s0_n * 2 ≤ (2 * Dx) * s0_n * 2 := by gcongr
      _ = (4 * s0_n) * Dx := by ring
      _ ≤ s0_d * Dx := Nat.mul_le_mul_right Dx hs0_lt_quarter.le
  have hD0_hi_bound : (2 * Dx - xR_n) * s0_n * 2 ≤ s0_d * Dx := by
    have h1 : 2 * Dx - xR_n ≤ 2 * Dx := Nat.sub_le _ _
    calc
      (2 * Dx - xR_n) * s0_n * 2 ≤ (2 * Dx) * s0_n * 2 := by gcongr
      _ = (4 * s0_n) * Dx := by ring
      _ ≤ s0_d * Dx := Nat.mul_le_mul_right Dx hs0_lt_quarter.le
  have hD1_lo_bound : (2 * Dx - xL_n) * s1_n * 2 ≤ s1_d * Dx := by
    have h1 : 2 * Dx - xL_n ≤ 2 * Dx := Nat.sub_le _ _
    calc
      (2 * Dx - xL_n) * s1_n * 2 ≤ (2 * Dx) * s1_n * 2 := by gcongr
      _ = (4 * s1_n) * Dx := by ring
      _ ≤ s1_d * Dx := Nat.mul_le_mul_right Dx hs1_le_quarter
  have hs0dDx_pos : 0 < s0_d * Dx := Nat.mul_pos hs0d_pos hDx_pos
  have hs1dDx_pos : 0 < s1_d * Dx := Nat.mul_pos hs1d_pos hDx_pos
  have hD0_lo_pos : 0 < D0_lo_n := by
    dsimp [D0_lo_n]
    exact Nat.sub_pos_of_lt (by
      have h1 : (2 * Dx - xL_n) * s0_n * 2 ≤ s0_d * Dx := hD0_lo_bound
      have h2 : 0 < s0_d * Dx := hs0dDx_pos
      nlinarith only [h1, h2])
  have hD0_hi_pos : 0 < D0_hi_n := by
    dsimp [D0_hi_n]
    exact Nat.sub_pos_of_lt (by
      have h1 : (2 * Dx - xR_n) * s0_n * 2 ≤ s0_d * Dx := hD0_hi_bound
      have h2 : 0 < s0_d * Dx := hs0dDx_pos
      nlinarith only [h1, h2])
  have hD1_lo_pos : 0 < D1_lo_n := by
    dsimp [D1_lo_n]
    exact Nat.sub_pos_of_lt (by
      have h1 : (2 * Dx - xL_n) * s1_n * 2 ≤ s1_d * Dx := hD1_lo_bound
      have h2 : 0 < s1_d * Dx := hs1dDx_pos
      nlinarith only [h1, h2])
  have hD1_lo_6_pos : 0 < D1_lo_6 := by
    dsimp [D1_lo_6, natFloor]
    rw [Nat.div_pos_iff]
    refine ⟨hs1dDx_pos, ?_⟩
    have h1 : s1_d * Dx ≤ D1_lo_n * 2 := by
      dsimp [D1_lo_n]
      set A := (2 * Dx - xL_n) * s1_n
      have hA : A * 2 ≤ s1_d * Dx := hD1_lo_bound
      omega
    exact h1.trans (Nat.mul_le_mul_left D1_lo_n (by decide : 2 ≤ K6))
  have hK6_pos : 0 < K6 := by decide
  have hK9_pos : 0 < K9 := by decide
  have hS_eff_lo_6_pos : 0 < S_eff_lo_6 := by
    dsimp [S_eff_lo_6]
    exact Nat.lt_of_lt_of_le hK6_pos (Nat.le_trans (Nat.le_add_right _ _)
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
  have hxL_eq : xL = (xL_n : ℝ) / (Dx : ℝ) := by
    dsimp [xL, s0, dx, xL_n, Dx, dx_n]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hs0_lt.le]
    dsimp [s0_d, s0_n]
    push_cast
    have h0d : ((q0 * q0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
    have hNx : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
    field_simp [h0d, hNx]
  have hxR_eq : xR = (xR_n : ℝ) / (Dx : ℝ) := by
    dsimp [xR, s0, dx, xR_n, xL_n, Dx, dx_n]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hs0_lt.le]
    dsimp [s0_d, s0_n]
    push_cast
    have h0d : ((q0 * q0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
    have hNx : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
    field_simp [h0d, hNx]
    ring
  have hxR_sub_s0 : xR - s0 = (diff_n : ℝ) / (Dx : ℝ) := by
    dsimp [xR, s0, dx, diff_n, Dx, dx_n]
    simp only [Nat.cast_mul, Nat.cast_sub hs0_lt.le]
    dsimp [s0_d, s0_n]
    push_cast
    have h0d : ((q0 * q0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
    have hNx : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
    field_simp [h0d, hNx]
    ring
  have hx_ge_xL : (xL_n : ℝ) / (Dx : ℝ) ≤ x := hxL_eq ▸ hx.1
  have hx_le_xR : x ≤ (xR_n : ℝ) / (Dx : ℝ) := hxR_eq ▸ hx.2
  have hx_ge0 : 0 ≤ x := le_trans (by positivity) hx_ge_xL
  have hx_le1 : x ≤ 1 := by
    refine hx_le_xR.trans ?_
    rw [div_le_one (by exact_mod_cast hDx_pos)]
    exact_mod_cast hxR_le_Dx
  have hx_ge_s0 : s0 ≤ x := by
    have hs0_le_one : s0 ≤ 1 := by
      dsimp [s0]
      rw [div_le_one (by exact_mod_cast hs0d_pos)]
      exact_mod_cast hs0_lt.le
    have hdx_nn : 0 ≤ dx := div_nonneg (sub_nonneg.mpr hs0_le_one) (by exact_mod_cast hNx_pos.le)
    have hkdx : 0 ≤ (k : ℝ) * dx := mul_nonneg (Nat.cast_nonneg k) hdx_nn
    have hxL_ge : s0 ≤ xL := by dsimp [xL]; linarith only [hkdx]
    exact hxL_ge.trans hx.1
  have hs0_nn : 0 ≤ s0 := by dsimp [s0]; positivity
  have hs0_le : s0 ≤ 1 / 4 := by
    dsimp [s0]
    rw [div_le_div_iff₀ (by exact_mod_cast hs0d_pos) (by norm_num)]
    have : ((4 * s0_n : ℕ) : ℝ) ≤ ((s0_d : ℕ) : ℝ) := by exact_mod_cast hs0_lt_quarter.le
    push_cast at this; linarith only [this]
  have hs1_nn : 0 ≤ s1 := by dsimp [s1]; positivity
  have hs1_le : s1 ≤ 1 / 4 := by
    dsimp [s1]
    rw [div_le_div_iff₀ (by exact_mod_cast hs1d_pos) (by norm_num)]
    have : ((4 * s1_n : ℕ) : ℝ) ≤ ((s1_d : ℕ) : ℝ) := by exact_mod_cast hs1_le_quarter
    push_cast at this; linarith only [this]
  have hsqrt_le : Real.sqrt (x - s0) ≤ (q_hi_n : ℝ) / (1000 : ℝ) := by
    have h1 : Real.sqrt (x - s0) ≤ Real.sqrt (xR - s0) := Real.sqrt_le_sqrt (by linarith only [hx.2])
    have h2 : Real.sqrt (xR - s0) ≤ nfVal (nfSqrtUB (diff_n, Dx)) := by
      rw [hxR_sub_s0]
      exact @real_sqrt_nfVal_le_nfSqrtUB (diff_n, Dx) hDx_pos hdiff_le_Dx
    have h3 : nfVal (nfSqrtUB (diff_n, Dx)) = (q_hi_n : ℝ) / (1000 : ℝ) := by
      unfold nfSqrtUB nfVal
      have hne : diff_n ≠ 0 := hdiff_pos.ne'
      simp only [hne, ↓reduceIte]
      rfl
    linarith only [h1, h2, h3]
  let D0x : ℝ := 1 - (2 - x) * s0
  let D1x : ℝ := 1 - (2 - x) * s1
  have hD0_eq_L : 1 - (2 - xL) * s0 = (D0_lo_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ) := by
    rw [hxL_eq]
    have h1 : (2 * Dx - xL_n) * s0_n ≤ s0_d * Dx := by nlinarith only [hD0_lo_bound]
    dsimp [D0_lo_n, s0]
    simp only [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub h2Dx_xL]
    dsimp [Dx, s0_d, s0_n]
    push_cast
    have h0d : ((q0 * q0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
    have hNx : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
    field_simp [h0d, hNx]
  have hD0_eq_R : 1 - (2 - xR) * s0 = (D0_hi_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ) := by
    rw [hxR_eq]
    have h1 : (2 * Dx - xR_n) * s0_n ≤ s0_d * Dx := by nlinarith only [hD0_hi_bound]
    dsimp [D0_hi_n, s0]
    simp only [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub h2Dx_xR]
    dsimp [Dx, s0_d, s0_n]
    push_cast
    have h0d : ((q0 * q0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
    have hNx : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
    field_simp [h0d, hNx]
  have hD1_eq_L : 1 - (2 - xL) * s1 = (D1_lo_n : ℝ) / ((s1_d * Dx : ℕ) : ℝ) := by
    rw [hxL_eq]
    have h1 : (2 * Dx - xL_n) * s1_n ≤ s1_d * Dx := by nlinarith only [hD1_lo_bound]
    dsimp [D1_lo_n, s1]
    simp only [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub h2Dx_xL]
    dsimp [Dx, s1_d, s1_n]
    push_cast
    have h0d : (s0_d : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
    have h1d : ((q1 * q1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs1d_pos.ne'
    have hNx : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
    field_simp [h0d, h1d, hNx]
  have hD0_ge : (D0_lo_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ) ≤ D0x := by
    have hxs0 : xL * s0 ≤ x * s0 := mul_le_mul_of_nonneg_right hx.1 hs0_nn
    dsimp [D0x]; rw [← hD0_eq_L]; linarith only [hxs0]
  have hD0_le : D0x ≤ (D0_hi_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ) := by
    have hxs0 : x * s0 ≤ xR * s0 := mul_le_mul_of_nonneg_right hx.2 hs0_nn
    dsimp [D0x]; rw [← hD0_eq_R]; linarith only [hxs0]
  have hD1_ge_L : (D1_lo_n : ℝ) / ((s1_d * Dx : ℕ) : ℝ) ≤ D1x := by
    have hxs1 : xL * s1 ≤ x * s1 := mul_le_mul_of_nonneg_right hx.1 hs1_nn
    dsimp [D1x]; rw [← hD1_eq_L]; linarith only [hxs1]
  have hD1_ge_6 : (D1_lo_6 : ℝ) / (K6 : ℝ) ≤ D1x := by
    have hf := natFloor_le_natDiv K6 D1_lo_n (s1_d * Dx) hK6_pos (Nat.mul_pos hs1d_pos hDx_pos)
    exact hf.trans hD1_ge_L
  have hD0_pos : 0 < D0x := lt_of_lt_of_le (by positivity) hD0_ge
  have hD1_pos : 0 < D1x := lt_of_lt_of_le (by positivity) hD1_ge_6
  have hphi2_le : (x - s0) / D0x ≤ (phi2_hi_6 : ℝ) / (K6 : ℝ) := by
    have h1 : (x - s0) / D0x ≤ (xR - s0) / ((D0_lo_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ)) :=
      div_le_div₀ (by linarith) (by linarith [hx.2]) (by positivity) hD0_ge
    have h2 : (xR - s0) / ((D0_lo_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ)) =
        ((diff_n * s0_d : ℕ) : ℝ) / (D0_lo_n : ℝ) := by
      rw [hxR_sub_s0]
      push_cast
      have h0d : (s0_d : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
      have hDx' : (Dx : ℝ) ≠ 0 := by exact_mod_cast hDx_pos.ne'
      have hD0l : (D0_lo_n : ℝ) ≠ 0 := by exact_mod_cast hD0_lo_pos.ne'
      field_simp [h0d, hDx', hD0l]
    exact h1.trans (h2 ▸ natDiv_le_natCeil K6 (diff_n * s0_d) D0_lo_n hK6_pos hD0_lo_pos)
  have homx_le : 1 - x ≤ (omxL_6 : ℝ) / (K6 : ℝ) := by
    have h1 : 1 - x ≤ 1 - xL := by linarith [hx.1]
    have h2 : 1 - xL = ((Dx - xL_n : ℕ) : ℝ) / (Dx : ℝ) := by
      rw [hxL_eq, Nat.cast_sub hxL_le_Dx]
      have hDx' : (Dx : ℝ) ≠ 0 := by exact_mod_cast hDx_pos.ne'
      field_simp [hDx']
    exact h1.trans (h2 ▸ natDiv_le_natCeil K6 (Dx - xL_n) Dx hK6_pos hDx_pos)
  have hx4_le : x ^ 4 ≤ (xR4_6 : ℝ) / (K6 : ℝ) := by
    have hx_R6 : x ≤ (xR_6 : ℝ) / (K6 : ℝ) :=
      hx_le_xR.trans (natDiv_le_natCeil K6 xR_n Dx hK6_pos hDx_pos)
    have hx2_R6 : x ^ 2 ≤ (xR2_6 : ℝ) / (K6 : ℝ) := by
      have hsq : x ^ 2 ≤ ((xR_6 * xR_6 : ℕ) : ℝ) / ((K6 * K6 : ℕ) : ℝ) := by
        push_cast
        have : x ^ 2 ≤ ((xR_6 : ℝ) / (K6 : ℝ)) ^ 2 := pow_le_pow_left₀ hx_ge0 hx_R6 2
        linarith only [this, show ((xR_6 : ℝ) / (K6 : ℝ)) ^ 2 = (xR_6 : ℝ) * (xR_6 : ℝ) / ((K6 : ℝ) * (K6 : ℝ)) by ring]
      exact hsq.trans (natDiv_le_natCeil K6 (xR_6 * xR_6) (K6 * K6) hK6_pos (Nat.mul_pos hK6_pos hK6_pos))
    have hx4_R6 : x ^ 4 ≤ ((xR2_6 * xR2_6 : ℕ) : ℝ) / ((K6 * K6 : ℕ) : ℝ) := by
      push_cast
      have : x ^ 4 ≤ ((xR2_6 : ℝ) / (K6 : ℝ)) ^ 2 := by
        calc
          x ^ 4 = (x ^ 2) ^ 2 := by ring
          _ ≤ ((xR2_6 : ℝ) / (K6 : ℝ)) ^ 2 := pow_le_pow_left₀ (sq_nonneg x) hx2_R6 2
      linarith [show ((xR2_6 : ℝ) / (K6 : ℝ)) ^ 2 = (xR2_6 : ℝ) * (xR2_6 : ℝ) / ((K6 : ℝ) * (K6 : ℝ)) by ring]
    exact hx4_R6.trans (natDiv_le_natCeil K6 (xR2_6 * xR2_6) (K6 * K6) hK6_pos (Nat.mul_pos hK6_pos hK6_pos))
  have hS_eff_ge : (S_eff_lo_6 : ℝ) / (K6 : ℝ) ≤
      1 + x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - s0) / D0x) := by
    have hxL6_le : (xL_6 : ℝ) / (K6 : ℝ) ≤ x :=
      (natFloor_le_natDiv K6 xL_n Dx hK6_pos hDx_pos).trans hx_ge_xL
    have nat_div_K6_le : ∀ a b : ℕ, ((a * b / K6 : ℕ) : ℝ) / (K6 : ℝ) ≤
        ((a : ℝ) / (K6 : ℝ)) * ((b : ℝ) / (K6 : ℝ)) := fun a b => by
      have hdiv : ((a * b / K6 : ℕ) : ℝ) ≤ (a * b : ℕ) / (K6 : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hK6_pos)]
        exact_mod_cast Nat.div_mul_le_self (a * b) K6
      calc
        ((a * b / K6 : ℕ) : ℝ) / (K6 : ℝ)
            ≤ ((a * b : ℕ) / (K6 : ℝ)) / (K6 : ℝ) :=
              div_le_div_of_nonneg_right hdiv (by exact_mod_cast hK6_pos.le)
        _ = ((a : ℝ) / (K6 : ℝ)) * ((b : ℝ) / (K6 : ℝ)) := by push_cast; ring
    have hxL6_nn : 0 ≤ (xL_6 : ℝ) / (K6 : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hK6_pos.le)
    have hxL2_nn : 0 ≤ (xL2_6 : ℝ) / (K6 : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hK6_pos.le)
    have hxL2_le : (xL2_6 : ℝ) / (K6 : ℝ) ≤ x ^ 2 := by
      have h := nat_div_K6_le xL_6 xL_6
      calc
        (xL2_6 : ℝ) / (K6 : ℝ) ≤ ((xL_6 : ℝ) / (K6 : ℝ)) * ((xL_6 : ℝ) / (K6 : ℝ)) := h
        _ ≤ x * x := mul_le_mul hxL6_le hxL6_le hxL6_nn hx_ge0
        _ = x ^ 2 := by ring
    have hxL3_le : (xL3_6 : ℝ) / (K6 : ℝ) ≤ x ^ 3 := by
      have h := nat_div_K6_le xL2_6 xL_6
      calc
        (xL3_6 : ℝ) / (K6 : ℝ) ≤ ((xL2_6 : ℝ) / (K6 : ℝ)) * ((xL_6 : ℝ) / (K6 : ℝ)) := h
        _ ≤ x ^ 2 * x := mul_le_mul hxL2_le hxL6_le hxL6_nn (sq_nonneg x)
        _ = x ^ 3 := by ring
    have hxL4_le : (xL4_6 : ℝ) / (K6 : ℝ) ≤ x ^ 4 := by
      have h := nat_div_K6_le xL2_6 xL2_6
      calc
        (xL4_6 : ℝ) / (K6 : ℝ) ≤ ((xL2_6 : ℝ) / (K6 : ℝ)) * ((xL2_6 : ℝ) / (K6 : ℝ)) := h
        _ ≤ x ^ 2 * x ^ 2 := mul_le_mul hxL2_le hxL2_le hxL2_nn (sq_nonneg x)
        _ = x ^ 4 := by ring
    have hfac_le : (fac_6 : ℝ) / (K6 : ℝ) ≤ (1 - s0) / D0x := by
      have hf := natFloor_le_natDiv K6 (dx_n * Dx) D0_hi_n hK6_pos hD0_hi_pos
      have heq : ((dx_n * Dx : ℕ) : ℝ) / (D0_hi_n : ℝ) =
          (1 - s0) / ((D0_hi_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ)) := by
        dsimp [dx_n, s0]
        simp only [Nat.cast_mul, Nat.cast_sub hs0_lt.le]
        dsimp [s0_d, s0_n]
        push_cast
        have h0d : ((q0 * q0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
        have hDx' : (Dx : ℝ) ≠ 0 := by exact_mod_cast hDx_pos.ne'
        have hD0h : (D0_hi_n : ℝ) ≠ 0 := by exact_mod_cast hD0_hi_pos.ne'
        field_simp [h0d, hDx', hD0h]
      have hdiv : (1 - s0) / ((D0_hi_n : ℝ) / ((s0_d * Dx : ℕ) : ℝ)) ≤ (1 - s0) / D0x :=
        div_le_div_of_nonneg_left (by linarith only [hs0_le]) hD0_pos hD0_le
      exact hf.trans (heq ▸ hdiv)
    have hlast_le : ((xL4_6 * fac_6 / K6 : ℕ) : ℝ) / (K6 : ℝ) ≤ x ^ 4 * ((1 - s0) / D0x) := by
      have h := nat_div_K6_le xL4_6 fac_6
      have hfac_nn : 0 ≤ (fac_6 : ℝ) / (K6 : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hK6_pos.le)
      have hx4_nn : 0 ≤ x ^ 4 := pow_nonneg hx_ge0 4
      calc
        ((xL4_6 * fac_6 / K6 : ℕ) : ℝ) / (K6 : ℝ)
            ≤ ((xL4_6 : ℝ) / (K6 : ℝ)) * ((fac_6 : ℝ) / (K6 : ℝ)) := h
        _ ≤ x ^ 4 * ((1 - s0) / D0x) := mul_le_mul hxL4_le hfac_le hfac_nn hx4_nn
    dsimp [S_eff_lo_6]
    push_cast
    have hK6_ne : (K6 : ℝ) ≠ 0 := by exact_mod_cast hK6_pos.ne'
    have hsum_split : ((K6 : ℝ) + xL_6 + xL2_6 + xL3_6 + ↑(xL4_6 * fac_6 / K6)) / (K6 : ℝ) =
        1 + (xL_6 : ℝ) / K6 + (xL2_6 : ℝ) / K6 + (xL3_6 : ℝ) / K6 +
          ((xL4_6 * fac_6 / K6 : ℕ) : ℝ) / K6 := by
      field_simp [hK6_ne]
    rw [hsum_split]
    linarith only [hxL6_le, hxL2_le, hxL3_le, hlast_le]
  set S_eff := 1 + x + x ^ 2 + x ^ 3 + x ^ 4 * ((1 - s0) / D0x)
  have hS_eff_pos : 0 < S_eff :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast hS_eff_lo_6_pos) (by exact_mod_cast hK6_pos)) hS_eff_ge
  have hD1_pos' : (0 : ℝ) < (D1_lo_6 : ℝ) / K6 :=
    div_pos (by exact_mod_cast hD1_lo_6_pos) (by exact_mod_cast hK6_pos)
  have hS_pos' : (0 : ℝ) < (S_eff_lo_6 : ℝ) / K6 :=
    div_pos (by exact_mod_cast hS_eff_lo_6_pos) (by exact_mod_cast hK6_pos)
  have homx_nn_ub : 0 ≤ (omxL_6 : ℝ) / K6 := div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hK6_pos.le)
  have hxR4_nn_ub : 0 ≤ (xR4_6 : ℝ) / K6 := div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hK6_pos.le)
  have hphi2_nn_ub : 0 ≤ (phi2_hi_6 : ℝ) / K6 := div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hK6_pos.le)
  have hqhi_nn_ub : 0 ≤ (q_hi_n : ℝ) / 1000 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have h1_term : (1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0x) * Real.sqrt (x - s0) / (2 * D1x * S_eff) ≤
      (t1_9 : ℝ) / (K9 : ℝ) := by
    have hnum_le : (1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0x) * Real.sqrt (x - s0) ≤
        ((omxL_6 : ℝ) / K6) ^ 2 * ((xR4_6 : ℝ) / K6) * ((phi2_hi_6 : ℝ) / K6) * ((q_hi_n : ℝ) / 1000) := by
      have h1x_nn : 0 ≤ 1 - x := by linarith only [hx_le1]
      have hphi_nn : 0 ≤ (x - s0) / D0x := div_nonneg (by linarith only [hx_ge_s0]) hD0_pos.le
      have h1sq : (1 - x) ^ 2 ≤ ((omxL_6 : ℝ) / K6) ^ 2 := pow_le_pow_left₀ h1x_nn homx_le 2
      have h12 := mul_le_mul h1sq hx4_le (pow_nonneg hx_ge0 4) (sq_nonneg _)
      have h123 := mul_le_mul h12 hphi2_le hphi_nn (mul_nonneg (sq_nonneg _) hxR4_nn_ub)
      exact mul_le_mul h123 hsqrt_le (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (sq_nonneg _) hxR4_nn_ub) hphi2_nn_ub)
    have hden_ge : 2 * ((D1_lo_6 : ℝ) / K6) * ((S_eff_lo_6 : ℝ) / K6) ≤ 2 * D1x * S_eff := by
      have h2d : 2 * ((D1_lo_6 : ℝ) / K6) ≤ 2 * D1x := mul_le_mul_of_nonneg_left hD1_ge_6 (by norm_num)
      exact mul_le_mul h2d hS_eff_ge hS_pos'.le (mul_nonneg (by norm_num) hD1_pos.le)
    have hdiv_le : (1 - x) ^ 2 * x ^ 4 * ((x - s0) / D0x) * Real.sqrt (x - s0) / (2 * D1x * S_eff) ≤
        (((omxL_6 * omxL_6 * xR4_6 * phi2_hi_6 * q_hi_n : ℕ) : ℝ) /
          ((2 * D1_lo_6 * S_eff_lo_6 * K6 * K6 * 1000 : ℕ) : ℝ)) := by
      have hden_pos : 0 < 2 * ((D1_lo_6 : ℝ) / K6) * ((S_eff_lo_6 : ℝ) / K6) :=
        mul_pos (mul_pos (by norm_num) hD1_pos') hS_pos'
      have hnum_rhs_nn : 0 ≤ ((omxL_6 : ℝ) / K6) ^ 2 * ((xR4_6 : ℝ) / K6) * ((phi2_hi_6 : ℝ) / K6) * ((q_hi_n : ℝ) / 1000) :=
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hxR4_nn_ub) hphi2_nn_ub) hqhi_nn_ub
      have hdiv1 := div_le_div₀ hnum_rhs_nn hnum_le hden_pos hden_ge
      have heq : (((omxL_6 : ℝ) / K6) ^ 2 * ((xR4_6 : ℝ) / K6) * ((phi2_hi_6 : ℝ) / K6) * ((q_hi_n : ℝ) / 1000)) /
          (2 * ((D1_lo_6 : ℝ) / K6) * ((S_eff_lo_6 : ℝ) / K6)) =
          ((omxL_6 * omxL_6 * xR4_6 * phi2_hi_6 * q_hi_n : ℕ) : ℝ) /
            ((2 * D1_lo_6 * S_eff_lo_6 * K6 * K6 * 1000 : ℕ) : ℝ) := by
        push_cast
        have hK6' : (K6 : ℝ) ≠ 0 := by exact_mod_cast hK6_pos.ne'
        have hD1' : (D1_lo_6 : ℝ) ≠ 0 := by exact_mod_cast hD1_lo_6_pos.ne'
        have hS' : (S_eff_lo_6 : ℝ) ≠ 0 := by exact_mod_cast hS_eff_lo_6_pos.ne'
        field_simp [hK6', hD1', hS']
      exact hdiv1.trans_eq heq
    have hden_nat_pos : 0 < 2 * D1_lo_6 * S_eff_lo_6 * K6 * K6 * 1000 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hD1_lo_6_pos)
        hS_eff_lo_6_pos) hK6_pos) hK6_pos) (by decide)
    dsimp only [t1_9]
    exact hdiv_le.trans (natDiv_le_natCeil K9 (omxL_6 * omxL_6 * xR4_6 * phi2_hi_6 * q_hi_n)
      (2 * D1_lo_6 * S_eff_lo_6 * K6 * K6 * 1000) hK9_pos hden_nat_pos)
  have h2_term : 4 * (1 - x) * x ^ 4 * (1 - s1) * Real.sqrt (x - s0) / (D1x ^ 2 * S_eff ^ 2) ≤
      (t2_9 : ℝ) / (K9 : ℝ) := by
    have h1s1_eq : 1 - s1 = ((s1_d - s1_n : ℕ) : ℝ) / (s1_d : ℝ) := by
      dsimp [s1]
      rw [Nat.cast_sub hs1_lt.le]
      dsimp [s1_d, s1_n]
      have h1d : ((q1 * q1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs1d_pos.ne'
      field_simp [h1d]
    have hnum_le : 4 * (1 - x) * x ^ 4 * (1 - s1) * Real.sqrt (x - s0) ≤
        4 * ((omxL_6 : ℝ) / K6) * ((xR4_6 : ℝ) / K6) * (((s1_d - s1_n : ℕ) : ℝ) / s1_d) *
          ((q_hi_n : ℝ) / 1000) := by
      have h1s1_nn : 0 ≤ 1 - s1 := by linarith only [hs1_le]
      rw [← h1s1_eq]
      have h4omx : 4 * (1 - x) ≤ 4 * ((omxL_6 : ℝ) / K6) :=
        mul_le_mul_of_nonneg_left homx_le (by norm_num)
      have hx4_nn : 0 ≤ x ^ 4 := pow_nonneg hx_ge0 4
      have h1_step := mul_le_mul h4omx hx4_le hx4_nn (mul_nonneg (by norm_num) homx_nn_ub)
      have h2_step := mul_le_mul_of_nonneg_right h1_step h1s1_nn
      exact mul_le_mul h2_step hsqrt_le (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) homx_nn_ub) hxR4_nn_ub) h1s1_nn)
    have hden_ge : ((D1_lo_6 : ℝ) / K6) ^ 2 * ((S_eff_lo_6 : ℝ) / K6) ^ 2 ≤ D1x ^ 2 * S_eff ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hD1_pos'.le hD1_ge_6 2) (pow_le_pow_left₀ hS_pos'.le hS_eff_ge 2)
        (sq_nonneg _) (sq_nonneg _)
    have hdiv_le : 4 * (1 - x) * x ^ 4 * (1 - s1) * Real.sqrt (x - s0) / (D1x ^ 2 * S_eff ^ 2) ≤
        (((4 * omxL_6 * xR4_6 * (s1_d - s1_n) * q_hi_n * K6 * K6 : ℕ) : ℝ) /
          ((D1_lo_6 * D1_lo_6 * S_eff_lo_6 * S_eff_lo_6 * s1_d * 1000 : ℕ) : ℝ)) := by
      have hden_pos : 0 < ((D1_lo_6 : ℝ) / K6) ^ 2 * ((S_eff_lo_6 : ℝ) / K6) ^ 2 :=
        mul_pos (sq_pos_of_pos hD1_pos') (sq_pos_of_pos hS_pos')
      have hs1_diff_nn : 0 ≤ ((s1_d - s1_n : ℕ) : ℝ) / s1_d :=
        div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hs1d_pos.le)
      have hnum_rhs_nn : 0 ≤ 4 * ((omxL_6 : ℝ) / K6) * ((xR4_6 : ℝ) / K6) * (((s1_d - s1_n : ℕ) : ℝ) / s1_d) *
          ((q_hi_n : ℝ) / 1000) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) homx_nn_ub) hxR4_nn_ub) hs1_diff_nn) hqhi_nn_ub
      have hdiv1 := div_le_div₀ hnum_rhs_nn hnum_le hden_pos hden_ge
      have heq : (4 * ((omxL_6 : ℝ) / K6) * ((xR4_6 : ℝ) / K6) * (((s1_d - s1_n : ℕ) : ℝ) / s1_d) *
            ((q_hi_n : ℝ) / 1000)) /
          (((D1_lo_6 : ℝ) / K6) ^ 2 * ((S_eff_lo_6 : ℝ) / K6) ^ 2) =
          ((4 * omxL_6 * xR4_6 * (s1_d - s1_n) * q_hi_n * K6 * K6 : ℕ) : ℝ) /
            ((D1_lo_6 * D1_lo_6 * S_eff_lo_6 * S_eff_lo_6 * s1_d * 1000 : ℕ) : ℝ) := by
        push_cast
        have hK6' : (K6 : ℝ) ≠ 0 := by exact_mod_cast hK6_pos.ne'
        have hD1' : (D1_lo_6 : ℝ) ≠ 0 := by exact_mod_cast hD1_lo_6_pos.ne'
        have hS' : (S_eff_lo_6 : ℝ) ≠ 0 := by exact_mod_cast hS_eff_lo_6_pos.ne'
        have h1d' : (s1_d : ℝ) ≠ 0 := by exact_mod_cast hs1d_pos.ne'
        field_simp [hK6', hD1', hS', h1d']
      exact hdiv1.trans_eq heq
    have hden_nat_pos : 0 < D1_lo_6 * D1_lo_6 * S_eff_lo_6 * S_eff_lo_6 * s1_d * 1000 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hD1_lo_6_pos hD1_lo_6_pos)
        hS_eff_lo_6_pos) hS_eff_lo_6_pos) hs1d_pos) (by decide)
    dsimp only [t2_9]
    exact hdiv_le.trans (natDiv_le_natCeil K9 (4 * omxL_6 * xR4_6 * (s1_d - s1_n) * q_hi_n * K6 * K6)
      (D1_lo_6 * D1_lo_6 * S_eff_lo_6 * S_eff_lo_6 * s1_d * 1000) hK9_pos hden_nat_pos)
  unfold rem3Upper
  dsimp only [D0x, D1x, S_eff] at h1_term h2_term
  have hsum : ((t1_9 + t2_9 : ℕ) : ℝ) / (K9 : ℝ) = (t1_9 : ℝ) / K9 + (t2_9 : ℝ) / K9 := by
    push_cast; ring
  dsimp only
  linarith only [h1_term, h2_term, hsum]

theorem chordDelta_three_pos_of_check (p0 q0 p1 q1 d : ℕ)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hle : p0 * q1 < p1 * q0) (hp1 : 2 * p1 ≤ q1)
    (hcheck : checkN3BlockPow2 p0 q0 p1 q1 d = true)
    {t : ℝ} (ht0 : 0 < t) (hlo : (p0 : ℝ) / q0 ≤ t) (hhi : t ≤ (p1 : ℝ) / q1) :
    0 < chordDelta 3 t := by
  let K9 : ℕ := 1000000000
  let Nx : ℕ := 2 ^ d
  let s0_n := p0 * p0
  let s0_d := q0 * q0
  let s1_n := p1 * p1
  let s1_d := q1 * q1
  let s0 : ℝ := (s0_n : ℝ) / (s0_d : ℝ)
  let s1 : ℝ := (s1_n : ℝ) / (s1_d : ℝ)
  have hs0d_pos : 0 < s0_d := Nat.mul_pos hq0 hq0
  have hs1d_pos : 0 < s1_d := Nat.mul_pos hq1 hq1
  have hNx_pos : 0 < Nx := Nat.two_pow_pos d
  have hK9_pos : 0 < K9 := by decide
  have hs0_nn : 0 ≤ s0 := by dsimp [s0]; positivity
  have hs1_nn : 0 ≤ s1 := by dsimp [s1]; positivity
  have hs0_t : s0 ≤ t ^ 2 := by
    have h1 : (p0 : ℝ) / q0 ≥ 0 := by positivity
    have h2 : s0 = ((p0 : ℝ) / q0) ^ 2 := by dsimp [s0, s0_n, s0_d]; push_cast; ring
    rw [h2]
    exact pow_le_pow_left₀ h1 hlo 2
  have ht_s1 : t ^ 2 ≤ s1 := by
    have h2 : s1 = ((p1 : ℝ) / q1) ^ 2 := by dsimp [s1, s1_n, s1_d]; push_cast; ring
    rw [h2]
    exact pow_le_pow_left₀ ht0.le hhi 2
  have ht1_half : (p1 : ℝ) / q1 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by exact_mod_cast hq1) (by norm_num)]
    have : ((2 * p1 : ℕ) : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hp1
    push_cast at this; linarith
  have hs1_le : s1 ≤ 1 / 4 := by
    have h2 : s1 = ((p1 : ℝ) / q1) ^ 2 := by dsimp [s1, s1_n, s1_d]; push_cast; ring
    rw [h2]; nlinarith
  have hs0_le : s0 ≤ 1 / 4 := hs0_t.trans (ht_s1.trans hs1_le)
  have ht_lt1 : t < 1 := by linarith
  have ht_m1 : -1 < t := by linarith
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  have hmain_real := mainTerm_three_ge_block ht0 hhi ht1_half
  have ha2_1_eq : 1 - s1 = ((s1_d - s1_n : ℕ) : ℝ) / (s1_d : ℝ) := by
    have hs1_lt : s1_n ≤ s1_d := by dsimp [s1_n, s1_d]; nlinarith
    dsimp [s1]; rw [Nat.cast_sub hs1_lt]
    have h1d : (s1_d : ℝ) ≠ 0 := by exact_mod_cast hs1d_pos.ne'
    field_simp [h1d]
  let a2_1_n := s1_d - s1_n
  let r_lo_n := n3RLo a2_1_n s1_d
  let mlb_n := 176 * a2_1_n ^ 3 * r_lo_n * s1_d
  let mlb_d := 315 * s1_d ^ 3 * 1000 * (11 * s1_d - 8 * s1_n)
  have hs1_lt : s1_n ≤ s1_d := by
    have h4 : (2 * p1) * (2 * p1) ≤ q1 * q1 := Nat.mul_le_mul hp1 hp1
    dsimp [s1_n, s1_d]
    calc
      p1 * p1 ≤ (2 * p1) * (2 * p1) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ q1 * q1 := h4
  have hr_lo_le : (r_lo_n : ℝ) / 1000 ≤ Real.sqrt (1 - s1) := by
    rw [ha2_1_eq]
    dsimp only [r_lo_n, n3RLo]
    exact @nfSqrtLB_le_real_sqrt_nfVal (a2_1_n, s1_d) hs1d_pos (Nat.sub_le _ _)
  have h8_le : 8 * s1_n < 11 * s1_d := by
    have h4 : (2 * p1) * (2 * p1) ≤ q1 * q1 := Nat.mul_le_mul hp1 hp1
    have h8 : 8 * s1_n ≤ 2 * s1_d := by
      dsimp [s1_n, s1_d]
      calc
        8 * (p1 * p1) = 2 * ((2 * p1) * (2 * p1)) := by ring
        _ ≤ 2 * (q1 * q1) := Nat.mul_le_mul_left 2 h4
    omega
  have h11_8_pos : 0 < 11 * s1_d - 8 * s1_n := by omega
  have hmlb_d_pos : 0 < mlb_d := by
    have : 0 < 315 := by decide
    have : 0 < 1000 := by decide
    positivity
  have hmlb_rat : (mlb_n : ℝ) / (mlb_d : ℝ) ≤
      (176 / 315 : ℝ) * (1 - ((p1 : ℝ) / q1) ^ 2) ^ 3 * Real.sqrt (1 - ((p1 : ℝ) / q1) ^ 2) /
        (11 - 8 * ((p1 : ℝ) / q1) ^ 2) := by
    have hs1_eq : ((p1 : ℝ) / q1) ^ 2 = s1 := by dsimp [s1, s1_n, s1_d]; push_cast; ring
    rw [hs1_eq]
    have heq_rat : (mlb_n : ℝ) / (mlb_d : ℝ) =
        (176 / 315 : ℝ) * (1 - s1) ^ 3 * ((r_lo_n : ℝ) / 1000) / (11 - 8 * s1) := by
      dsimp [mlb_n, mlb_d]
      rw [ha2_1_eq]
      dsimp [s1, a2_1_n]
      push_cast [Nat.cast_sub h8_le.le, Nat.cast_sub hs1_lt]
      have h1d : (s1_d : ℝ) ≠ 0 := by exact_mod_cast hs1d_pos.ne'
      have hden : 11 * (s1_d : ℝ) - 8 * (s1_n : ℝ) ≠ 0 := by
        have : 0 < 11 * (s1_d : ℝ) - 8 * (s1_n : ℝ) := by
          have : ((8 * s1_n : ℕ) : ℝ) < ((11 * s1_d : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 8 * s1_n < 11 * s1_d)
          push_cast at this; linarith only [this]
        exact this.ne'
      field_simp [h1d, hden]
    rw [heq_rat]
    have hden_pos : 0 < 11 - 8 * s1 := by linarith only [hs1_le]
    have h1s1_nn : 0 ≤ 1 - s1 := by linarith only [hs1_le]
    gcongr
  have hmain_mlb : (mlb_n : ℝ) / (mlb_d : ℝ) ≤
      ∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v) :=
    hmlb_rat.trans hmain_real
  let dx : ℝ := (1 - s0) / (Nx : ℝ)
  let xPt : ℕ → ℝ := fun k => s0 + (k : ℝ) * dx
  have hu_cont := continuousOn_rem3Upper hs0_nn hs0_le hs1_nn hs1_le
  have hsum_adj : (∑ k ∈ Finset.range Nx, ∫ x in xPt k..xPt (k + 1), rem3Upper s0 s1 x) =
      ∫ x in xPt 0..xPt Nx, rem3Upper s0 s1 x := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro k hk_lt
    have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ Nx := by exact_mod_cast hk_lt
    have hx_le1 : xPt (k + 1) ≤ 1 := by
      dsimp [xPt, dx]
      have hdx_nn : 0 ≤ (1 - s0) / (Nx : ℝ) := div_nonneg (by linarith) (by positivity)
      calc
        s0 + ((k + 1 : ℕ) : ℝ) * ((1 - s0) / (Nx : ℝ))
            ≤ s0 + (Nx : ℝ) * ((1 - s0) / (Nx : ℝ)) := by gcongr
        _ = 1 := by
            have hNx' : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
            field_simp [hNx']; ring
    have hx0_ge : 0 ≤ xPt k := by
      dsimp [xPt, dx]
      have hdx_nn : 0 ≤ (1 - s0) / (Nx : ℝ) := div_nonneg (by linarith) (by positivity)
      positivity
    have hk_le : xPt k ≤ xPt (k + 1) := by
      dsimp [xPt, dx]
      have hdx_nn : 0 ≤ (1 - s0) / (Nx : ℝ) := div_nonneg (by linarith) (by positivity)
      push_cast
      nlinarith
    exact (hu_cont.mono (Icc_subset_Icc hx0_ge hx_le1)).intervalIntegrable_of_Icc hk_le
  have hxPt0 : xPt 0 = s0 := by dsimp [xPt]; simp
  have hxPtNx : xPt Nx = 1 := by
    dsimp [xPt, dx]
    have hNx' : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
    field_simp [hNx']; ring
  have hbox_sum : (∫ x in s0..1, rem3Upper s0 s1 x) ≤
      ((sumNatPow2 (n3BlockBoxCeil p0 q0 p1 q1 Nx) 0 d : ℕ) : ℝ) / (K9 : ℝ) := by
    have hgoal_eq : (∫ x in s0..1, rem3Upper s0 s1 x) =
        ∫ x in xPt 0..xPt Nx, rem3Upper s0 s1 x := by
      rw [hxPt0, hxPtNx]
    rw [hgoal_eq, ← hsum_adj, sumNatPow2_eq_sum]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < Nx := Finset.mem_range.mp hk
    have hx_le : xPt k ≤ xPt (k + 1) := by
      dsimp [xPt, dx]
      have hdx_nn : 0 ≤ (1 - s0) / (Nx : ℝ) := div_nonneg (by linarith) (by positivity)
      push_cast
      nlinarith
    have hx0_ge : 0 ≤ xPt k := by
      dsimp [xPt, dx]
      have hdx_nn : 0 ≤ (1 - s0) / (Nx : ℝ) := div_nonneg (by linarith) (by positivity)
      positivity
    have hx1_le : xPt (k + 1) ≤ 1 := by
      dsimp [xPt, dx]
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ Nx := by exact_mod_cast hk_lt
      have hdx_nn : 0 ≤ (1 - s0) / (Nx : ℝ) := div_nonneg (by linarith) (by positivity)
      calc
        s0 + ((k + 1 : ℕ) : ℝ) * ((1 - s0) / (Nx : ℝ))
            ≤ s0 + (Nx : ℝ) * ((1 - s0) / (Nx : ℝ)) := by gcongr
        _ = 1 := by
            have hNx' : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
            field_simp [hNx']; ring
    have hconst := rem3Upper_box_le p0 q0 p1 q1 d k hq0 hq1 hle hp1 hk_lt
    dsimp only at hconst
    set B : ℕ := n3BoxDensityUB p0 q0 p1 q1 Nx k
    have hbox_int : IntervalIntegrable (rem3Upper s0 s1) volume (xPt k) (xPt (k + 1)) :=
      (hu_cont.mono (Icc_subset_Icc hx0_ge hx1_le)).intervalIntegrable_of_Icc hx_le
    have hmono_box : (∫ x in xPt k..xPt (k + 1), rem3Upper s0 s1 x) ≤
        ∫ _ in xPt k..xPt (k + 1), ((B : ℝ) / (K9 : ℝ)) :=
      intervalIntegral.integral_mono_on hx_le hbox_int intervalIntegrable_const hconst
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono_box
    have hwidth : xPt (k + 1) - xPt k = dx := by
      dsimp [xPt]; push_cast; ring
    rw [hwidth] at hmono_box
    have hs0_lt : s0_n ≤ s0_d := by
      have hp0_lt : 2 * p0 < q0 := by nlinarith only [hle, hp1, hq1]
      dsimp [s0_n, s0_d]
      exact Nat.mul_le_mul (by omega) (by omega)
    have hdx_eq : dx = ((s0_d - s0_n : ℕ) : ℝ) / ((s0_d * Nx : ℕ) : ℝ) := by
      dsimp [dx, s0]; rw [Nat.cast_sub hs0_lt]; dsimp [s0_d, s0_n]; push_cast
      have h0d : ((q0 * q0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hs0d_pos.ne'
      have hNx' : (Nx : ℝ) ≠ 0 := by exact_mod_cast hNx_pos.ne'
      field_simp [h0d, hNx']
    have hceil := natDiv_le_natCeil K9 ((s0_d - s0_n) * B) (s0_d * Nx * K9) hK9_pos
      (by positivity)
    have hmul_eq : dx * ((B : ℝ) / (K9 : ℝ)) =
        (((s0_d - s0_n) * B : ℕ) : ℝ) / ((s0_d * Nx * K9 : ℕ) : ℝ) := by
      rw [hdx_eq]; push_cast; ring
    have hbox_eq : n3BlockBoxCeil p0 q0 p1 q1 Nx (0 + k) =
        natCeil K9 ((q0 * q0 - p0 * p0) * B) (q0 * q0 * Nx * K9) := by
      rw [Nat.zero_add]
      rfl
    change _ ≤ ((n3BlockBoxCeil p0 q0 p1 q1 Nx (0 + k) : ℕ) : ℝ) / (K9 : ℝ)
    rw [hbox_eq]
    dsimp only [s0_d, s0_n] at hceil hmul_eq
    linarith only [hmono_box, hceil, hmul_eq]
  have hrem_upper := (rem3Clean_integral_le_rem3Upper hs0_nn hs0_t ht_s1 hs1_le).trans hbox_sum
  unfold checkN3BlockPow2 at hcheck
  dsimp only at hcheck
  rw [decide_eq_true_eq] at hcheck
  have hr_lt_m : ((sumNatPow2 (n3BlockBoxCeil p0 q0 p1 q1 Nx) 0 d : ℕ) : ℝ) / (K9 : ℝ) <
      (mlb_n : ℝ) / (mlb_d : ℝ) := by
    rw [div_lt_div_iff₀ (by exact_mod_cast hK9_pos) (by exact_mod_cast hmlb_d_pos)]
    exact_mod_cast hcheck
  have hdiff_pos : 0 < (∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) -
      (∫ v in (0 : ℝ)..a, rem3Clean t v) := by
    linarith only [hmain_mlb, hrem_upper, hr_lt_m]
  have hmain_cont : ContinuousOn (fun v => (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) (Icc 0 a) := by
    have hD_cont : Continuous (chordD t) := by
      unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
    have hx_cont : Continuous (chordX t) := by
      unfold chordX; exact continuous_const.add (continuous_pow 2)
    exact (((continuous_const.sub hx_cont).pow 3).mul ((continuous_pow 2).div hD_cont fun v =>
      (chordD_pos ht_lt1 ht_m1 v).ne')).continuousOn
  have hmain_int : IntervalIntegrable (fun v => (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) volume 0 a :=
    hmain_cont.intervalIntegrable_of_Icc ha_pos.le
  have hrem_int : IntervalIntegrable (rem3Clean t) volume 0 a :=
    (rem3Clean_continuousOn ht_m1 ht_lt1).intervalIntegrable_of_Icc ha_pos.le
  have hchord_int : IntervalIntegrable (chordIntegrand 3 t) volume 0 a :=
    chordIntegrand_intervalIntegrable 3 (by omega) ht0.le ht_lt1
  have hmono : (∫ v in (0 : ℝ)..a, t * ((1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v) - rem3Clean t v)) ≤
      ∫ v in (0 : ℝ)..a, chordIntegrand 3 t v :=
    intervalIntegral.integral_mono_on_of_le_Ioo ha_pos.le ((hmain_int.sub hrem_int).const_mul t)
      hchord_int (fun v hv => chordIntegrand_three_ge_clean ht0 ht_lt1 hv.1 hv.2)
  have hsplit : (∫ v in (0 : ℝ)..a, t * ((1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v) - rem3Clean t v)) =
      t * ((∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) -
        (∫ v in (0 : ℝ)..a, rem3Clean t v)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hmain_int hrem_int]
  have hint_pos : 0 < ∫ v in (0 : ℝ)..a, chordIntegrand 3 t v := by
    have h1 : 0 < t * ((∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ 3 * (v ^ 2 / chordD t v)) -
        (∫ v in (0 : ℝ)..a, rem3Clean t v)) := mul_pos ht0 hdiff_pos
    linarith only [h1, hmono, hsplit]
  rw [chordDelta_eq_chordDeltaIntegral]
  unfold chordDeltaIntegral
  exact mul_pos (div_pos (by norm_num) Real.pi_pos) hint_pos

/-- `chordDelta 3 t > 0` for all `t ∈ (0, 1/2]` via the 5-block kernel-verified certificate. -/
theorem chordDelta_three_pos {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) :
    0 < chordDelta 3 t := by
  rcases ht with ⟨ht0, ht_half⟩
  by_cases h1 : t ≤ 1 / 4
  · exact chordDelta_three_pos_of_check 0 1 1 4 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) n3_block0_certified ht0 (by norm_num; exact ht0.le) (by norm_num; exact h1)
  · by_cases h2 : t ≤ 7 / 20
    · exact chordDelta_three_pos_of_check 1 4 7 20 4 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) n3_block1_certified ht0 (by norm_num; linarith) (by norm_num; exact h2)
    · by_cases h3 : t ≤ 21 / 50
      · exact chordDelta_three_pos_of_check 7 20 21 50 5 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) n3_block2_certified ht0 (by norm_num; linarith) (by norm_num; exact h3)
      · by_cases h4 : t ≤ 23 / 50
        · exact chordDelta_three_pos_of_check 21 50 23 50 5 (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) n3_block3_certified ht0 (by norm_num; linarith) (by norm_num; exact h4)
        · exact chordDelta_three_pos_of_check 23 50 1 2 7 (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) n3_block4_certified ht0 (by norm_num; linarith) (by norm_num; exact ht_half)

end SharpL1.Analysis
