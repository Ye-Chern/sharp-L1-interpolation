import SharpL1.Analysis.NodeSpeed
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local differentiable root branches for the Jacobi pencil

Given `k : ℕ` and an interior root `(t, y)` with `|t| < 1`, `|y| ≤ 1`, and
`(nodePolynomial k t).eval y = 0`, we apply Mathlib's inverse function theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph` / `HasStrictFDerivAt.localInverse`)
to `nodeMap k (s, x) = (s, (nodePolynomial k s).eval x)` to construct a local
differentiable branch `u : ℝ → ℝ` near `t`.

This file proves:
1. Local existence (`u t = y`, `HasStrictDerivAt`, `DifferentiableAt ℝ u t`,
   `∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0`), together with the exact
   node speed formula via `hasDerivAt_node_speed` when `|y| < 1`.
2. Local uniqueness near `(t, y)`: in a neighborhood of `(t, y)` (and on an explicit
   open rectangle `(t - δ, t + δ) × (y - ε, y + ε)`), `(nodePolynomial k s).eval x = 0 ↔ x = u s`.
3. Simultaneous disjoint (and order-preserving) local branches for a finite family
   of distinct or strictly increasing roots in `(-1, 1)` at `t`, plus multiset exhaustion
   when the family has full size `k + 2`.
-/

namespace SharpL1

open Polynomial Filter Topology Set
open Polynomial.Chebyshev (U)

/-! ### Auxiliary map and invertible lower-triangular derivative -/

/-- The map `(s, x) ↦ (s, p_s(x))` used to construct local root branches via the
inverse function theorem. -/
noncomputable def nodeMap (k : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, (nodePolynomial k p.1).eval p.2)

/-- Continuous linear equivalence on `ℝ × ℝ` given by the lower-triangular map
`(ds, dx) ↦ (ds, a * ds + b * dx)` for `b ≠ 0`. -/
noncomputable def lowerTriangularEquiv (a b : ℝ) (hb : b ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (p.1, a * p.1 + b * p.2)
  invFun q := (q.1, (q.2 - a * q.1) / b)
  map_add' p q := by
    ext
    · rfl
    · dsimp; ring
  map_smul' c p := by
    ext
    · rfl
    · dsimp; ring
  left_inv p := by
    ext
    · rfl
    · dsimp
      field_simp
      ring
  right_inv q := by
    ext
    · rfl
    · dsimp
      field_simp
      ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem lowerTriangularEquiv_apply (a b : ℝ) (hb : b ≠ 0) (p : ℝ × ℝ) :
    lowerTriangularEquiv a b hb p = (p.1, a * p.1 + b * p.2) :=
  rfl

@[simp]
theorem lowerTriangularEquiv_symm_apply (a b : ℝ) (hb : b ≠ 0) (q : ℝ × ℝ) :
    (lowerTriangularEquiv a b hb).symm q = (q.1, (q.2 - a * q.1) / b) :=
  rfl

private theorem hasStrictFDerivAt_eval_U (m : ℤ) (t y : ℝ) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => (U ℝ m).eval p.2)
      (((derivative (U ℝ m)).eval y) • ContinuousLinearMap.snd ℝ ℝ ℝ) (t, y) := by
  have hsnd : HasStrictFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (t, y) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt
  have h := ((U ℝ m).hasStrictDerivAt y).comp_hasStrictFDerivAt (t, y) hsnd
  exact h

/-- Strict Fréchet derivative of `nodeMap k` at any `(t, y) : ℝ × ℝ`. -/
theorem hasStrictFDerivAt_nodeMap (k : ℕ) (t y : ℝ) :
    HasStrictFDerivAt (nodeMap k)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (nodePolynomialDerivT k t y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (derivative (nodePolynomial k t)).eval y • ContinuousLinearMap.snd ℝ ℝ ℝ))
      (t, y) := by
  have hfst : HasStrictFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (t, y) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt
  have hU2 := hasStrictFDerivAt_eval_U ((k : ℤ) + 2) t y
  have hU1 := hasStrictFDerivAt_eval_U ((k : ℤ) + 1) t y
  have hU0 := hasStrictFDerivAt_eval_U (k : ℤ) t y
  have h2s : HasStrictFDerivAt (fun p : ℝ × ℝ => 2 * p.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (t, y) :=
    hfst.const_mul (2 : ℝ)
  have hs2 : HasStrictFDerivAt (fun p : ℝ × ℝ => p.1 ^ 2)
      ((2 * t) • ContinuousLinearMap.fst ℝ ℝ ℝ) (t, y) := by
    have h := (hasStrictDerivAt_pow 2 t).comp_hasStrictFDerivAt (t, y) hfst
    rw [show ((2 : ℕ) : ℝ) * t ^ (2 - 1) = 2 * t by norm_num] at h
    exact h
  have h2sU1 := h2s.mul hU1
  have hs2U0 := hs2.mul hU0
  have heval : HasStrictFDerivAt (fun p : ℝ × ℝ => (nodePolynomial k p.1).eval p.2)
      (nodePolynomialDerivT k t y • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (derivative (nodePolynomial k t)).eval y • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, y) := by
    have hcomb := (hU2.sub h2sU1).add hs2U0
    have hfun : (fun p : ℝ × ℝ => (nodePolynomial k p.1).eval p.2) =
        ((fun p : ℝ × ℝ => (U ℝ ((k : ℤ) + 2)).eval p.2) -
          (fun p : ℝ × ℝ => 2 * p.1) * (fun p : ℝ × ℝ => (U ℝ ((k : ℤ) + 1)).eval p.2) +
          (fun p : ℝ × ℝ => p.1 ^ 2) * (fun p : ℝ × ℝ => (U ℝ k).eval p.2)) := by
      funext p
      simp [nodePolynomial]
    have hder :
        ((derivative (U ℝ ((k : ℤ) + 2))).eval y • ContinuousLinearMap.snd ℝ ℝ ℝ -
            ((2 * (t, y).1) • (derivative (U ℝ ((k : ℤ) + 1))).eval y •
                ContinuousLinearMap.snd ℝ ℝ ℝ +
              (U ℝ ((k : ℤ) + 1)).eval (t, y).2 • (2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
          ((t, y).1 ^ 2 • (derivative (U ℝ k)).eval y • ContinuousLinearMap.snd ℝ ℝ ℝ +
            (U ℝ k).eval (t, y).2 • (2 * t) • ContinuousLinearMap.fst ℝ ℝ ℝ)) =
        (nodePolynomialDerivT k t y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (derivative (nodePolynomial k t)).eval y • ContinuousLinearMap.snd ℝ ℝ ℝ) := by
      apply ContinuousLinearMap.ext
      intro p
      simp only [nodePolynomial, derivative_add, derivative_sub, derivative_C_mul,
        eval_add, eval_sub, eval_mul, eval_C, nodePolynomialDerivT,
        add_apply, sub_apply, smul_apply]
      ring
    rw [hfun, ← hder]
    exact hcomb
  exact hfst.prodMk heval

/-- Invertible strict Fréchet derivative of `nodeMap k` at an interior root `(t, y)`. -/
theorem hasStrictFDerivAt_nodeMap_equiv (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    HasStrictFDerivAt (nodeMap k)
      ((lowerTriangularEquiv (nodePolynomialDerivT k t y)
        ((derivative (nodePolynomial k t)).eval y)
        (derivative_nodePolynomial_ne_zero_of_root k ht hy hroot) :
        (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
      (t, y) := by
  have hder :
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (nodePolynomialDerivT k t y • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (derivative (nodePolynomial k t)).eval y • ContinuousLinearMap.snd ℝ ℝ ℝ)) =
      ((lowerTriangularEquiv (nodePolynomialDerivT k t y)
        ((derivative (nodePolynomial k t)).eval y)
        (derivative_nodePolynomial_ne_zero_of_root k ht hy hroot) :
        (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := by
    apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · rfl
    · simp [lowerTriangularEquiv, smul_eq_mul]
  rw [← hder]
  exact hasStrictFDerivAt_nodeMap k t y

/-! ### Priority 1: Local differentiable root branch and exact speed -/

/-- Local root branch `u : ℝ → ℝ` passing through `(t, y)` for `nodePolynomial k`,
obtained as the second coordinate of the local inverse of `nodeMap k`. -/
noncomputable def localRootBranch (k : ℕ) (t y : ℝ)
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) : ℝ → ℝ :=
  fun s =>
    ((hasStrictFDerivAt_nodeMap_equiv k ht hy hroot).localInverse (nodeMap k)
      (lowerTriangularEquiv (nodePolynomialDerivT k t y)
        ((derivative (nodePolynomial k t)).eval y)
        (derivative_nodePolynomial_ne_zero_of_root k ht hy hroot))
      (t, y) (s, 0)).2

@[simp]
theorem localRootBranch_at (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    localRootBranch k t y ht hy hroot t = y := by
  have hnode : nodeMap k (t, y) = (t, 0) := by
    simp [nodeMap, hroot]
  have hinv := (hasStrictFDerivAt_nodeMap_equiv k ht hy hroot).localInverse_apply_image
  rw [hnode] at hinv
  simpa [localRootBranch] using congr_arg Prod.snd hinv

/-- Strict differentiability of `localRootBranch` at `t` with explicit implicit-function
derivative `-∂_t p(t, y) / ∂_y p(t, y)`. -/
theorem hasStrictDerivAt_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    HasStrictDerivAt (localRootBranch k t y ht hy hroot)
      (-nodePolynomialDerivT k t y / (derivative (nodePolynomial k t)).eval y) t := by
  have hf := hasStrictFDerivAt_nodeMap_equiv k ht hy hroot
  have hinv := hf.to_localInverse
  have hnode : nodeMap k (t, y) = (t, 0) := by
    simp [nodeMap, hroot]
  rw [hnode] at hinv
  have hslice : HasStrictFDerivAt (fun s : ℝ => (s, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) t :=
    (hasStrictFDerivAt_id t).prodMk (hasStrictFDerivAt_const (0 : ℝ) t)
  have hcomp := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt.comp t
    (hinv.comp t hslice)
  have hderiv := hcomp.hasStrictDerivAt
  have hval :
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (((lowerTriangularEquiv (nodePolynomialDerivT k t y)
          ((derivative (nodePolynomial k t)).eval y)
          (derivative_nodePolynomial_ne_zero_of_root k ht hy hroot)).symm :
            (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)))) 1 =
      -nodePolynomialDerivT k t y / (derivative (nodePolynomial k t)).eval y := by
    change ((((lowerTriangularEquiv (nodePolynomialDerivT k t y)
      ((derivative (nodePolynomial k t)).eval y)
      (derivative_nodePolynomial_ne_zero_of_root k ht hy hroot)).symm) (1, 0)).2) = _
    rw [lowerTriangularEquiv_symm_apply]
    ring
  rw [hval] at hderiv
  exact hderiv

theorem hasDerivAt_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    HasDerivAt (localRootBranch k t y ht hy hroot)
      (-nodePolynomialDerivT k t y / (derivative (nodePolynomial k t)).eval y) t :=
  (hasStrictDerivAt_localRootBranch k ht hy hroot).hasDerivAt

theorem differentiableAt_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    DifferentiableAt ℝ (localRootBranch k t y ht hy hroot) t :=
  (hasDerivAt_localRootBranch k ht hy hroot).differentiableAt

theorem continuousAt_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    ContinuousAt (localRootBranch k t y ht hy hroot) t :=
  (differentiableAt_localRootBranch k ht hy hroot).continuousAt

/-- Near `t`, `localRootBranch` is a root of `nodePolynomial k s`. -/
theorem eventually_eval_localRootBranch_eq_zero (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    ∀ᶠ s in nhds t,
      (nodePolynomial k s).eval (localRootBranch k t y ht hy hroot s) = 0 := by
  have hf := hasStrictFDerivAt_nodeMap_equiv k ht hy hroot
  have hright := hf.eventually_right_inverse
  have hnode : nodeMap k (t, y) = (t, 0) := by
    simp [nodeMap, hroot]
  rw [hnode] at hright
  have hcont : Continuous (fun s : ℝ => (s, (0 : ℝ))) := by fun_prop
  have hpull : ∀ᶠ s in nhds t,
      nodeMap k (hf.localInverse (nodeMap k) _ (t, y) (s, 0)) = (s, 0) :=
    (hcont.continuousAt.eventually hright)
  refine hpull.mono ?_
  intro s hs
  have h1 : (hf.localInverse (nodeMap k) _ (t, y) (s, 0)).1 = s :=
    congr_arg Prod.fst hs
  have h2 : (nodePolynomial k
      (hf.localInverse (nodeMap k) _ (t, y) (s, 0)).1).eval
      (localRootBranch k t y ht hy hroot s) = 0 :=
    congr_arg Prod.snd hs
  rwa [h1] at h2

/-- Exact `HasDerivAt` node speed formula for `localRootBranch`, expressed in terms of `u t`. -/
theorem hasDerivAt_node_speed_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| < 1) (hroot : (nodePolynomial k t).eval y = 0) :
    let u := localRootBranch k t y ht hy.le hroot
    HasDerivAt u (2 * (1 - u t ^ 2) / speedDenominator (k + 1) t (u t)) t := by
  intro u
  have hu_lt : |u t| < 1 := by
    simpa [u, localRootBranch_at] using hy
  exact hasDerivAt_node_speed k u t ht hu_lt
    (differentiableAt_localRootBranch k ht hy.le hroot)
    (eventually_eval_localRootBranch_eq_zero k ht hy.le hroot)

/-- Exact `HasDerivAt` node speed formula for `localRootBranch`, expressed in terms of `y`. -/
theorem hasDerivAt_node_speed_localRootBranch_at_root (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| < 1) (hroot : (nodePolynomial k t).eval y = 0) :
    HasDerivAt (localRootBranch k t y ht hy.le hroot)
      (2 * (1 - y ^ 2) / speedDenominator (k + 1) t y) t := by
  simpa [localRootBranch_at] using
    hasDerivAt_node_speed_localRootBranch k ht hy hroot

/-- Near `t`, `localRootBranch` remains strictly differentiable everywhere in a neighborhood of `t`. -/
theorem eventually_hasStrictDerivAt_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| < 1) (hroot : (nodePolynomial k t).eval y = 0) :
    ∀ᶠ s in nhds t,
      HasStrictDerivAt (localRootBranch k t y ht hy.le hroot)
        (-nodePolynomialDerivT k s (localRootBranch k t y ht hy.le hroot s) /
          (derivative (nodePolynomial k s)).eval
            (localRootBranch k t y ht hy.le hroot s)) s := by
  let hf := hasStrictFDerivAt_nodeMap_equiv k ht hy.le hroot
  let e := hf.toOpenPartialHomeomorph (nodeMap k)
  have hnode : nodeMap k (t, y) = (t, 0) := by
    simp [nodeMap, hroot]
  have hmem_tgt : (t, (0 : ℝ)) ∈ e.target := by
    rw [← hnode]
    exact hf.image_mem_toOpenPartialHomeomorph_target
  have hslice_cont : ContinuousAt (fun s : ℝ => (s, (0 : ℝ))) t :=
    (continuousAt_id (x := t)).prodMk continuousAt_const
  have hs_tgt : ∀ᶠ s in nhds t, (s, (0 : ℝ)) ∈ e.target :=
    hslice_cont (e.open_target.mem_nhds hmem_tgt)
  have hs_right : ∀ᶠ s in nhds t, nodeMap k (e.symm (s, 0)) = (s, 0) := by
    have hr := hf.eventually_right_inverse
    rw [hnode] at hr
    exact hslice_cont.eventually hr
  have hs_abs : ∀ᶠ s in nhds t, |s| < 1 :=
    Filter.Eventually.mono (Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2) fun _ hs =>
      abs_lt.mpr hs
  have hu_abs : ∀ᶠ s in nhds t, |localRootBranch k t y ht hy.le hroot s| < 1 := by
    have h : ∀ᶠ s in nhds t, localRootBranch k t y ht hy.le hroot s ∈ Ioo (-1) 1 := by
      have htend := (continuousAt_localRootBranch k ht hy.le hroot).tendsto
      rw [localRootBranch_at] at htend
      exact htend (Ioo_mem_nhds (abs_lt.mp hy).1 (abs_lt.mp hy).2)
    exact h.mono fun _ hs => abs_lt.mpr hs
  have hev_root := eventually_eval_localRootBranch_eq_zero k ht hy.le hroot
  filter_upwards [hs_tgt, hs_right, hs_abs, hu_abs, hev_root] with
    s hstgt hsright hsabs huabs hsroot
  have hsymm_eq : e.symm (s, 0) = (s, localRootBranch k t y ht hy.le hroot s) := by
    have h1 : (e.symm (s, 0)).1 = s := congr_arg Prod.fst hsright
    exact Prod.ext h1 rfl
  have hf_s : HasStrictFDerivAt e
      ((lowerTriangularEquiv (nodePolynomialDerivT k s (localRootBranch k t y ht hy.le hroot s))
        ((derivative (nodePolynomial k s)).eval (localRootBranch k t y ht hy.le hroot s))
        (derivative_nodePolynomial_ne_zero_of_root k hsabs huabs.le hsroot) :
        (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
      (e.symm (s, 0)) := by
    rw [hsymm_eq]
    exact hasStrictFDerivAt_nodeMap_equiv k hsabs huabs.le hsroot
  have hinv_s := e.hasStrictFDerivAt_symm hstgt hf_s
  have hslice_s : HasStrictFDerivAt (fun r : ℝ => (r, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) s :=
    (hasStrictFDerivAt_id s).prodMk (hasStrictFDerivAt_const (0 : ℝ) s)
  have hcomp_s := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt.comp s
    (hinv_s.comp s hslice_s)
  have hderiv_s := hcomp_s.hasStrictDerivAt
  have hval_s :
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (((lowerTriangularEquiv (nodePolynomialDerivT k s (localRootBranch k t y ht hy.le hroot s))
          ((derivative (nodePolynomial k s)).eval (localRootBranch k t y ht hy.le hroot s))
          (derivative_nodePolynomial_ne_zero_of_root k hsabs huabs.le hsroot)).symm :
            (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)))) 1 =
      -nodePolynomialDerivT k s (localRootBranch k t y ht hy.le hroot s) /
        (derivative (nodePolynomial k s)).eval (localRootBranch k t y ht hy.le hroot s) := by
    change ((((lowerTriangularEquiv
      (nodePolynomialDerivT k s (localRootBranch k t y ht hy.le hroot s))
      ((derivative (nodePolynomial k s)).eval (localRootBranch k t y ht hy.le hroot s))
      (derivative_nodePolynomial_ne_zero_of_root k hsabs huabs.le hsroot)).symm) (1, 0)).2) = _
    rw [lowerTriangularEquiv_symm_apply]
    ring
  rw [hval_s] at hderiv_s
  exact hderiv_s

/-- Near `t`, `localRootBranch` is differentiable on a neighborhood of `t`. -/
theorem eventually_differentiableAt_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| < 1) (hroot : (nodePolynomial k t).eval y = 0) :
    ∀ᶠ s in nhds t, DifferentiableAt ℝ (localRootBranch k t y ht hy.le hroot) s :=
  (eventually_hasStrictDerivAt_localRootBranch k ht hy hroot).mono fun _ h =>
    h.hasDerivAt.differentiableAt

/-- Near `t`, `localRootBranch` satisfies the exact `HasDerivAt` node speed formula on a
neighborhood of `t`. -/
theorem eventually_hasDerivAt_node_speed_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| < 1) (hroot : (nodePolynomial k t).eval y = 0) :
    let u := localRootBranch k t y ht hy.le hroot
    ∀ᶠ s in nhds t,
      HasDerivAt u (2 * (1 - u s ^ 2) / speedDenominator (k + 1) s (u s)) s := by
  intro u
  have hs_abs : ∀ᶠ s in nhds t, |s| < 1 :=
    Filter.Eventually.mono (Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2) fun _ hs =>
      abs_lt.mpr hs
  have hu_abs : ∀ᶠ s in nhds t, |u s| < 1 := by
    have h : ∀ᶠ s in nhds t, u s ∈ Ioo (-1) 1 := by
      have htend := (continuousAt_localRootBranch k ht hy.le hroot).tendsto
      rw [localRootBranch_at] at htend
      exact htend (Ioo_mem_nhds (abs_lt.mp hy).1 (abs_lt.mp hy).2)
    exact h.mono fun _ hs => abs_lt.mpr hs
  have hdiff := eventually_differentiableAt_localRootBranch k ht hy hroot
  have hev_root := (eventually_eval_localRootBranch_eq_zero k ht hy.le hroot).eventually_nhds
  filter_upwards [hs_abs, hu_abs, hdiff, hev_root] with s hs_lt hu_lt hs_diff hs_root
  exact hasDerivAt_node_speed k u s hs_lt hu_lt hs_diff hs_root

/-- Existential summary of Priority 1 for a single interior root `(t, y)`. -/
theorem exists_local_root_branch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| < 1) (hroot : (nodePolynomial k t).eval y = 0) :
    ∃ u : ℝ → ℝ,
      u t = y ∧
      DifferentiableAt ℝ u t ∧
      (∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0) ∧
      HasDerivAt u (2 * (1 - u t ^ 2) / speedDenominator (k + 1) t (u t)) t ∧
      HasDerivAt u (2 * (1 - y ^ 2) / speedDenominator (k + 1) t y) t := by
  refine ⟨localRootBranch k t y ht hy.le hroot, ?_, ?_, ?_, ?_, ?_⟩
  · exact localRootBranch_at k ht hy.le hroot
  · exact differentiableAt_localRootBranch k ht hy.le hroot
  · exact eventually_eval_localRootBranch_eq_zero k ht hy.le hroot
  · exact hasDerivAt_node_speed_localRootBranch k ht hy hroot
  · exact hasDerivAt_node_speed_localRootBranch_at_root k ht hy hroot

/-! ### Priority 2a: Local uniqueness near `(t, y)` -/

/-- Local uniqueness in a neighborhood of `(t, y)` in `ℝ × ℝ`:
`(nodePolynomial k s).eval x = 0 ↔ x = u s`. -/
theorem eventually_nodePolynomial_eq_zero_iff_eq_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    ∀ᶠ p : ℝ × ℝ in nhds (t, y),
      (nodePolynomial k p.1).eval p.2 = 0 ↔
        p.2 = localRootBranch k t y ht hy hroot p.1 := by
  have hf := hasStrictFDerivAt_nodeMap_equiv k ht hy hroot
  have hleft := hf.eventually_left_inverse
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (t, y),
      (nodePolynomial k p.1).eval (localRootBranch k t y ht hy hroot p.1) = 0 :=
    (continuous_fst.continuousAt (x := (t, y))).eventually
      (eventually_eval_localRootBranch_eq_zero k ht hy hroot)
  filter_upwards [hleft, hev] with p hp_left hp_root
  constructor
  · intro hpx
    have hmap : nodeMap k p = (p.1, 0) := by
      simp [nodeMap, hpx]
    rw [hmap] at hp_left
    exact (congr_arg Prod.snd hp_left).symm
  · intro hpx
    rwa [hpx]

/-- Rectangle form of local uniqueness and branch containment around `(t, y)`. -/
theorem exists_unique_root_rectangle_localRootBranch (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    ∃ δ > 0, ∃ ε > 0,
      ∀ s ∈ Ioo (t - δ) (t + δ),
        localRootBranch k t y ht hy hroot s ∈ Ioo (y - ε) (y + ε) ∧
        (nodePolynomial k s).eval (localRootBranch k t y ht hy hroot s) = 0 ∧
        ∀ x ∈ Ioo (y - ε) (y + ε),
          ((nodePolynomial k s).eval x = 0 ↔ x = localRootBranch k t y ht hy hroot s) := by
  have hiff := eventually_nodePolynomial_eq_zero_iff_eq_localRootBranch k ht hy hroot
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hiff
  rcases hiff with ⟨P, hP, Q, hQ, hPQ⟩
  rcases Metric.mem_nhds_iff.mp hP with ⟨δ₁, hδ₁, hball₁⟩
  rcases Metric.mem_nhds_iff.mp hQ with ⟨ε, hε, hball₂⟩
  have hcont : ∀ᶠ s in nhds t, |localRootBranch k t y ht hy hroot s - y| < ε := by
    have h := (continuousAt_localRootBranch k ht hy hroot).tendsto
    rw [localRootBranch_at] at h
    exact h (Metric.ball_mem_nhds y hε)
  have hev_root := eventually_eval_localRootBranch_eq_zero k ht hy hroot
  rcases Metric.mem_nhds_iff.mp (hcont.and hev_root) with ⟨δ₂, hδ₂, hball₂'⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ε, hε, ?_⟩
  intro s hs
  have hst : dist s t < min δ₁ δ₂ := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hs.1, hs.2]
  have hs1 : s ∈ Metric.ball t δ₁ := hst.trans_le (min_le_left _ _)
  have hs2 : s ∈ Metric.ball t δ₂ := hst.trans_le (min_le_right _ _)
  rcases hball₂' hs2 with ⟨hdist, hsr⟩
  refine ⟨?_, hsr, ?_⟩
  · rcases abs_lt.mp hdist with ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · intro x hx
    have hxball : x ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hx.1, hx.2]
    exact hPQ (hball₁ hs1) (hball₂ hxball)

/-! ### Priority 2b: Simultaneous disjoint local branches for finite root families -/

/-- Simultaneous local differentiable branches for a finite family `y : Fin m → ℝ` of
distinct roots of `nodePolynomial k t` in `(-1, 1)`, staying inside pairwise disjoint
open intervals `(lo i, hi i) ⊆ (-1, 1)` where each `u i s` is the unique root of
`nodePolynomial k s` for all `s ∈ (t - δ, t + δ)`. -/
theorem simultaneous_local_root_branches (k m : ℕ) {t : ℝ} (ht : |t| < 1)
    (y : Fin m → ℝ) (hy_lt : ∀ i, |y i| < 1)
    (hroot : ∀ i, (nodePolynomial k t).eval (y i) = 0)
    (hinj : Function.Injective y) :
    ∃ (u : Fin m → ℝ → ℝ) (δ : ℝ) (lo hi : Fin m → ℝ),
      0 < δ ∧
      (∀ i, u i t = y i) ∧
      (∀ i, DifferentiableAt ℝ (u i) t) ∧
      (∀ i, HasDerivAt (u i) (2 * (1 - y i ^ 2) / speedDenominator (k + 1) t (y i)) t) ∧
      (∀ i, lo i < y i ∧ y i < hi i) ∧
      (∀ i, Ioo (lo i) (hi i) ⊆ Ioo (-1) 1) ∧
      Pairwise (fun i j => Disjoint (Icc (lo i) (hi i)) (Icc (lo j) (hi j))) ∧
      (∀ s ∈ Ioo (t - δ) (t + δ),
        |s| < 1 ∧
        ∀ i,
          u i s ∈ Ioo (lo i) (hi i) ∧
          (nodePolynomial k s).eval (u i s) = 0 ∧
          DifferentiableAt ℝ (u i) s ∧
          HasDerivAt (u i) (2 * (1 - u i s ^ 2) / speedDenominator (k + 1) s (u i s)) s ∧
          ∀ x ∈ Ioo (lo i) (hi i), ((nodePolynomial k s).eval x = 0 ↔ x = u i s)) := by
  let u : Fin m → ℝ → ℝ := fun i => localRootBranch k t (y i) ht (hy_lt i).le (hroot i)
  have hrect : ∀ i : Fin m, ∃ δi > 0, ∃ εi > 0,
      ∀ s ∈ Ioo (t - δi) (t + δi),
        u i s ∈ Ioo (y i - εi) (y i + εi) ∧
        (nodePolynomial k s).eval (u i s) = 0 ∧
        ∀ x ∈ Ioo (y i - εi) (y i + εi),
          ((nodePolynomial k s).eval x = 0 ↔ x = u i s) :=
    fun i => exists_unique_root_rectangle_localRootBranch k ht (hy_lt i).le (hroot i)
  let δi : Fin m → ℝ := fun i => Classical.choose (hrect i)
  have hδi_pos : ∀ i, 0 < δi i := fun i => (Classical.choose_spec (hrect i)).1
  let εi : Fin m → ℝ := fun i => Classical.choose (Classical.choose_spec (hrect i)).2
  have hεi_pos : ∀ i, 0 < εi i := fun i => (Classical.choose_spec (Classical.choose_spec (hrect i)).2).1
  have hrect_spec : ∀ i s, s ∈ Ioo (t - δi i) (t + δi i) →
      u i s ∈ Ioo (y i - εi i) (y i + εi i) ∧
      (nodePolynomial k s).eval (u i s) = 0 ∧
      ∀ x ∈ Ioo (y i - εi i) (y i + εi i), ((nodePolynomial k s).eval x = 0 ↔ x = u i s) :=
    fun i => (Classical.choose_spec (Classical.choose_spec (hrect i)).2).2
  -- Choose a uniform radius `ε > 0` small enough for `ε ≤ εi i`, `Ioo (y i - ε) (y i + ε) ⊆ (-1, 1)`,
  -- and pairwise disjointness.
  let cand : Finset ℝ :=
    ({1} : Finset ℝ) ∪
    (Finset.univ.image εi) ∪
    (Finset.univ.image fun i => 1 - |y i|) ∪
    ((Finset.univ.product Finset.univ).filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).image
      (fun p => |y p.1 - y p.2| / 3)
  have hcand_pos : ∀ c ∈ cand, 0 < c := by
    intro c hc
    simp only [cand, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ((rfl | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩) | ⟨⟨i, j⟩, hij, rfl⟩
    · norm_num
    · exact hεi_pos i
    · linarith [hy_lt i]
    · have hne : y i - y j ≠ 0 := sub_ne_zero.mpr (hinj.ne hij.2)
      exact div_pos (abs_pos.mpr hne) (by norm_num)
  have hcand_ne : cand.Nonempty := ⟨1, by simp [cand]⟩
  let ε : ℝ := cand.min' hcand_ne
  have hε_pos : 0 < ε := hcand_pos ε (Finset.min'_mem cand hcand_ne)
  have hε_le_εi : ∀ i, ε ≤ εi i := fun i =>
    Finset.min'_le cand _ (by simp [cand])
  have hε_le_bd : ∀ i, ε ≤ 1 - |y i| := fun i =>
    Finset.min'_le cand _ (by simp [cand])
  have hε_le_sep : ∀ i j, i ≠ j → ε ≤ |y i - y j| / 3 := fun i j hij =>
    Finset.min'_le cand _ (by
      simp only [cand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      right
      exact ⟨(i, j), ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij⟩, rfl⟩)
  -- Choose `δ > 0` small enough for `|s| < 1`, `s ∈ Ioo (t - δi i) (t + δi i)`,
  -- and `u i s ∈ Ioo (y i - ε) (y i + ε)`.
  have hu_cont : ∀ i, ∀ᶠ s in nhds t, u i s ∈ Ioo (y i - ε) (y i + ε) := by
    intro i
    have h := (continuousAt_localRootBranch k ht (hy_lt i).le (hroot i)).tendsto
    rw [localRootBranch_at] at h
    exact h (Ioo_mem_nhds (by linarith) (by linarith))
  have hev_all : ∀ᶠ s in nhds t, ∀ i : Fin m,
      u i s ∈ Ioo (y i - ε) (y i + ε) ∧
      DifferentiableAt ℝ (u i) s ∧
      HasDerivAt (u i) (2 * (1 - u i s ^ 2) / speedDenominator (k + 1) s (u i s)) s := by
    refine Filter.eventually_all.mpr fun i => ?_
    exact (hu_cont i).and
      ((eventually_differentiableAt_localRootBranch k ht (hy_lt i) (hroot i)).and
        (eventually_hasDerivAt_node_speed_localRootBranch k ht (hy_lt i) (hroot i)))
  rcases Metric.mem_nhds_iff.mp hev_all with ⟨δu, hδu_pos, hδu_ball⟩
  let dcand : Finset ℝ :=
    ({1 - |t|, δu} : Finset ℝ) ∪ Finset.univ.image δi
  have hdcand_pos : ∀ d ∈ dcand, 0 < d := by
    intro d hd
    simp only [dcand, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and] at hd
    rcases hd with (rfl | rfl) | ⟨i, -, rfl⟩
    · linarith [ht]
    · exact hδu_pos
    · exact hδi_pos i
  have hdcand_ne : dcand.Nonempty := ⟨1 - |t|, by simp [dcand]⟩
  let δ : ℝ := dcand.min' hdcand_ne
  have hδ_pos : 0 < δ := hdcand_pos δ (Finset.min'_mem dcand hdcand_ne)
  have hδ_le_t : δ ≤ 1 - |t| := Finset.min'_le dcand _ (by simp [dcand])
  have hδ_le_u : δ ≤ δu := Finset.min'_le dcand _ (by simp [dcand])
  have hδ_le_i : ∀ i, δ ≤ δi i := fun i => Finset.min'_le dcand _ (by simp [dcand])
  refine ⟨u, δ, fun i => y i - ε, fun i => y i + ε, hδ_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact localRootBranch_at k ht (hy_lt i).le (hroot i)
  · intro i; exact differentiableAt_localRootBranch k ht (hy_lt i).le (hroot i)
  · intro i; exact hasDerivAt_node_speed_localRootBranch_at_root k ht (hy_lt i) (hroot i)
  · intro i; constructor <;> linarith
  · intro i x hx
    have hybd := abs_lt.mp (hy_lt i)
    have hle := hε_le_bd i
    rcases le_or_gt 0 (y i) with hy0 | hy0
    · rw [abs_of_nonneg hy0] at hle
      exact ⟨by linarith [hx.1, hybd.1], by linarith [hx.2, hle]⟩
    · rw [abs_of_neg hy0] at hle
      exact ⟨by linarith [hx.1, hle], by linarith [hx.2, hybd.2]⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hsep := hε_le_sep i j hij
    rcases le_or_gt (y i) (y j) with hle | hlt
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hsep
      linarith [hxi.2, hxj.1]
    · rw [abs_of_pos (sub_pos.mpr hlt)] at hsep
      linarith [hxi.1, hxj.2]
  · intro s hs
    have hst : |s - t| < δ := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hs_abs : |s| < 1 := by
      calc |s| = |(s - t) + t| := by ring_nf
        _ ≤ |s - t| + |t| := abs_add_le _ _
        _ < δ + |t| := by linarith
        _ ≤ 1 := by linarith [hδ_le_t]
    refine ⟨hs_abs, ?_⟩
    intro i
    have hs_ball : s ∈ Metric.ball t δu := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hst hδ_le_u
    have hs_i : s ∈ Ioo (t - δi i) (t + δi i) := by
      have h1 : |s - t| < δi i := lt_of_lt_of_le hst (hδ_le_i i)
      rcases abs_lt.mp h1 with ⟨ha, hb⟩
      exact ⟨by linarith, by linarith⟩
    have hspec := hrect_spec i s hs_i
    have hball_i := hδu_ball hs_ball i
    refine ⟨hball_i.1, hspec.2.1, hball_i.2.1, hball_i.2.2, ?_⟩
    intro x hx
    have hxi : x ∈ Ioo (y i - εi i) (y i + εi i) := by
      have hle := hε_le_εi i
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact hspec.2.2 x hxi

/-- Order-preserving variant of `simultaneous_local_root_branches` for strictly increasing
roots `y : Fin m → ℝ`. -/
theorem simultaneous_strictMono_root_branches (k m : ℕ) {t : ℝ} (ht : |t| < 1)
    (y : Fin m → ℝ) (hy_lt : ∀ i, |y i| < 1)
    (hroot : ∀ i, (nodePolynomial k t).eval (y i) = 0)
    (hmono : StrictMono y) :
    ∃ (u : Fin m → ℝ → ℝ) (δ : ℝ) (lo hi : Fin m → ℝ),
      0 < δ ∧
      (∀ i, u i t = y i) ∧
      (∀ i, DifferentiableAt ℝ (u i) t) ∧
      (∀ i, HasDerivAt (u i) (2 * (1 - y i ^ 2) / speedDenominator (k + 1) t (y i)) t) ∧
      (∀ i, lo i < y i ∧ y i < hi i) ∧
      (∀ i, Ioo (lo i) (hi i) ⊆ Ioo (-1) 1) ∧
      (∀ i j, i < j → hi i < lo j) ∧
      (∀ s ∈ Ioo (t - δ) (t + δ),
        |s| < 1 ∧
        StrictMono (fun i => u i s) ∧
        ∀ i,
          u i s ∈ Ioo (lo i) (hi i) ∧
          (nodePolynomial k s).eval (u i s) = 0 ∧
          DifferentiableAt ℝ (u i) s ∧
          HasDerivAt (u i) (2 * (1 - u i s ^ 2) / speedDenominator (k + 1) s (u i s)) s ∧
          ∀ x ∈ Ioo (lo i) (hi i), ((nodePolynomial k s).eval x = 0 ↔ x = u i s)) := by
  obtain ⟨u, δ, lo, hi, hδ, hat, hdiff, hderiv, hcont_y, hsub, hdisj, hspec⟩ :=
    simultaneous_local_root_branches k m ht y hy_lt hroot hmono.injective
  have hsep : ∀ i j : Fin m, i < j → hi i < lo j := by
    intro i j hij
    by_contra hle
    push Not at hle
    have hd := hdisj hij.ne
    dsimp only at hd
    rw [Set.disjoint_left] at hd
    have hmem_i : max (lo i) (lo j) ∈ Icc (lo i) (hi i) := by
      refine ⟨le_max_left _ _, max_le ((hcont_y i).1.trans (hcont_y i).2).le hle⟩
    have hmem_j : max (lo i) (lo j) ∈ Icc (lo j) (hi j) := by
      have hlo_hi : lo i ≤ hi j :=
        ((hcont_y i).1.trans ((hmono hij).trans (hcont_y j).2)).le
      refine ⟨le_max_right _ _, max_le hlo_hi ((hcont_y j).1.trans (hcont_y j).2).le⟩
    exact hd hmem_i hmem_j
  refine ⟨u, δ, lo, hi, hδ, hat, hdiff, hderiv, hcont_y, hsub, hsep, ?_⟩
  intro s hs
  obtain ⟨hs_abs, hsi⟩ := hspec s hs
  refine ⟨hs_abs, ?_, hsi⟩
  intro i j hij
  calc
    u i s < hi i := (hsi i).1.2
    _ < lo j := hsep i j hij
    _ < u j s := (hsi j).1.1

/-- When a finite family of `k + 2` distinct interior roots at `t` is continued to
simultaneous disjoint local branches, their images exhaust `(nodePolynomial k s).roots`
for every `s ∈ (t - δ, t + δ)`. -/
theorem simultaneous_full_root_branches_roots_eq (k : ℕ) {t : ℝ} (ht : |t| < 1)
    (y : Fin (k + 2) → ℝ) (hy_lt : ∀ i, |y i| < 1)
    (hroot : ∀ i, (nodePolynomial k t).eval (y i) = 0)
    (hmono : StrictMono y) :
    ∃ (u : Fin (k + 2) → ℝ → ℝ) (δ : ℝ) (lo hi : Fin (k + 2) → ℝ),
      0 < δ ∧
      (∀ i, u i t = y i) ∧
      (∀ i, DifferentiableAt ℝ (u i) t) ∧
      (∀ i, HasDerivAt (u i) (2 * (1 - y i ^ 2) / speedDenominator (k + 1) t (y i)) t) ∧
      (∀ i, lo i < y i ∧ y i < hi i) ∧
      (∀ i, Ioo (lo i) (hi i) ⊆ Ioo (-1) 1) ∧
      (∀ i j, i < j → hi i < lo j) ∧
      (∀ s ∈ Ioo (t - δ) (t + δ),
        |s| < 1 ∧
        StrictMono (fun i => u i s) ∧
        (nodePolynomial k s).roots = (Finset.univ.image (fun i => u i s)).val ∧
        ∀ i,
          u i s ∈ Ioo (lo i) (hi i) ∧
          (nodePolynomial k s).eval (u i s) = 0 ∧
          DifferentiableAt ℝ (u i) s ∧
          HasDerivAt (u i) (2 * (1 - u i s ^ 2) / speedDenominator (k + 1) s (u i s)) s ∧
          ∀ x ∈ Ioo (lo i) (hi i), ((nodePolynomial k s).eval x = 0 ↔ x = u i s)) := by
  obtain ⟨u, δ, lo, hi, hδ, hat, hdiff, hderiv, hcont_y, hsub, hsep, hspec⟩ :=
    simultaneous_strictMono_root_branches k (k + 2) ht y hy_lt hroot hmono
  refine ⟨u, δ, lo, hi, hδ, hat, hdiff, hderiv, hcont_y, hsub, hsep, ?_⟩
  intro s hs
  obtain ⟨hs_abs, hmono_s, hsi⟩ := hspec s hs
  refine ⟨hs_abs, hmono_s, ?_, hsi⟩
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact (hsi i).2.1
  · rw [natDegree_nodePolynomial, Finset.card_image_of_injective Finset.univ hmono_s.injective]
    simp
  · exact nodePolynomial_ne_zero k s

end SharpL1
