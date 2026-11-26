import SharpL1.Analysis.RootBranches
import SharpL1.JacobiContainment
import SharpL1.JacobiOrdered
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! ## The ordered Jacobi roots follow the local branches in the interior -/

namespace SharpL1

open Filter Set Topology

theorem hasDerivAt_orderedNode (k : ℕ) {t : ℝ} (ht : |t| < 1) (i : Fin (k + 2)) :
    HasDerivAt (fun s => orderedNode k s i)
      (2 * (1 - orderedNode k t i ^ 2) / speedDenominator (k + 1) t (orderedNode k t i)) t := by
  have hy (j : Fin (k + 2)) : |orderedNode k t j| < 1 :=
    abs_lt.mpr (nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t j))
  obtain ⟨u, δ, lo, hi, hδ, hat, hdiff, hderiv, hrect, hsub, hsep, hs⟩ :=
    simultaneous_full_root_branches_roots_eq k ht (orderedNode k t) hy
      (orderedNode_eval_eq_zero k t) (orderedNode_strictMono k t)
  have hev : (fun s => orderedNode k s i) =ᶠ[𝓝 t] (u i) := by
    filter_upwards [Ioo_mem_nhds (show t - δ < t by linarith) (show t < t + δ by linarith)]
      with s hs'
    obtain ⟨_, hmono, hroots, _⟩ := hs s hs'
    exact congrFun (orderedNode_eq_of_strictMono_of_roots k s _ hmono hroots) i
  exact (hderiv i).congr_of_eventuallyEq hev

theorem orderedNode_deriv_bounds (k : ℕ) {t : ℝ} (ht : |t| < 1) (i : Fin (k + 2)) :
    0 < deriv (fun s => orderedNode k s i) t ∧
      deriv (fun s => orderedNode k s i) t ≤ 2 / (((k + 1 : ℕ) : ℝ) + 1) := by
  have hy : |orderedNode k t i| < 1 :=
    abs_lt.mpr (nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t i))
  have hd := hasDerivAt_orderedNode k ht i
  rw [hd.deriv]
  exact node_speed_bounds k _ _ _ ht hy hd (.of_forall fun s => orderedNode_eval_eq_zero k s i)

theorem orderedNode_strictMonoOn (k : ℕ) (i : Fin (k + 2)) :
    StrictMonoOn (fun t => orderedNode k t i) (Ioo (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro t ht
    exact (hasDerivAt_orderedNode k (abs_lt.mpr ht) i).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := interior_subset ht
    exact (orderedNode_deriv_bounds k (abs_lt.mpr ht') i).1

theorem orderedNode_coefficient_monotoneOn (k : ℕ) (i : Fin (k + 2)) :
    MonotoneOn (fun t => t - orderedNode k t i) (Ioo (-1 : ℝ) 1) := by
  have hd (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun x => x - orderedNode k x i)
        (1 - 2 * (1 - orderedNode k t i ^ 2) / speedDenominator (k + 1) t (orderedNode k t i)) t :=
    (hasDerivAt_id t).sub (hasDerivAt_orderedNode k (abs_lt.mpr ht) i)
  apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := interior_subset ht
    rw [(hd t ht').deriv, ← (hasDerivAt_orderedNode k (abs_lt.mpr ht') i).deriv]
    have hbound := (orderedNode_deriv_bounds k (abs_lt.mpr ht') i).2
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hscale : (2 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      push_cast
      linarith
    linarith [hbound.trans hscale]

end SharpL1
