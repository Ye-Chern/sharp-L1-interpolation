import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! ## The explicit interpolation error at a parameter -/

namespace SharpL1.Analysis

/-- Equation `Eexplicit` for ordered nodes at parameter `t`. -/
noncomputable def explicitError (n : ℕ) (u : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  1 - t - (2 : ℝ) ^ n / ((n : ℝ) + 1) * (1 - t) ^ (n + 1) +
    (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
      ∑ j : Fin (n + 1), (-1 : ℝ) ^ (n - j.val) * (max (u j - t) 0) ^ (n + 1)

end SharpL1.Analysis
