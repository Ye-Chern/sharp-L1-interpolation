import Mathlib.Data.Real.Basic

/-!
# Nonnegativity of the alternating left fold

For a nondecreasing list of nonnegative reals, the left fold
`fun acc x => x - acc` starting at `0` is nonnegative. Reading the list from
the left, the running value alternates signs, so this is the input to the
exterior monotonicity argument in the paper.
-/

namespace SharpL1.Analysis

/-- General form. If the accumulator `a` is nonnegative and lies below every
remaining element, and the remaining list is nondecreasing, then the
alternating fold stays nonnegative.

The induction keeps the invariant `0 ≤ a ≤ x` for the head `x`: the next
accumulator `x - a` lies in `[0, x]`, hence is still below every later
element by monotonicity. -/
theorem foldl_sub_nonneg {a : ℝ} {xs : List ℝ}
    (ha : 0 ≤ a) (hs : xs.Pairwise (· ≤ ·)) (h : ∀ x ∈ xs, a ≤ x) :
    0 ≤ xs.foldl (fun acc x => x - acc) a := by
  induction xs generalizing a with
  | nil => simpa using ha
  | cons x t ih =>
    obtain ⟨hxt, hpt⟩ := List.pairwise_cons.mp hs
    have hax : a ≤ x := h x (by simp)
    have hsub : 0 ≤ x - a := sub_nonneg.mpr hax
    have ht : ∀ y ∈ t, x - a ≤ y := by
      intro y hy
      exact (sub_le_self x ha).trans (hxt y hy)
    simpa using ih (a := x - a) hsub hpt ht

/-- For a nondecreasing list of nonnegative reals, the alternating left fold
starting at zero is nonnegative. -/
theorem foldl_alternating_nonneg {xs : List ℝ}
    (hs : xs.Pairwise (· ≤ ·)) (h0 : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ xs.foldl (fun acc x => x - acc) 0 :=
  foldl_sub_nonneg le_rfl hs h0

end SharpL1.Analysis
