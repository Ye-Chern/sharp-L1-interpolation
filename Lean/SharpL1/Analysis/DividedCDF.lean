module

public import SharpL1.Analysis.DividedDifference
public import Lean.Elab.Tactic.Omega

public section

/-! ## Finite differences of truncated powers -/

namespace SharpL1.Analysis

open Polynomial

/-- At order zero this is the closed indicator, consistent with the CDF at a
singleton node. At higher orders it is the corresponding positive-part power. -/
@[expose] noncomputable def truncatedPower (m : ℕ) (t y : ℝ) : ℝ :=
  if t ≤ y then (y - t) ^ m else 0

theorem truncatedPower_succ (m : ℕ) (t y : ℝ) :
    truncatedPower (m + 1) t y = (y - t) * truncatedPower m t y := by
  by_cases h : t ≤ y <;> simp [truncatedPower, h, pow_succ']

theorem barycentric_truncatedPower_nonneg_side {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (ha : Set.InjOn a s) (hs : s.Nonempty)
    (t : ℝ) (ht : ∀ i ∈ s, t ≤ a i) :
    barycentricDividedDifferenceOn s a (fun i => truncatedPower (s.card - 1) t (a i)) = 1 := by
  let p : ℝ[X] := (X - C t) ^ (s.card - 1)
  have hcard := Finset.card_pos.mpr hs
  have hm : p.Monic := (monic_X_sub_C t).pow _
  have hn : p.natDegree = s.card - 1 := by simp [p]
  have hd : p.degree < s.card := by
    rw [degree_eq_natDegree hm.ne_zero, hn]
    exact_mod_cast (show s.card - 1 < s.card by omega)
  calc
    _ = barycentricDividedDifferenceOn s a (fun i => p.eval (a i)) := by
      unfold barycentricDividedDifferenceOn
      exact Finset.sum_congr rfl fun i hi => by simp [truncatedPower, ht i hi, p]
    _ = p.coeff (s.card - 1) := barycentricDividedDifferenceOn_eval_eq_coeff ha p hd
    _ = 1 := by rw [← hn, coeff_natDegree]; exact hm

theorem barycentric_truncatedPower_nonpos_side {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) {m : ℕ} (hm : 0 < m)
    (t : ℝ) (ht : ∀ i ∈ s, a i ≤ t) :
    barycentricDividedDifferenceOn s a (fun i => truncatedPower m t (a i)) = 0 := by
  unfold barycentricDividedDifferenceOn
  apply Finset.sum_eq_zero
  intro i hi
  rcases (ht i hi).lt_or_eq with h | h
  · simp [truncatedPower, h.not_ge]
  · simp [truncatedPower, h, Nat.ne_of_gt hm]

/-- The two adjacent differences give the mixed branch of the interpolation
table for truncated powers. This identity also holds outside the mixed region. -/
theorem barycentric_truncatedPower_erase_pair {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (hinj : Set.InjOn a s) {l h : ι}
    (hl : l ∈ s) (hh : h ∈ s) (horder : a l < a h) (m : ℕ) (t : ℝ) :
    barycentricDividedDifferenceOn s a (fun i => truncatedPower (m + 1) t (a i)) =
      ((a h - t) * barycentricDividedDifferenceOn (s.erase l) a (fun i => truncatedPower m t (a i)) +
        (t - a l) * barycentricDividedDifferenceOn (s.erase h) a (fun i => truncatedPower m t (a i))) /
          (a h - a l) := by
  simp only [truncatedPower_succ]
  rw [← barycentricDividedDifferenceOn_mul_sub_erase hinj hl,
    ← barycentricDividedDifferenceOn_mul_sub_erase hinj hh]
  apply (eq_div_iff (sub_ne_zero.mpr horder.ne')).2
  simp only [barycentricDividedDifferenceOn, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end SharpL1.Analysis
