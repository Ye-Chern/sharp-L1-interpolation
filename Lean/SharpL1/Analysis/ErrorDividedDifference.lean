import SharpL1.Analysis.DividedCDF

/-! ## Algebraic form of the four-law derivative identity -/

namespace SharpL1.Analysis

theorem barycentric_truncatedPower_erase {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (hinj : Set.InjOn a s) {c : ι} (hc : c ∈ s)
    (m : ℕ) (t : ℝ) :
    barycentricDividedDifferenceOn (s.erase c) a (fun i => truncatedPower m t (a i)) =
      barycentricDividedDifferenceOn s a (fun i => truncatedPower (m + 1) t (a i)) +
        (t - a c) * barycentricDividedDifferenceOn s a (fun i => truncatedPower m t (a i)) := by
  rw [← barycentricDividedDifferenceOn_mul_sub_erase hinj hc]
  simp only [truncatedPower_succ, barycentricDividedDifferenceOn, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem barycentric_truncatedPower_erase_endpoints {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (hinj : Set.InjOn a s) {l h : ι} (hl : l ∈ s) (hh : h ∈ s)
    (hlv : a l = -1) (hhv : a h = 1) (m : ℕ) (t : ℝ) :
    barycentricDividedDifferenceOn ((s.erase l).erase h) a (fun i => truncatedPower m t (a i)) =
      barycentricDividedDifferenceOn s a (fun i => truncatedPower (m + 2) t (a i)) +
        2 * t * barycentricDividedDifferenceOn s a (fun i => truncatedPower (m + 1) t (a i)) +
        (t ^ 2 - 1) * barycentricDividedDifferenceOn s a (fun i => truncatedPower m t (a i)) := by
  have hne : h ≠ l := by
    intro heq
    rw [heq, hlv] at hhv
    norm_num at hhv
  have hh' := Finset.mem_erase.mpr ⟨hne, hh⟩
  rw [barycentric_truncatedPower_erase (hinj.mono (Finset.erase_subset _ _)) hh',
    barycentric_truncatedPower_erase hinj hl, barycentric_truncatedPower_erase hinj hl,
    hlv, hhv]
  ring

/-- The polynomial weight in the explicit derivative equals the combination
of full and deleted-node differences in `Hcomp`. For a probability law these
differences represent the closed zero-threshold CDFs. -/
theorem barycentric_Hcomp {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (hinj : Set.InjOn a s) {l h : ι} (hl : l ∈ s) (hh : h ∈ s)
    (hlv : a l = -1) (hhv : a h = 1) (n : ℕ) (t : ℝ) :
    let D (v : Finset ι) (m : ℕ) :=
      barycentricDividedDifferenceOn v a (fun i => truncatedPower m t (a i))
    1 - barycentricDividedDifferenceOn s a (fun i =>
        ((n : ℝ) * (1 - t ^ 2) - 2 * ((n : ℝ) - 1) * t * (a i - t) + 2 * (a i - t) ^ 2) *
          truncatedPower n t (a i)) =
      ((1 - 2 * D (s.erase h) (n + 1)) + (1 - 2 * D (s.erase l) (n + 1))) / 2 +
        (n : ℝ) / 2 * ((1 - 2 * D s (n + 2)) - (1 - 2 * D ((s.erase l).erase h) n)) := by
  dsimp only
  rw [barycentric_truncatedPower_erase hinj hh, barycentric_truncatedPower_erase hinj hl,
    barycentric_truncatedPower_erase_endpoints hinj hl hh hlv hhv, hlv, hhv]
  have hweight : barycentricDividedDifferenceOn s a (fun i =>
      ((n : ℝ) * (1 - t ^ 2) - 2 * ((n : ℝ) - 1) * t * (a i - t) + 2 * (a i - t) ^ 2) *
        truncatedPower n t (a i)) =
      (n : ℝ) * (1 - t ^ 2) * barycentricDividedDifferenceOn s a (fun i => truncatedPower n t (a i)) -
        2 * ((n : ℝ) - 1) * t * barycentricDividedDifferenceOn s a (fun i => truncatedPower (n + 1) t (a i)) +
        2 * barycentricDividedDifferenceOn s a (fun i => truncatedPower (n + 2) t (a i)) := by
    simp only [truncatedPower_succ, barycentricDividedDifferenceOn, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hweight]
  ring

end SharpL1.Analysis
