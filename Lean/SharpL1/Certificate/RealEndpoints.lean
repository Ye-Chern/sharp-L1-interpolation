module

public import SharpL1.Certificate.CDFBridge
public import SharpL1.Certificate.DerivativeBridge
public import Mathlib.Data.List.Forall2

public section

/-! ## Coefficient enclosures derived from the actual bracket rows -/

namespace SharpL1.Certificate

open SharpL1.Probability

/-- The real coefficients use the same descending order of roots as the CSV. -/
@[expose] noncomputable def coreCoefficients {m : ℕ} (row : Row) (roots : Fin m → ℝ) : List ℝ :=
  List.ofFn fun i => parameter row.t - roots i

/-- A checked row supplies ordered integer lists and positionwise enclosures
of the actual core coefficients. The certified roots exhaust the polynomial. -/
theorem checkRootRow_core_enclosure (k : ℕ) (row : Row)
    (hcheck : checkRootRow gridScale row.t k row.brackets = true) :
    ∃ roots : Fin (k + 2) → ℝ,
      StrictAnti roots ∧
      (nodePolynomial k (parameter row.t)).roots = (Finset.univ.image roots).val ∧
      (coefficientLower row).Pairwise (· ≤ ·) ∧ (coefficientUpper row).Pairwise (· ≤ ·) ∧
      List.Forall₂ (· ≤ ·) (realCoefficients gridScale (coefficientLower row))
        (coreCoefficients row roots) ∧
      List.Forall₂ (· ≤ ·) (coreCoefficients row roots)
        (realCoefficients gridScale (coefficientUpper row)) := by
  obtain ⟨roots, hrange, hanti, hroot⟩ := checkRootRow_sound _ _ _ _ hcheck
  simp only [checkRootRow, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcheck
  obtain ⟨⟨⟨_, hlen⟩, hvalid⟩, hsep⟩ := hcheck
  have hget (i : Fin (k + 2)) : rowBracket row.brackets i.val =
      row.brackets[i.val]'(by simpa only [hlen] using i.isLt) := by
    simp [rowBracket, show i.val < row.brackets.length by simpa only [hlen] using i.isLt]
  refine ⟨roots, hanti, hroot, ?_, ?_, ?_, ?_⟩
  · rw [coefficientLower, List.pairwise_map]
    refine hsep.imp_of_mem ?_
    intro a b ha _ hab
    have hv := hvalid a ha
    exact sub_le_sub_left (hab.le.trans hv.2.1.le) _
  · rw [coefficientUpper, List.pairwise_map]
    refine hsep.imp_of_mem ?_
    intro a b _ hb hab
    have hv := hvalid b hb
    exact sub_le_sub_left (hv.2.1.le.trans hab.le) _
  · refine List.forall₂_iff_get.mpr ⟨by simp [realCoefficients, coefficientLower, coreCoefficients, hlen], ?_⟩
    intro i _ hi
    have hi' : i < k + 2 := by simpa only [coreCoefficients, List.length_ofFn] using hi
    have hright := (hrange ⟨i, hi'⟩).2.1.le
    rw [hget] at hright
    simpa only [realCoefficients, coefficientLower, coreCoefficients, parameter,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, Int.cast_sub, sub_div] using
      sub_le_sub_left hright ((row.t : ℝ) / gridScale)
  · refine List.forall₂_iff_get.mpr ⟨by simp [realCoefficients, coefficientUpper, coreCoefficients, hlen], ?_⟩
    intro i hi _
    have hi' : i < k + 2 := by simpa only [coreCoefficients, List.length_ofFn] using hi
    have hleft := (hrange ⟨i, hi'⟩).1.le
    rw [hget] at hleft
    simpa only [realCoefficients, coefficientUpper, coreCoefficients, parameter,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn, Int.cast_sub, sub_div] using
      sub_le_sub_left hleft ((row.t : ℝ) / gridScale)

/-- For the core list, a valid bracket row bounds the sign mean of the true
weighted law. Distinctness of the roots guarantees a nonzero coefficient. -/
theorem checkRootRow_core_sign (k : ℕ) (row : Row)
    (hcheck : checkRootRow gridScale row.t k row.brackets = true) :
    ∃ roots : Fin (k + 2) → ℝ,
      StrictAnti roots ∧
      (nodePolynomial k (parameter row.t)).roots = (Finset.univ.image roots).val ∧
      ((evaluate row).lower.core : ℝ) ≤
        (gridScale : ℝ) * lawSignMean (weightedExpSum (coreCoefficients row roots)) ∧
      (gridScale : ℝ) * lawSignMean (weightedExpSum (coreCoefficients row roots)) ≤
        ((evaluate row).upper.core : ℝ) := by
  obtain ⟨roots, hanti, hroot, hlo, huo, hl, hu⟩ := checkRootRow_core_enclosure k row hcheck
  have hmem (i : Fin (k + 2)) : parameter row.t - roots i ∈ coreCoefficients row roots := by
    simp only [coreCoefficients, List.mem_ofFn]
    exact ⟨i, rfl⟩
  have hnz : ∃ c ∈ coreCoefficients row roots, c ≠ 0 := by
    by_contra! h
    let i : Fin (k + 2) := ⟨0, by omega⟩
    let j : Fin (k + 2) := ⟨1, by omega⟩
    have hij : i < j := Nat.zero_lt_one
    linarith [hanti hij, h _ (hmem i), h _ (hmem j)]
  have hln : coefficientLower row ≠ [] := by
    intro h
    have hh := hl.length_eq
    simp [realCoefficients, h, coreCoefficients] at hh
  have hun : coefficientUpper row ≠ [] := by
    intro h
    have hh := hu.length_eq
    simp [realCoefficients, h, coreCoefficients] at hh
  refine ⟨roots, hanti, hroot, ?_⟩
  exact cdfSign_encloses_weightedLaw gridScale (by decide) (coefficientLower row)
    (coefficientUpper row) (coreCoefficients row roots) hl hu hnz hln hlo hun huo

end SharpL1.Certificate
