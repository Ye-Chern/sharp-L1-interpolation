import SharpL1.Certificate.CDFSemantics
import SharpL1.Certificate.CDFSigns
import SharpL1.Probability.WeightedComparison

/-! ## Real sign bounds from scaled integer coefficients -/

namespace SharpL1.Certificate

open SharpL1.Probability

/-- Interpret grid coefficients at scale `s` as real coefficients. -/
noncomputable def realCoefficients (s : ℤ) (knots : List ℤ) : List ℝ :=
  knots.map fun k : ℤ => (k : ℝ) / (s : ℝ)

private theorem weightedCdfZero_realCoefficients (s : ℤ) (hs : 0 < s) (knots : List ℤ) :
    weightedCdfZero (realCoefficients s knots) =
      weightedCdfZero (knots.map fun k : ℤ => (k : ℝ)) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hmap : realCoefficients s knots =
      (knots.map fun k : ℤ => (k : ℝ)).map (fun c => (s : ℝ)⁻¹ * c) := by
    rw [realCoefficients, List.map_map]
    congr 1
    funext k
    simp only [Function.comp_apply, div_eq_mul_inv, mul_comm ((s : ℝ)⁻¹)]
  rw [hmap, weightedCdfZero_map_pos _ (inv_pos.mpr hs')]

/-- Directed rounding and coefficient enclosures give bounds on the actual
sign expectation using the two ordered grid lists. -/
theorem cdfSign_encloses_weightedLaw (s : ℤ) (hs : 0 < s) (lower upper : List ℤ)
    (cs : List ℝ) (hl : List.Forall₂ (· ≤ ·) (realCoefficients s lower) cs)
    (hu : List.Forall₂ (· ≤ ·) cs (realCoefficients s upper)) (hnz : ∃ c ∈ cs, c ≠ 0)
    (hln : lower ≠ []) (hlo : lower.Pairwise (· ≤ ·))
    (hun : upper ≠ []) (huo : upper.Pairwise (· ≤ ·)) :
    (cdfToSign s (cdfUpper s lower) : ℝ) ≤ (s : ℝ) * lawSignMean (weightedExpSum cs) ∧
      (s : ℝ) * lawSignMean (weightedExpSum cs) ≤ (cdfToSign s (cdfLower s upper) : ℝ) := by
  have hfl : cdfExact upper ≤ weightedCdfZero cs := by
    rw [cdfExact_eq_weightedCdfZero upper hun huo, ← weightedCdfZero_realCoefficients s hs upper]
    exact weightedCdfZero_antitone hu
  have hfu : weightedCdfZero cs ≤ cdfExact lower := by
    rw [cdfExact_eq_weightedCdfZero lower hln hlo, ← weightedCdfZero_realCoefficients s hs lower]
    exact weightedCdfZero_antitone hl
  rw [weightedExpSum_signMean hnz]
  exact cdfToSign_encloses s (cdfLower s upper) (cdfUpper s lower)
    (cdfExact upper) (weightedCdfZero cs) (cdfExact lower) hs hfl hfu
    (cdfLower_sound s upper) (cdfUpper_sound s lower)

end SharpL1.Certificate
