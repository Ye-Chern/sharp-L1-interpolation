import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace SharpL1.Certificate

/-- The scaled sign quantity from a scaled CDF. -/
def cdfToSign (s cdf : ℤ) : ℤ := s - 2 * cdf

/-- Reversing the CDF bounds, including coefficient and rounding uncertainty,
gives bounds on the scaled value of `1 - 2 * F`. -/
theorem cdfToSign_encloses (s lo hi : ℤ) (fl f fu : ℝ) (hs : 0 < s)
    (hfl : fl ≤ f) (hfu : f ≤ fu)
    (hlo : (lo : ℝ) ≤ (s : ℝ) * fl) (hhi : (s : ℝ) * fu ≤ (hi : ℝ)) :
    (cdfToSign s hi : ℝ) ≤ (s : ℝ) * (1 - 2 * f) ∧
      (s : ℝ) * (1 - 2 * f) ≤ (cdfToSign s lo : ℝ) := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hl := hlo.trans (mul_le_mul_of_nonneg_left hfl hs')
  have hu := (mul_le_mul_of_nonneg_left hfu hs').trans hhi
  push_cast [cdfToSign]
  exact ⟨by linarith, by linarith⟩

end SharpL1.Certificate
