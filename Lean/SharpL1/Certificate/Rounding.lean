import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Directed rounding for the mixed-sign CDF step

Child bounds and output bounds are in units of 1/S. The enclosure proofs use
the already scaled children; the conversion back to a CDF uses positive S.
-/

namespace SharpL1.Certificate

def roundDown (v d : ℤ) : ℤ := v / d
def roundUp (v d : ℤ) : ℤ := (v + d - 1) / d
def mixedNumerator (l h x y : ℤ) : ℤ := (-l) * x + h * y
def lowerUpdate (l h x y : ℤ) : ℤ := roundDown (mixedNumerator l h x y) (h - l)
def upperUpdate (l h x y : ℤ) : ℤ := roundUp (mixedNumerator l h x y) (h - l)

noncomputable def scaledAverage (S l h : ℤ) (f g : ℝ) : ℝ :=
  (S : ℝ) * ((-(l : ℝ)) * f + (h : ℝ) * g) / ((h : ℝ) - (l : ℝ))

private theorem floor_div_le_real (v d : ℤ) (hd : 0 < d) :
    ((v / d : ℤ) : ℝ) ≤ (v : ℝ) / (d : ℝ) := by
  have hmul := Int.ediv_mul_le v (ne_of_gt hd)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).2
  exact_mod_cast hmul

private theorem real_div_le_ceil_div (v d : ℤ) (hd : 0 < d) :
    (v : ℝ) / (d : ℝ) ≤ (((v + d - 1) / d : ℤ) : ℝ) := by
  have hdiv := Int.mul_ediv_add_emod (v + d - 1) d
  have hrem0 := Int.emod_nonneg (v + d - 1) (ne_of_gt hd)
  have hrem := Int.emod_lt_of_pos (v + d - 1) hd
  have hcomm : d * ((v + d - 1) / d) = ((v + d - 1) / d) * d := Int.mul_comm _ _
  have hv : v ≤ ((v + d - 1) / d) * d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (div_le_iff₀ hdR).2
  exact_mod_cast hv

theorem lowerUpdate_sound (S l h xlo ylo : ℤ) (f g : ℝ)
    (hl : l < 0) (hh : 0 < h)
    (hxl : (xlo : ℝ) ≤ (S : ℝ) * f) (hyl : (ylo : ℝ) ≤ (S : ℝ) * g) :
    ((lowerUpdate l h xlo ylo : ℤ) : ℝ) ≤ scaledAverage S l h f g := by
  have hd : 0 < h - l := by omega
  have hdR : 0 < ((h - l : ℤ) : ℝ) := by exact_mod_cast hd
  have hwL : 0 ≤ (-(l : ℝ)) := by exact_mod_cast (show 0 ≤ -l by omega)
  have hwH : 0 ≤ (h : ℝ) := by exact_mod_cast (le_of_lt hh)
  have hnum : (mixedNumerator l h xlo ylo : ℝ) ≤
      (S : ℝ) * ((-(l : ℝ)) * f + (h : ℝ) * g) := by
    have a := mul_le_mul_of_nonneg_left hxl hwL
    have b := mul_le_mul_of_nonneg_left hyl hwH
    simp only [mixedNumerator, Int.cast_add, Int.cast_mul, Int.cast_neg] at a b ⊢
    nlinarith
  have hfloor := floor_div_le_real (mixedNumerator l h xlo ylo) (h - l) hd
  have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hdR)
  change ((mixedNumerator l h xlo ylo / (h - l) : ℤ) : ℝ) ≤ _
  exact le_trans hfloor (by simpa [scaledAverage] using hdiv)

theorem upperUpdate_sound (S l h xhi yhi : ℤ) (f g : ℝ)
    (hl : l < 0) (hh : 0 < h)
    (hxh : (S : ℝ) * f ≤ (xhi : ℝ)) (hyh : (S : ℝ) * g ≤ (yhi : ℝ)) :
    scaledAverage S l h f g ≤ ((upperUpdate l h xhi yhi : ℤ) : ℝ) := by
  have hd : 0 < h - l := by omega
  have hdR : 0 < ((h - l : ℤ) : ℝ) := by exact_mod_cast hd
  have hwL : 0 ≤ (-(l : ℝ)) := by exact_mod_cast (show 0 ≤ -l by omega)
  have hwH : 0 ≤ (h : ℝ) := by exact_mod_cast (le_of_lt hh)
  have hnum : (S : ℝ) * ((-(l : ℝ)) * f + (h : ℝ) * g) ≤
      (mixedNumerator l h xhi yhi : ℝ) := by
    have a := mul_le_mul_of_nonneg_left hxh hwL
    have b := mul_le_mul_of_nonneg_left hyh hwH
    simp only [mixedNumerator, Int.cast_add, Int.cast_mul, Int.cast_neg] at a b ⊢
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hdR)
  have hceil := real_div_le_ceil_div (mixedNumerator l h xhi yhi) (h - l) hd
  change _ ≤ (((mixedNumerator l h xhi yhi + (h - l) - 1) / (h - l) : ℤ) : ℝ)
  exact le_trans (by simpa [scaledAverage] using hdiv) hceil

end SharpL1.Certificate
