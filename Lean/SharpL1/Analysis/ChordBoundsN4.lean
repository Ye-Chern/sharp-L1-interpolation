import SharpL1.Analysis.ChordIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative Analytic Bounds on the Vertical-Chord Integral (`n ≥ 4`)

This file formalizes Section 6 and Appendix B.1 of `chebyshev_L1_complete.tex`:
proving strict positivity of the vertical-chord integral
`chordDeltaIntegral n t` for all `n ≥ 4` and all `t ∈ (0, 1/2]`.

It also exposes the reusable pointwise chord-integrand lower bound and
main/remainder decomposition for `n ≥ 2` so `LowOrderMono.lean` can reuse
them for `n = 3`.
-/

namespace SharpL1.Analysis

open scoped BigOperators
open Set intervalIntegral
open MeasureTheory (volume IntegrableOn AEStronglyMeasurable Ico_ae_eq_Ioc)

/-! ### Vertical-chord integrand and elementary algebraic identities -/

/-- Blaschke factor `φ_t(u) = (u - t) / (1 - t u)`. -/
noncomputable def chordBlaschke (t : ℝ) (u : ℂ) : ℂ :=
  (u - (t : ℂ)) / (1 - (t : ℂ) * u)

/-- Vertical-chord integrand `(1 - t^2 - v^2)^n * Re(-φ_t(t+iv) / (1 - (t+iv)^(2n+2) φ_t(t+iv)^2))`. -/
noncomputable def chordIntegrand (n : ℕ) (t v : ℝ) : ℝ :=
  (1 - t ^ 2 - v ^ 2) ^ n *
    ((-(chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I))) /
      (1 - ((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
        (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2)).re

/-- Vertical-chord integral `(8 / π) ∫_0^√(1 - t^2) chordIntegrand n t v dv`. -/
noncomputable def chordDeltaIntegral (n : ℕ) (t : ℝ) : ℝ :=
  (8 / Real.pi) * ∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), chordIntegrand n t v

/-- `D(t, v) = (1 - t^2)^2 + t^2 v^2 = 1 - (2 - (t^2 + v^2)) t^2`. -/
def chordD (t v : ℝ) : ℝ :=
  (1 - t ^ 2) ^ 2 + t ^ 2 * v ^ 2

/-- `x(t, v) = t^2 + v^2`. -/
def chordX (t v : ℝ) : ℝ :=
  t ^ 2 + v ^ 2

theorem chordD_eq (t v : ℝ) :
    chordD t v = 1 - (2 - chordX t v) * t ^ 2 := by
  unfold chordD chordX
  ring

theorem chordD_pos {t : ℝ} (ht1 : t < 1) (ht0 : -1 < t) (v : ℝ) :
    0 < chordD t v := by
  unfold chordD
  have ha2 : 0 < 1 - t ^ 2 := by nlinarith
  positivity

theorem chordX_sub_sq_div_chordD {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (v : ℝ) :
    chordX t v - v ^ 2 / chordD t v =
      t ^ 2 * (1 - chordX t v) ^ 2 / chordD t v := by
  have hD : chordD t v ≠ 0 := (chordD_pos ht1 ht0 v).ne'
  field_simp [hD]
  unfold chordD chordX
  ring

theorem sq_div_chordD_le_chordX {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (v : ℝ) :
    v ^ 2 / chordD t v ≤ chordX t v := by
  have hD : 0 < chordD t v := chordD_pos ht1 ht0 v
  have hdiff := chordX_sub_sq_div_chordD ht0 ht1 v
  have hnonneg : 0 ≤ t ^ 2 * (1 - chordX t v) ^ 2 / chordD t v := by positivity
  linarith

theorem chordX_lt_one {t v : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hv0 : 0 ≤ v) (hva : v < Real.sqrt (1 - t ^ 2)) :
    chordX t v < 1 := by
  have ha2 : 0 < 1 - t ^ 2 := by nlinarith
  have hv2 : v ^ 2 < 1 - t ^ 2 := by
    calc
      v ^ 2 < (Real.sqrt (1 - t ^ 2)) ^ 2 := by nlinarith [Real.sqrt_pos.mpr ha2]
      _ = 1 - t ^ 2 := Real.sq_sqrt ha2.le
  unfold chordX
  linarith

theorem one_sub_chordX_eq (t v : ℝ) :
    1 - chordX t v = 1 - t ^ 2 - v ^ 2 := by
  unfold chordX
  ring

/-! ### Complex identities on the vertical chord `u = t + i v` -/

private theorem normSq_one_sub_mul_u (t v : ℝ) :
    Complex.normSq (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) = chordD t v := by
  have h : (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) =
      (((1 - t ^ 2 : ℝ) : ℂ) + ((-(t * v) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.normSq_add_mul_I]
  unfold chordD
  ring

private theorem norm_one_sub_mul_u_sq (t v : ℝ) :
    ‖1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 = chordD t v := by
  rw [← Complex.normSq_eq_norm_sq, normSq_one_sub_mul_u]

private theorem one_sub_mul_u_ne_zero {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (v : ℝ) :
    (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) ≠ 0 := by
  intro h
  have hns : Complex.normSq (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) = 0 := by
    simp [h]
  rw [normSq_one_sub_mul_u] at hns
  linarith [chordD_pos ht1 ht0 v]

private theorem neg_chordBlaschke_eq {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (v : ℝ) :
    -(chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) =
      (((t * v ^ 2 / chordD t v : ℝ) : ℂ) +
        (((-(1 - t ^ 2) * v / chordD t v : ℝ) : ℂ) * Complex.I)) := by
  have hD : chordD t v ≠ 0 := (chordD_pos ht1 ht0 v).ne'
  have hne : (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) ≠ 0 :=
    one_sub_mul_u_ne_zero ht0 ht1 v
  have hneg : -(chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) =
      -((v : ℂ) * Complex.I) / (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) := by
    unfold chordBlaschke
    ring
  rw [hneg]
  have hconj :
      (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) *
        (((1 - t ^ 2 : ℝ) : ℂ) + (((t * v : ℝ) : ℂ) * Complex.I)) = (chordD t v : ℂ) := by
    unfold chordD
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hinv : (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I))⁻¹ =
      (((1 - t ^ 2 : ℝ) : ℂ) + (((t * v : ℝ) : ℂ) * Complex.I)) / (chordD t v : ℂ) := by
    rw [eq_div_iff (by exact_mod_cast hD)]
    calc
      (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I))⁻¹ * (chordD t v : ℂ)
          = (1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I))⁻¹ *
              ((1 - (t : ℂ) * ((t : ℂ) + (v : ℂ) * Complex.I)) *
                (((1 - t ^ 2 : ℝ) : ℂ) + (((t * v : ℝ) : ℂ) * Complex.I))) := by
              rw [hconj]
      _ = (((1 - t ^ 2 : ℝ) : ℂ) + (((t * v : ℝ) : ℂ) * Complex.I)) := by
              rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [div_eq_mul_inv, hinv]
  have hDc : (chordD t v : ℂ) ≠ 0 := by exact_mod_cast hD
  push_cast
  field_simp [hDc]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem neg_chordBlaschke_re {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (v : ℝ) :
    (-(chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I))).re = t * v ^ 2 / chordD t v := by
  rw [neg_chordBlaschke_eq ht0 ht1 v]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]

theorem neg_chordBlaschke_im {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (v : ℝ) :
    (-(chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I))).im = -(1 - t ^ 2) * v / chordD t v := by
  rw [neg_chordBlaschke_eq ht0 ht1 v]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.I_re, mul_zero, add_zero, zero_add]

theorem norm_chordBlaschke_sq (t v : ℝ) :
    ‖chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 = v ^ 2 / chordD t v := by
  unfold chordBlaschke
  rw [norm_div, div_pow, norm_one_sub_mul_u_sq]
  have hnum : ((t : ℂ) + (v : ℂ) * Complex.I - (t : ℂ)) = (v : ℂ) * Complex.I := by ring
  rw [hnum, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_chord_u_sq (t v : ℝ) :
    ‖(t : ℂ) + (v : ℂ) * Complex.I‖ ^ 2 = chordX t v := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  unfold chordX
  ring

theorem norm_reflection_z_eq (t : ℝ) (n : ℕ) (v : ℝ) :
    ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
        (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖ =
      (chordX t v) ^ (n + 1) * (v ^ 2 / chordD t v) := by
  rw [norm_mul, norm_pow, norm_pow]
  have hpow : ‖(t : ℂ) + (v : ℂ) * Complex.I‖ ^ (2 * n + 2) =
      (‖(t : ℂ) + (v : ℂ) * Complex.I‖ ^ 2) ^ (n + 1) := by
    rw [← pow_mul]
    ring_nf
  rw [hpow, norm_chord_u_sq, norm_chordBlaschke_sq]

theorem norm_reflection_z_le {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (n : ℕ) (v : ℝ) :
    ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
        (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖ ≤
      (chordX t v) ^ (n + 2) := by
  rw [norm_reflection_z_eq t n v]
  have hx : 0 ≤ chordX t v := by unfold chordX; positivity
  calc
    (chordX t v) ^ (n + 1) * (v ^ 2 / chordD t v)
        ≤ (chordX t v) ^ (n + 1) * chordX t v := by
          gcongr
          exact sq_div_chordD_le_chordX ht0 ht1 v
    _ = (chordX t v) ^ (n + 2) := by ring

/-! ### Real-part and phase/argument bounds -/

theorem abs_re_mul_div_one_sub_le (w z : ℂ) (hz : ‖z‖ < 1) :
    |(w * (z / (1 - z))).re| ≤
      |w.re| * (‖z‖ / (1 - ‖z‖)) + |w.im| * (|z.im| / (1 - ‖z‖) ^ 2) := by
  have h1z_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have h1z_ne : (1 - z) ≠ 0 := by
    intro h
    have : ‖z‖ = 1 := by
      have hz1 : z = 1 := (sub_eq_zero.mp h).symm
      simp [hz1]
    linarith
  have hrev : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) z
  have hnorm_div : |(z / (1 - z)).re| ≤ ‖z‖ / (1 - ‖z‖) := by
    calc
      |(z / (1 - z)).re| ≤ ‖z / (1 - z)‖ := Complex.abs_re_le_norm _
      _ = ‖z‖ / ‖1 - z‖ := norm_div z (1 - z)
      _ ≤ ‖z‖ / (1 - ‖z‖) := by gcongr
  have him_div : |(z / (1 - z)).im| ≤ |z.im| / (1 - ‖z‖) ^ 2 := by
    have him_eq : (z / (1 - z)).im = z.im / ‖1 - z‖ ^ 2 := by
      rw [div_eq_mul_inv, Complex.inv_def, ← Complex.normSq_eq_norm_sq]
      simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [him_eq, abs_div, abs_of_nonneg (sq_nonneg ‖1 - z‖)]
    have hsq : (1 - ‖z‖) ^ 2 ≤ ‖1 - z‖ ^ 2 := by nlinarith
    gcongr
  rw [Complex.mul_re]
  calc
    |w.re * (z / (1 - z)).re - w.im * (z / (1 - z)).im|
        ≤ |w.re * (z / (1 - z)).re| + |w.im * (z / (1 - z)).im| := abs_sub _ _
    _ = |w.re| * |(z / (1 - z)).re| + |w.im| * |(z / (1 - z)).im| := by
          rw [abs_mul, abs_mul]
    _ ≤ |w.re| * (‖z‖ / (1 - ‖z‖)) + |w.im| * (|z.im| / (1 - ‖z‖) ^ 2) := by
          gcongr

private theorem arctan_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  let g : ℝ → ℝ := fun x => x - Real.arctan x
  have hg_deriv : ∀ x : ℝ, HasDerivAt g (1 - 1 / (1 + x ^ 2)) x := fun x =>
    (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
  have hg_mono : Monotone g := by
    apply monotone_of_deriv_nonneg (fun x => (hg_deriv x).differentiableAt)
    intro x
    rw [(hg_deriv x).deriv]
    have h1 : (1 : ℝ) ≤ 1 + x ^ 2 := by linarith [sq_nonneg x]
    have h2 : 1 / (1 + x ^ 2) ≤ 1 := div_le_one_of_le₀ h1 (by positivity)
    linarith
  have h0 : g 0 ≤ g y := hg_mono hy
  dsimp [g] at h0
  simp only [Real.arctan_zero, sub_zero] at h0
  linarith

private theorem abs_sin_le_abs_self (ψ : ℝ) : |Real.sin ψ| ≤ |ψ| := by
  simpa using Real.abs_sin_sub_sin_le ψ 0

private theorem polar_u_eq {t v : ℝ} (ht : 0 < t) (hv : 0 < v) :
    ((t : ℂ) + (v : ℂ) * Complex.I) =
      Complex.I * (‖(t : ℂ) + (v : ℂ) * Complex.I‖ : ℂ) *
        Complex.exp (-((Real.arctan (t / v) : ℝ) : ℂ) * Complex.I) := by
  let u : ℂ := (t : ℂ) + (v : ℂ) * Complex.I
  let θ₁ : ℝ := Real.arctan (t / v)
  have hu_pos : 0 < ‖u‖ := by
    rw [norm_pos_iff]
    intro h
    have him : u.im = 0 := by simp [h]
    simp [u] at him
    linarith
  have hnorm_eq : ‖u‖ = Real.sqrt (t ^ 2 + v ^ 2) := by
    rw [← Real.sqrt_sq hu_pos.le, norm_chord_u_sq]
    rfl
  have h1tv : 1 + (t / v) ^ 2 = (t ^ 2 + v ^ 2) / v ^ 2 := by
    field_simp [hv.ne']
    ring
  have hsqrt_1tv : Real.sqrt (1 + (t / v) ^ 2) = ‖u‖ / v := by
    rw [h1tv, Real.sqrt_div (by positivity), Real.sqrt_sq hv.le, hnorm_eq]
  have hcos : Real.cos θ₁ = v / ‖u‖ := by
    rw [Real.cos_arctan, hsqrt_1tv, one_div_div]
  have hsin : Real.sin θ₁ = t / ‖u‖ := by
    rw [Real.sin_arctan, hsqrt_1tv]
    field_simp [hv.ne', hu_pos.ne']
  have hexp : Complex.exp (-(θ₁ : ℂ) * Complex.I) =
      ((Real.cos θ₁ : ℝ) : ℂ) - ((Real.sin θ₁ : ℝ) : ℂ) * Complex.I := by
    have h1 : -(θ₁ : ℂ) * Complex.I = ((-θ₁ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  change u = Complex.I * (‖u‖ : ℂ) * Complex.exp (-(θ₁ : ℂ) * Complex.I)
  rw [hexp, hcos, hsin]
  have huc : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hu_pos.ne'
  dsimp [u]
  push_cast
  have h1 : (‖u‖ : ℂ) * ((v : ℂ) / (‖u‖ : ℂ)) = (v : ℂ) := mul_div_cancel₀ _ huc
  have h2 : (‖u‖ : ℂ) * ((t : ℂ) / (‖u‖ : ℂ)) = (t : ℂ) := mul_div_cancel₀ _ huc
  calc
    (t : ℂ) + (v : ℂ) * Complex.I
        = (‖u‖ : ℂ) * ((t : ℂ) / (‖u‖ : ℂ)) + (‖u‖ : ℂ) * ((v : ℂ) / (‖u‖ : ℂ)) * Complex.I := by
            rw [h1, h2]
    _ = Complex.I * (‖u‖ : ℂ) * ((v : ℂ) / (‖u‖ : ℂ) - (t : ℂ) / (‖u‖ : ℂ) * Complex.I) := by
            ring_nf
            simp only [Complex.I_sq]
            ring

private theorem polar_phi_eq {t v : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (hv : 0 < v) :
    chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I) =
      Complex.I * (‖chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)‖ : ℂ) *
        Complex.exp (((Real.arctan (t * v / (1 - t ^ 2)) : ℝ) : ℂ) * Complex.I) := by
  let a2 : ℝ := 1 - t ^ 2
  have ha2 : 0 < a2 := by dsimp [a2]; nlinarith
  let D : ℝ := chordD t v
  have hD : 0 < D := chordD_pos ht1 ht0 v
  let φ : ℂ := chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)
  let θ₂ : ℝ := Real.arctan (t * v / a2)
  have hnorm_sq : ‖φ‖ ^ 2 = v ^ 2 / D := norm_chordBlaschke_sq t v
  have hnorm_eq : ‖φ‖ = v / Real.sqrt D := by
    rw [← Real.sqrt_sq (norm_nonneg φ), hnorm_sq, Real.sqrt_div (sq_nonneg v), Real.sqrt_sq hv.le]
  have h1tv : 1 + (t * v / a2) ^ 2 = D / a2 ^ 2 := by
    have ha2_eq : a2 = 1 - t ^ 2 := rfl
    have hD_eq : D = a2 ^ 2 + t ^ 2 * v ^ 2 := by unfold D chordD; rw [ha2_eq]
    rw [hD_eq]
    field_simp [ha2.ne']
  have hsqrt_1tv : Real.sqrt (1 + (t * v / a2) ^ 2) = Real.sqrt D / a2 := by
    rw [h1tv, Real.sqrt_div hD.le, Real.sqrt_sq ha2.le]
  have hcos : Real.cos θ₂ = a2 / Real.sqrt D := by
    rw [Real.cos_arctan, hsqrt_1tv, one_div_div]
  have hsin : Real.sin θ₂ = t * v / Real.sqrt D := by
    rw [Real.sin_arctan, hsqrt_1tv]
    field_simp [ha2.ne']
  have hexp : Complex.exp ((θ₂ : ℂ) * Complex.I) =
      ((Real.cos θ₂ : ℝ) : ℂ) + ((Real.sin θ₂ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hphi_neg : φ = -(-(φ)) := by ring
  have hphi_eq : φ = (((-(t * v ^ 2) / D : ℝ) : ℂ) + (((a2 * v / D : ℝ) : ℂ) * Complex.I)) := by
    rw [hphi_neg, neg_chordBlaschke_eq ht0 ht1 v]
    dsimp [a2, D]
    push_cast
    ring
  change φ = Complex.I * (‖φ‖ : ℂ) * Complex.exp ((θ₂ : ℂ) * Complex.I)
  nth_rw 1 [hphi_eq]
  rw [hexp, hnorm_eq, hcos, hsin]
  have hsqrtD_sq : (Real.sqrt D : ℂ) ^ 2 = (D : ℂ) := by
    have h := Real.sq_sqrt hD.le
    exact_mod_cast h
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsDc : (Real.sqrt D : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  push_cast
  field_simp [hDc, hsDc]
  ring_nf
  simp only [Complex.I_sq, hsqrtD_sq]
  ring

theorem abs_reflection_z_im_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ)
    {v : ℝ} (hv0 : 0 < v) (hva : v < Real.sqrt (1 - t ^ 2)) :
    |(((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
        (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2).im| ≤
      ((2 * (n : ℝ) + 2) * t / v) *
        ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
          (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖ := by
  let u : ℂ := (t : ℂ) + (v : ℂ) * Complex.I
  let φ : ℂ := chordBlaschke t u
  let z : ℂ := u ^ (2 * n + 2) * φ ^ 2
  let θ₁ : ℝ := Real.arctan (t / v)
  let θ₂ : ℝ := Real.arctan (t * v / (1 - t ^ 2))
  let ψ : ℝ := 2 * θ₂ - (2 * (n : ℝ) + 2) * θ₁
  have ht_m1 : -1 < t := by linarith
  have hu_polar := polar_u_eq ht0 hv0
  have hphi_polar := polar_phi_eq ht_m1 ht1 hv0
  have hpow_u : u ^ (2 * n + 2) =
      Complex.I ^ (2 * n + 2) * (‖u‖ ^ (2 * n + 2) : ℂ) *
        Complex.exp (-((2 * (n : ℝ) + 2) * θ₁ : ℂ) * Complex.I) := by
    calc
      u ^ (2 * n + 2)
          = (Complex.I * (‖u‖ : ℂ) * Complex.exp (-(θ₁ : ℂ) * Complex.I)) ^ (2 * n + 2) := by
              exact congrArg (· ^ (2 * n + 2)) hu_polar
      _ = Complex.I ^ (2 * n + 2) * (‖u‖ : ℂ) ^ (2 * n + 2) *
            (Complex.exp (-(θ₁ : ℂ) * Complex.I)) ^ (2 * n + 2) := by ring
      _ = Complex.I ^ (2 * n + 2) * (‖u‖ ^ (2 * n + 2) : ℂ) *
            Complex.exp (((2 * n + 2 : ℕ) : ℂ) * (-(θ₁ : ℂ) * Complex.I)) := by
              rw [← Complex.exp_nat_mul]
      _ = Complex.I ^ (2 * n + 2) * (‖u‖ ^ (2 * n + 2) : ℂ) *
            Complex.exp (-((2 * (n : ℝ) + 2) * θ₁ : ℂ) * Complex.I) := by
              push_cast
              ring_nf
  have hpow_phi : φ ^ 2 =
      Complex.I ^ 2 * (‖φ‖ ^ 2 : ℂ) * Complex.exp ((2 * θ₂ : ℂ) * Complex.I) := by
    calc
      φ ^ 2 = (Complex.I * (‖φ‖ : ℂ) * Complex.exp ((θ₂ : ℂ) * Complex.I)) ^ 2 := by
              exact congrArg (· ^ 2) hphi_polar
      _ = Complex.I ^ 2 * (‖φ‖ : ℂ) ^ 2 * (Complex.exp ((θ₂ : ℂ) * Complex.I)) ^ 2 := by ring
      _ = Complex.I ^ 2 * (‖φ‖ ^ 2 : ℂ) *
            Complex.exp ((2 : ℕ) * ((θ₂ : ℂ) * Complex.I)) := by
              rw [← Complex.exp_nat_mul]
      _ = Complex.I ^ 2 * (‖φ‖ ^ 2 : ℂ) * Complex.exp ((2 * θ₂ : ℂ) * Complex.I) := by
              push_cast
              ring_nf
  have hI_pow : Complex.I ^ (2 * n + 2) * Complex.I ^ 2 = ((-1 : ℝ) ^ (n + 2) : ℂ) := by
    calc
      Complex.I ^ (2 * n + 2) * Complex.I ^ 2 = (Complex.I ^ 2) ^ (n + 2) := by
        rw [← pow_add, ← pow_mul]
        ring_nf
      _ = ((-1 : ℂ)) ^ (n + 2) := by rw [Complex.I_sq]
      _ = ((-1 : ℝ) ^ (n + 2) : ℂ) := by push_cast; rfl
  have hnorm_z : ‖z‖ = ‖u‖ ^ (2 * n + 2) * ‖φ‖ ^ 2 := by
    dsimp [z]
    rw [norm_mul, norm_pow, norm_pow]
  have hz_polar : z = (((-1 : ℝ) ^ (n + 2) * ‖z‖ : ℝ) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := by
    calc
      z = u ^ (2 * n + 2) * φ ^ 2 := rfl
      _ = Complex.I ^ (2 * n + 2) * (‖u‖ ^ (2 * n + 2) : ℂ) *
            Complex.exp (-((2 * (n : ℝ) + 2) * θ₁ : ℂ) * Complex.I) *
            (Complex.I ^ 2 * (‖φ‖ ^ 2 : ℂ) * Complex.exp ((2 * θ₂ : ℂ) * Complex.I)) := by
              rw [hpow_u, hpow_phi]
      _ = (Complex.I ^ (2 * n + 2) * Complex.I ^ 2) *
              ((‖u‖ ^ (2 * n + 2) : ℂ) * (‖φ‖ ^ 2 : ℂ)) *
              (Complex.exp ((2 * θ₂ : ℂ) * Complex.I) *
                Complex.exp (-((2 * (n : ℝ) + 2) * θ₁ : ℂ) * Complex.I)) := by ring
      _ = (((-1 : ℝ) ^ (n + 2) * ‖z‖ : ℝ) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := by
              rw [hI_pow, ← Complex.exp_add]
              push_cast
              rw [hnorm_z]
              dsimp [ψ]
              push_cast
              ring_nf
  have hz_im : z.im = (-1 : ℝ) ^ (n + 2) * ‖z‖ * Real.sin ψ := by
    nth_rw 1 [hz_polar]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, zero_add]
  have ha2 : 0 < 1 - t ^ 2 := by nlinarith
  have hv2_le_a2 : v ^ 2 ≤ 1 - t ^ 2 := by
    have hlt : v ^ 2 < (Real.sqrt (1 - t ^ 2)) ^ 2 := by nlinarith
    rw [Real.sq_sqrt ha2.le] at hlt
    exact hlt.le
  have hv_div_a2 : v / (1 - t ^ 2) ≤ 1 / v := by
    rw [div_le_div_iff₀ ha2 hv0]
    nlinarith
  have hθ₁_pos : 0 ≤ θ₁ := Real.arctan_nonneg.mpr (by positivity)
  have hθ₂_pos : 0 ≤ θ₂ := Real.arctan_nonneg.mpr (by positivity)
  have hθ₁_le : θ₁ ≤ t / v := arctan_le_self_of_nonneg (by positivity)
  have hθ₂_le : θ₂ ≤ t / v := by
    calc
      θ₂ ≤ t * v / (1 - t ^ 2) := arctan_le_self_of_nonneg (by positivity)
      _ = t * (v / (1 - t ^ 2)) := by ring
      _ ≤ t * (1 / v) := by gcongr
      _ = t / v := by ring
  have hψ_abs : |ψ| ≤ (2 * (n : ℝ) + 2) * t / v := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmul_eq : (2 * (n : ℝ) + 2) * (t / v) = (2 * (n : ℝ) + 2) * t / v := by ring
    have hupper : ψ ≤ (2 * (n : ℝ) + 2) * t / v := by
      dsimp [ψ]
      have h2t : 2 * θ₂ ≤ 2 * (t / v) := by linarith
      have hnt : 2 * (t / v) ≤ (2 * (n : ℝ) + 2) * (t / v) := by
        nlinarith [show (0 : ℝ) ≤ t / v by positivity]
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (n : ℝ) + 2) hθ₁_pos]
    have hlower : -((2 * (n : ℝ) + 2) * t / v) ≤ ψ := by
      dsimp [ψ]
      have h1 : (2 * (n : ℝ) + 2) * θ₁ ≤ (2 * (n : ℝ) + 2) * (t / v) := by gcongr
      linarith
    exact abs_le.mpr ⟨hlower, hupper⟩
  calc
    |z.im| = |(-1 : ℝ) ^ (n + 2) * ‖z‖ * Real.sin ψ| := by rw [hz_im]
    _ = ‖z‖ * |Real.sin ψ| := by
          rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (norm_nonneg z)]
    _ ≤ ‖z‖ * |ψ| := mul_le_mul_of_nonneg_left (abs_sin_le_abs_self ψ) (norm_nonneg z)
    _ ≤ ‖z‖ * ((2 * (n : ℝ) + 2) * t / v) := mul_le_mul_of_nonneg_left hψ_abs (norm_nonneg z)
    _ = ((2 * (n : ℝ) + 2) * t / v) * ‖z‖ := by ring

/-- Pointwise lower bound on `chordIntegrand n t v` for `t ∈ (0, 1)` and `v ∈ (0, √(1 - t^2))`.
Shared by both `n ≥ 4` and `n = 3`. -/
theorem chordIntegrand_ge (n : ℕ) {t v : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hv0 : 0 < v) (hva : v < Real.sqrt (1 - t ^ 2)) :
    let x := chordX t v
    let D := chordD t v
    let zNorm := ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
      (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖
    t * ((1 - x) ^ n * (v ^ 2 / D) -
      (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm)) -
      (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) ≤
      chordIntegrand n t v := by
  intro x D zNorm
  have ht_m1 : -1 < t := by linarith
  let u : ℂ := (t : ℂ) + (v : ℂ) * Complex.I
  let φ : ℂ := chordBlaschke t u
  let z : ℂ := u ^ (2 * n + 2) * φ ^ 2
  let w : ℂ := -φ
  have hx_lt : x < 1 := chordX_lt_one ht0.le ht1 hv0.le hva
  have hx_nonneg : 0 ≤ x := by dsimp [x, chordX]; positivity
  have hz_le_x : zNorm ≤ x ^ (n + 2) := norm_reflection_z_le ht_m1 ht1 n v
  have hz_lt_one : zNorm < 1 := by
    calc
      zNorm ≤ x ^ (n + 2) := hz_le_x
      _ < 1 := pow_lt_one₀ hx_nonneg hx_lt (by omega)
  have h1z_ne : (1 - z) ≠ 0 := by
    intro h
    have : ‖z‖ = 1 := by
      have hz1 : z = 1 := (sub_eq_zero.mp h).symm
      simp [hz1]
    linarith
  have hsplit : w / (1 - z) = w + w * (z / (1 - z)) := by
    field_simp [h1z_ne]
    ring
  have hre_split : (w / (1 - z)).re = w.re + (w * (z / (1 - z))).re := by
    rw [hsplit, Complex.add_re]
  have hre_bound : |(w * (z / (1 - z))).re| ≤
      |w.re| * (zNorm / (1 - zNorm)) + |w.im| * (|z.im| / (1 - zNorm) ^ 2) :=
    abs_re_mul_div_one_sub_le w z hz_lt_one
  have hD_pos : 0 < D := chordD_pos ht1 ht_m1 v
  have hw_re : w.re = t * v ^ 2 / D := neg_chordBlaschke_re ht_m1 ht1 v
  have hw_im : w.im = -(1 - t ^ 2) * v / D := neg_chordBlaschke_im ht_m1 ht1 v
  have hw_re_abs : |w.re| = t * v ^ 2 / D := by
    rw [hw_re, abs_of_nonneg (by positivity)]
  have hw_im_abs : |w.im| = (1 - t ^ 2) * v / D := by
    have ha2 : 0 ≤ 1 - t ^ 2 := by nlinarith
    rw [hw_im, abs_div, abs_of_pos hD_pos, abs_mul, abs_neg, abs_of_nonneg ha2, abs_of_nonneg hv0.le]
  have hz_im_le : |z.im| ≤ ((2 * (n : ℝ) + 2) * t / v) * zNorm :=
    abs_reflection_z_im_le ht0 ht1 n hv0 hva
  have him_term : |w.im| * (|z.im| / (1 - zNorm) ^ 2) ≤
      t * ((2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) := by
    have h1z_sq_pos : 0 ≤ (1 - zNorm) ^ 2 := sq_nonneg _
    have hcoeff_nonneg : 0 ≤ (1 - t ^ 2) * v / D := by
      have : 0 ≤ 1 - t ^ 2 := by nlinarith
      positivity
    calc
      |w.im| * (|z.im| / (1 - zNorm) ^ 2)
          ≤ ((1 - t ^ 2) * v / D) * ((((2 * (n : ℝ) + 2) * t / v) * zNorm) / (1 - zNorm) ^ 2) := by
            rw [hw_im_abs]
            gcongr
      _ = t * ((2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) := by
            field_simp [hv0.ne', hD_pos.ne']
  have hre_lower :
      t * (v ^ 2 / D - (v ^ 2 / D) * (zNorm / (1 - zNorm)) -
        (2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) ≤
      (w / (1 - z)).re := by
    have hrem_abs : |(w * (z / (1 - z))).re| ≤
        t * ((v ^ 2 / D) * (zNorm / (1 - zNorm)) +
          (2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) := by
      calc
        |(w * (z / (1 - z))).re|
            ≤ |w.re| * (zNorm / (1 - zNorm)) + |w.im| * (|z.im| / (1 - zNorm) ^ 2) := hre_bound
        _ ≤ (t * v ^ 2 / D) * (zNorm / (1 - zNorm)) +
              t * ((2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) := by
              rw [hw_re_abs]
              gcongr
        _ = t * ((v ^ 2 / D) * (zNorm / (1 - zNorm)) +
              (2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) := by ring
    have hrem_ge : -(t * ((v ^ 2 / D) * (zNorm / (1 - zNorm)) +
        (2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2))) ≤
        (w * (z / (1 - z))).re := (neg_le_neg hrem_abs).trans (neg_abs_le _)
    rw [hre_split, hw_re]
    have htv_eq : t * v ^ 2 / D = t * (v ^ 2 / D) := by ring
    linarith
  have h1x_nonneg : 0 ≤ (1 - x) ^ n := pow_nonneg (by linarith) n
  have hfinal := mul_le_mul_of_nonneg_left hre_lower h1x_nonneg
  have hLHS :
      (1 - x) ^ n * (t * (v ^ 2 / D - (v ^ 2 / D) * (zNorm / (1 - zNorm)) -
        (2 * (n : ℝ) + 2) * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2))) =
      t * ((1 - x) ^ n * (v ^ 2 / D) -
        (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm)) -
        (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)) := by
    ring
  have hRHS : (1 - x) ^ n * (w / (1 - z)).re = chordIntegrand n t v := by
    unfold chordIntegrand
    rw [one_sub_chordX_eq t v]
  linarith

/-! ### Interval integrability of `chordIntegrand` on `[0, √(1 - t^2)]` -/

theorem chordIntegrand_continuousOn_Ico (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContinuousOn (chordIntegrand n t) (Ico 0 (Real.sqrt (1 - t ^ 2))) := by
  have ht_m1 : -1 < t := by linarith
  let uFn : ℝ → ℂ := fun v => (t : ℂ) + (v : ℂ) * Complex.I
  let phiFn : ℝ → ℂ := fun v => chordBlaschke t (uFn v)
  let denomFn : ℝ → ℂ := fun v => 1 - (uFn v) ^ (2 * n + 2) * (phiFn v) ^ 2
  have hu_cont : Continuous uFn :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have h1tu_ne : ∀ v : ℝ, (1 - (t : ℂ) * uFn v) ≠ 0 :=
    fun v => one_sub_mul_u_ne_zero ht_m1 ht1 v
  have hphi_cont : Continuous phiFn :=
    (hu_cont.sub continuous_const).div (continuous_const.sub (continuous_const.mul hu_cont)) h1tu_ne
  have hdenom_cont : Continuous denomFn :=
    continuous_const.sub ((hu_cont.pow _).mul (hphi_cont.pow 2))
  have hdenom_ne : ∀ v ∈ Ico (0 : ℝ) (Real.sqrt (1 - t ^ 2)), denomFn v ≠ 0 := by
    intro v hv hzero
    have hz1 : ‖(uFn v) ^ (2 * n + 2) * (phiFn v) ^ 2‖ = 1 := by
      have heq : (uFn v) ^ (2 * n + 2) * (phiFn v) ^ 2 = 1 := (sub_eq_zero.mp hzero).symm
      simp [heq]
    have hx_lt : chordX t v < 1 := chordX_lt_one ht0 ht1 hv.1 hv.2
    have hx_nonneg : 0 ≤ chordX t v := by unfold chordX; positivity
    have hle := norm_reflection_z_le ht_m1 ht1 n v
    have hpow_lt : (chordX t v) ^ (n + 2) < 1 := pow_lt_one₀ hx_nonneg hx_lt (by omega)
    change ‖(uFn v) ^ (2 * n + 2) * (phiFn v) ^ 2‖ ≤ (chordX t v) ^ (n + 2) at hle
    linarith
  have hfrac_cont : ContinuousOn (fun v => (-(phiFn v)) / denomFn v)
      (Ico 0 (Real.sqrt (1 - t ^ 2))) :=
    (hphi_cont.neg.continuousOn).div hdenom_cont.continuousOn hdenom_ne
  have hre_cont : ContinuousOn (fun v => ((-(phiFn v)) / denomFn v).re)
      (Ico 0 (Real.sqrt (1 - t ^ 2))) :=
    Complex.continuous_re.comp_continuousOn hfrac_cont
  have hpoly_cont : Continuous (fun v : ℝ => (1 - t ^ 2 - v ^ 2) ^ n) :=
    ((continuous_const.sub (continuous_pow 2))).pow n
  exact hpoly_cont.continuousOn.mul hre_cont

theorem chordIntegrand_norm_le_one (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {v : ℝ} (hv0 : 0 ≤ v) (hva : v < Real.sqrt (1 - t ^ 2)) :
    ‖chordIntegrand n t v‖ ≤ 1 := by
  have ht_m1 : -1 < t := by linarith
  let u : ℂ := (t : ℂ) + (v : ℂ) * Complex.I
  let φ : ℂ := chordBlaschke t u
  let z : ℂ := u ^ (2 * n + 2) * φ ^ 2
  have hx_lt : chordX t v < 1 := chordX_lt_one ht0 ht1 hv0 hva
  have hx_nonneg : 0 ≤ chordX t v := by unfold chordX; positivity
  have h1x_pos : 0 < 1 - chordX t v := sub_pos.mpr hx_lt
  have h1x_le_one : 1 - chordX t v ≤ 1 := by linarith
  have hphi_norm_le : ‖φ‖ ≤ 1 := by
    have hsq : ‖φ‖ ^ 2 ≤ 1 := by
      rw [norm_chordBlaschke_sq]
      exact (sq_div_chordD_le_chordX ht_m1 ht1 v).trans hx_lt.le
    nlinarith [norm_nonneg φ]
  have hz_le : ‖z‖ ≤ (chordX t v) ^ (n + 2) := norm_reflection_z_le ht_m1 ht1 n v
  have h1z_ge : 1 - chordX t v ≤ ‖1 - z‖ := by
    have hxn : (chordX t v) ^ (n + 2) ≤ chordX t v :=
      pow_le_of_le_one hx_nonneg hx_lt.le (by omega)
    have hrev : 1 - ‖z‖ ≤ ‖1 - z‖ := by simpa using norm_sub_norm_le (1 : ℂ) z
    linarith
  have hdiv_le : ‖(-φ) / (1 - z)‖ ≤ 1 / (1 - chordX t v) := by
    rw [norm_div, norm_neg]
    exact div_le_div₀ zero_le_one hphi_norm_le h1x_pos h1z_ge
  have hre_le : |((-φ) / (1 - z)).re| ≤ 1 / (1 - chordX t v) :=
    (Complex.abs_re_le_norm _).trans hdiv_le
  have hpow_le : (1 - chordX t v) ^ n ≤ 1 - chordX t v :=
    pow_le_of_le_one h1x_pos.le h1x_le_one (by omega)
  have hpoly_nonneg : 0 ≤ (1 - t ^ 2 - v ^ 2) ^ n := by
    rw [← one_sub_chordX_eq]
    exact pow_nonneg h1x_pos.le n
  unfold chordIntegrand
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpoly_nonneg, ← one_sub_chordX_eq t v]
  calc
    (1 - chordX t v) ^ n * |((-φ) / (1 - z)).re|
        ≤ (1 - chordX t v) * (1 / (1 - chordX t v)) := by gcongr
    _ = 1 := by field_simp [h1x_pos.ne']

theorem chordIntegrand_intervalIntegrable (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IntervalIntegrable (chordIntegrand n t) volume 0 (Real.sqrt (1 - t ^ 2)) := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ha2 : 0 < 1 - t ^ 2 := by nlinarith
  have ha_pos : 0 < a := Real.sqrt_pos.mpr ha2
  have hmeas_Ico : AEStronglyMeasurable (chordIntegrand n t) (volume.restrict (Ico 0 a)) :=
    (chordIntegrand_continuousOn_Ico n ht0 ht1).aestronglyMeasurable measurableSet_Ico
  have hbound : ∀ᵐ v ∂(volume.restrict (Ico 0 a)), ‖chordIntegrand n t v‖ ≤ 1 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ico] with v hv
    exact chordIntegrand_norm_le_one n hn ht0 ht1 hv.1 hv.2
  have hint_Ico : IntegrableOn (chordIntegrand n t) (Ico 0 a) volume :=
    IntegrableOn.of_bound measure_Ico_lt_top hmeas_Ico 1 hbound
  have hint_Ioc : IntegrableOn (chordIntegrand n t) (Ioc 0 a) volume := by
    rwa [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set Ico_ae_eq_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha_pos.le).mpr hint_Ioc

/-! ### Wallis integrals and Cauchy-Schwarz lower bound for the main term `M_n(t)` -/

/-- `I(n) = ∫_0^1 (1 - w^2)^n w^2 dw = (1/2) B(3/2, n+1)`. -/
noncomputable def wallisI (n : ℕ) : ℝ :=
  ∫ w in (0 : ℝ)..1, (1 - w ^ 2) ^ n * w ^ 2

/-- `J(n) = ∫_0^1 (1 - w^2)^n w^4 dw`. -/
noncomputable def wallisJ (n : ℕ) : ℝ :=
  ∫ w in (0 : ℝ)..1, (1 - w ^ 2) ^ n * w ^ 4

/-- Exact rational formula for `wallisI n`. -/
def wallisIRat : ℕ → ℚ
  | 0 => 1 / 3
  | n + 1 => ((2 * (n : ℚ) + 2) / (2 * (n : ℚ) + 5)) * wallisIRat n

theorem wallisI_zero : wallisI 0 = 1 / 3 := by
  unfold wallisI
  simp only [pow_zero, one_mul]
  have hd : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 3 / 3) (w ^ 2) w := fun w _ => by
    simpa [div_eq_mul_inv] using ((hasDerivAt_pow 3 w).div_const 3).congr_deriv (by ring)
  rw [integral_eq_sub_of_hasDerivAt hd ((continuous_pow 2).intervalIntegrable 0 1)]
  norm_num

theorem wallisJ_eq_mul_wallisI (n : ℕ) :
    (2 * (n : ℝ) + 5) * wallisJ n = 3 * wallisI n := by
  let u : ℝ → ℝ := fun w => w ^ 3
  let u' : ℝ → ℝ := fun w => 3 * w ^ 2
  let v : ℝ → ℝ := fun w => -((1 - w ^ 2) ^ (n + 1)) / (2 * ((n : ℝ) + 1))
  let v' : ℝ → ℝ := fun w => w * (1 - w ^ 2) ^ n
  have hu : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' w) w := fun w _ => by
    simpa [u, u'] using hasDerivAt_pow 3 w
  have hv : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt v (v' w) w := fun w _ => by
    have hinner : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * w)) w := by
      simpa using ((hasDerivAt_pow 2 w).const_sub 1).congr_deriv (by ring)
    have hpow : HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ (n + 1))
        (((n : ℝ) + 1) * (1 - w ^ 2) ^ n * (-(2 * w))) w :=
      (hinner.pow (n + 1)).congr_deriv (by
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one])
    have hden : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
    simpa [v, v'] using (hpow.neg.div_const (2 * ((n : ℝ) + 1))).congr_deriv (by
      field_simp [hden])
  have hu'_cont : ContinuousOn u' (uIcc (0 : ℝ) 1) := (continuous_const.mul (continuous_pow 2)).continuousOn
  have hv'_cont : ContinuousOn v' (uIcc (0 : ℝ) 1) :=
    (continuous_id.mul ((continuous_const.sub (continuous_pow 2)).pow n)).continuousOn
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'_cont.intervalIntegrable hv'_cont.intervalIntegrable
  have hibp_lhs : (∫ w in (0 : ℝ)..1, u w * v' w) = wallisJ n := by
    unfold wallisJ
    refine integral_congr fun w _ => ?_
    dsimp [u, v']
    ring
  have hibp_rhs_int : (∫ w in (0 : ℝ)..1, u' w * v w) =
      -(3 / (2 * ((n : ℝ) + 1))) * (wallisI n - wallisJ n) := by
    have hsplit : (fun w : ℝ => u' w * v w) =
        fun w : ℝ => -(3 / (2 * ((n : ℝ) + 1))) * ((1 - w ^ 2) ^ n * w ^ 2 - (1 - w ^ 2) ^ n * w ^ 4) := by
      ext w
      dsimp [u', v]
      ring
    rw [hsplit, integral_const_mul, integral_sub]
    · rfl
    · exact ((continuous_const.sub (continuous_pow 2)).pow n |>.mul (continuous_pow 2)).intervalIntegrable 0 1
    · exact ((continuous_const.sub (continuous_pow 2)).pow n |>.mul (continuous_pow 4)).intervalIntegrable 0 1
  have hbd : u 1 * v 1 - u 0 * v 0 = 0 := by
    simp [u, v]
  rw [hibp_lhs, hbd, hibp_rhs_int] at hibp
  have hden : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have hmul := congrArg (fun x => (2 * ((n : ℝ) + 1)) * x) hibp
  have hrhs_eq : (2 * ((n : ℝ) + 1)) * (0 - -(3 / (2 * ((n : ℝ) + 1))) * (wallisI n - wallisJ n)) =
      3 * wallisI n - 3 * wallisJ n := by
    field_simp [hden]
    ring
  linarith

theorem wallisI_succ (n : ℕ) :
    wallisI (n + 1) = ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 5)) * wallisI n := by
  have hsplit : wallisI (n + 1) = wallisI n - wallisJ n := by
    unfold wallisI wallisJ
    rw [← integral_sub]
    · refine integral_congr fun w _ => ?_
      ring
    · exact ((continuous_const.sub (continuous_pow 2)).pow n |>.mul (continuous_pow 2)).intervalIntegrable 0 1
    · exact ((continuous_const.sub (continuous_pow 2)).pow n |>.mul (continuous_pow 4)).intervalIntegrable 0 1
  have hJ := wallisJ_eq_mul_wallisI n
  have hpos : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  rw [show ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 5)) * wallisI n =
      (2 * (n : ℝ) + 2) * wallisI n / (2 * (n : ℝ) + 5) by ring, eq_div_iff hpos]
  nlinarith [hsplit, hJ]

theorem wallisI_eq_rat (n : ℕ) : wallisI n = (wallisIRat n : ℝ) := by
  induction n with
  | zero =>
    rw [wallisI_zero]
    norm_num [wallisIRat]
  | succ n ih =>
    rw [wallisI_succ, ih]
    simp only [wallisIRat, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_natCast]

theorem wallisI_pos (n : ℕ) : 0 < wallisI n := by
  induction n with
  | zero => rw [wallisI_zero]; norm_num
  | succ n ih =>
    rw [wallisI_succ]
    positivity

/-- Elementary Cauchy-Schwarz inequality on `[0, 1]`: `(∫ f)^2 / (∫ f * g) ≤ ∫ f / g`. -/
theorem cauchy_schwarz_div_le {f g : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1)) (hg_cont : ContinuousOn g (Icc 0 1))
    (hf_nonneg : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ f w)
    (hg_pos : ∀ w ∈ Icc (0 : ℝ) 1, 0 < g w)
    (hA_pos : 0 < ∫ w in (0 : ℝ)..1, f w * g w) :
    (∫ w in (0 : ℝ)..1, f w) ^ 2 / (∫ w in (0 : ℝ)..1, f w * g w) ≤
      ∫ w in (0 : ℝ)..1, f w / g w := by
  let A := ∫ w in (0 : ℝ)..1, f w * g w
  let B := ∫ w in (0 : ℝ)..1, f w
  let C := ∫ w in (0 : ℝ)..1, f w / g w
  let c : ℝ := B / A
  have hg_ne : ∀ w ∈ Icc (0 : ℝ) 1, g w ≠ 0 := fun w hw => (hg_pos w hw).ne'
  have hfg_int : IntervalIntegrable (fun w => f w * g w) volume 0 1 :=
    (hf_cont.mul hg_cont).intervalIntegrable_of_Icc zero_le_one
  have hf_int : IntervalIntegrable f volume 0 1 :=
    hf_cont.intervalIntegrable_of_Icc zero_le_one
  have hf_div_int : IntervalIntegrable (fun w => f w / g w) volume 0 1 :=
    (hf_cont.div hg_cont hg_ne).intervalIntegrable_of_Icc zero_le_one
  have hquad_nonneg : 0 ≤ ∫ w in (0 : ℝ)..1, (f w / g w) * (c * g w - 1) ^ 2 := by
    apply integral_nonneg zero_le_one
    intro w hw
    exact mul_nonneg (div_nonneg (hf_nonneg w hw) (hg_pos w hw).le) (sq_nonneg _)
  have hquad_eq : (∫ w in (0 : ℝ)..1, (f w / g w) * (c * g w - 1) ^ 2) =
      c ^ 2 * A - 2 * c * B + C := by
    have hcongr : EqOn (fun w => (f w / g w) * (c * g w - 1) ^ 2)
        (fun w => c ^ 2 * (f w * g w) - 2 * c * f w + f w / g w) (uIcc 0 1) := by
      intro w hw
      rw [uIcc_of_le zero_le_one] at hw
      have hgw := hg_ne w hw
      field_simp [hgw]
      ring
    rw [integral_congr hcongr,
      integral_add ((hfg_int.const_mul (c ^ 2)).sub (hf_int.const_mul (2 * c))) hf_div_int,
      integral_sub (hfg_int.const_mul (c ^ 2)) (hf_int.const_mul (2 * c)),
      integral_const_mul, integral_const_mul]
  have hpoly : 0 ≤ c ^ 2 * A - 2 * c * B + C := hquad_eq ▸ hquad_nonneg
  have hcalc : c ^ 2 * A - 2 * c * B + C = C - B ^ 2 / A := by
    have hAne : A ≠ 0 := hA_pos.ne'
    dsimp [c]
    field_simp [hAne]
    ring
  linarith

/-- Closed-form main-term lower bound `M_lb(n) = ((2n+5)/(2(n+3))) * (3/4)^(n-1) * (√3 / 2) * I(n)`.
Note this equals `(2n+5)/(3(n+3)) * (3/4)^(n+1/2) * B(3/2, n+1)` in `chebyshev_L1_complete.tex`. -/
noncomputable def mainTermLB (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 5) / (2 * ((n : ℝ) + 3))) * (3 / 4 : ℝ) ^ (n - 1) * (Real.sqrt 3 / 2) * wallisI n

theorem mainTerm_ge_lb (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    mainTermLB n ≤
      ∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2),
        (1 - chordX t v) ^ n * (v ^ 2 / chordD t v) := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ha2_eq : a ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha2_ge : (3 / 4 : ℝ) ≤ a ^ 2 := by linarith [show t ^ 2 ≤ 1 / 4 by nlinarith]
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hsub : (∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ n * (v ^ 2 / chordD t v)) =
      a ^ (2 * n + 1) * ∫ w in (0 : ℝ)..1, ((1 - w ^ 2) ^ n * w ^ 2) / (a ^ 2 + t ^ 2 * w ^ 2) := by
    have hcomp := intervalIntegral.integral_comp_mul_left
      (fun v => (1 - chordX t v) ^ n * (v ^ 2 / chordD t v)) ha_pos.ne' (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at hcomp
    have hleft : (∫ w in (0 : ℝ)..1, (1 - chordX t (a * w)) ^ n * ((a * w) ^ 2 / chordD t (a * w))) =
        a ^ (2 * n) * ∫ w in (0 : ℝ)..1, ((1 - w ^ 2) ^ n * w ^ 2) / (a ^ 2 + t ^ 2 * w ^ 2) := by
      rw [← integral_const_mul]
      refine integral_congr fun w _ => ?_
      have h1x : 1 - chordX t (a * w) = a ^ 2 * (1 - w ^ 2) := by
        unfold chordX
        rw [mul_pow, ha2_eq]
        ring
      have hD_eq : chordD t (a * w) = a ^ 2 * (a ^ 2 + t ^ 2 * w ^ 2) := by
        unfold chordD
        rw [← ha2_eq]
        ring
      rw [h1x, hD_eq, mul_pow, ← pow_mul]
      have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha_pos.ne'
      field_simp [ha2_ne]
    have hcomp' : (∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ n * (v ^ 2 / chordD t v)) =
        a * ∫ w in (0 : ℝ)..1, (1 - chordX t (a * w)) ^ n * ((a * w) ^ 2 / chordD t (a * w)) := by
      rw [hcomp, smul_eq_mul]
      field_simp [ha_pos.ne']
    rw [hcomp', hleft]
    ring
  let f : ℝ → ℝ := fun w => (1 - w ^ 2) ^ n * w ^ 2
  let g : ℝ → ℝ := fun w => a ^ 2 + t ^ 2 * w ^ 2
  have hf_cont : ContinuousOn f (Icc 0 1) :=
    (((continuous_const.sub (continuous_pow 2)).pow n).mul (continuous_pow 2)).continuousOn
  have hg_cont : ContinuousOn g (Icc 0 1) :=
    (continuous_const.add (continuous_const.mul (continuous_pow 2))).continuousOn
  have hf_nonneg : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ f w := by
    intro w hw
    have h1w : 0 ≤ 1 - w ^ 2 := by nlinarith [hw.1, hw.2]
    exact mul_nonneg (pow_nonneg h1w n) (sq_nonneg w)
  have hg_pos : ∀ w ∈ Icc (0 : ℝ) 1, 0 < g w := by
    intro w _
    dsimp [g]
    positivity
  have hA_eq : (∫ w in (0 : ℝ)..1, f w * g w) = (a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5)) * wallisI n := by
    have hcongr : (fun w => f w * g w) =
        fun w => a ^ 2 * ((1 - w ^ 2) ^ n * w ^ 2) + t ^ 2 * ((1 - w ^ 2) ^ n * w ^ 4) := by
      ext w
      dsimp [f, g]
      ring
    rw [hcongr, integral_add, integral_const_mul, integral_const_mul]
    · have hJ : wallisJ n = 3 / (2 * (n : ℝ) + 5) * wallisI n := by
        have h := wallisJ_eq_mul_wallisI n
        have hden : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
        field_simp [hden]
        linarith
      change a ^ 2 * wallisI n + t ^ 2 * wallisJ n = _
      rw [hJ]
      ring
    · exact (hf_cont.const_mul (a ^ 2)).intervalIntegrable_of_Icc zero_le_one
    · exact (((continuous_const.sub (continuous_pow 2)).pow n |>.mul (continuous_pow 4)).continuousOn.const_mul
        (t ^ 2)).intervalIntegrable_of_Icc zero_le_one
  have hA_pos : 0 < ∫ w in (0 : ℝ)..1, f w * g w := by
    rw [hA_eq]
    have hI := wallisI_pos n
    have hden : 0 < a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5) := by positivity
    exact mul_pos hden hI
  have hCS := cauchy_schwarz_div_le hf_cont hg_cont hf_nonneg hg_pos hA_pos
  have hB_eq : (∫ w in (0 : ℝ)..1, f w) = wallisI n := rfl
  rw [hB_eq, hA_eq] at hCS
  have hden_pos : 0 < a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5) := by positivity
  have hCS' : wallisI n / (a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5)) ≤
      ∫ w in (0 : ℝ)..1, f w / g w := by
    have hI := wallisI_pos n
    have heq : (wallisI n) ^ 2 / ((a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5)) * wallisI n) =
        wallisI n / (a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5)) := by
      field_simp [hI.ne', hden_pos.ne']
    linarith
  -- Bound `a^(2n+1) / (a^2 + 3 t^2 / (2n+5))` from below
  let c : ℝ := (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 5)
  have hc_lt : c < 1 := by
    dsimp [c]
    rw [div_lt_one (by positivity)]
    linarith
  have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
  have hs_le : t ^ 2 ≤ 1 / 4 := by nlinarith
  have hden_s : a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5) = 1 - c * t ^ 2 := by
    rw [ha2_eq]
    dsimp [c]
    have hpos : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
    field_simp [hpos]
    ring
  have hratio_ge : ((3 / 4 : ℝ) / (1 - c / 4)) ≤ a ^ 2 / (a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5)) := by
    rw [hden_s, ha2_eq]
    have h1c4_pos : 0 < 1 - c / 4 := by linarith
    have h1cs_pos : 0 < 1 - c * t ^ 2 := by nlinarith
    rw [div_le_div_iff₀ h1c4_pos h1cs_pos]
    have hdiff : (1 - t ^ 2) * (1 - c / 4) - (3 / 4) * (1 - c * t ^ 2) =
        (1 / 4 - t ^ 2) * (1 - c) := by ring
    have hnonneg : 0 ≤ (1 / 4 - t ^ 2) * (1 - c) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hratio_val : (3 / 4 : ℝ) / (1 - c / 4) = (2 * (n : ℝ) + 5) / (2 * ((n : ℝ) + 3)) := by
    dsimp [c]
    have h1 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
    have h2 : (n : ℝ) + 3 ≠ 0 := by positivity
    rw [div_eq_div_iff (by
      have hden : 1 - (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 5) / 4 = 3 * ((n : ℝ) + 3) / (2 * (2 * (n : ℝ) + 5)) := by
        field_simp [h1]; ring
      rw [hden]; positivity) (by positivity)]
    field_simp [h1, h2]
    ring
  have ha_pow_ge : (3 / 4 : ℝ) ^ (n - 1) * (Real.sqrt 3 / 2) ≤ a ^ (2 * n - 1) := by
    have ha_ge_s3 : Real.sqrt 3 / 2 ≤ a := by
      have h34 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_div (by norm_num), show Real.sqrt (4 : ℝ) = 2 by
          rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num]
      rw [← h34]
      exact Real.sqrt_le_sqrt (by linarith [ha2_eq, hs_le])
    have hpow_a2 : (3 / 4 : ℝ) ^ (n - 1) ≤ (a ^ 2) ^ (n - 1) :=
      pow_le_pow_left₀ (by norm_num) ha2_ge (n - 1)
    have hexp : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
    rw [hexp, pow_add, pow_one, pow_mul]
    exact mul_le_mul hpow_a2 ha_ge_s3 (by positivity) (by positivity)
  have ha_split : a ^ (2 * n + 1) = a ^ (2 * n - 1) * a ^ 2 := by
    have hexp : 2 * n + 1 = (2 * n - 1) + 2 := by omega
    rw [hexp, pow_add]
  have hI := wallisI_pos n
  calc
    mainTermLB n
        = ((3 / 4 : ℝ) / (1 - c / 4)) * ((3 / 4 : ℝ) ^ (n - 1) * (Real.sqrt 3 / 2)) * wallisI n := by
          unfold mainTermLB
          rw [hratio_val]
          ring
    _ ≤ (a ^ 2 / (a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5))) * a ^ (2 * n - 1) * wallisI n := by
          gcongr
    _ = a ^ (2 * n + 1) * (wallisI n / (a ^ 2 + 3 * t ^ 2 / (2 * (n : ℝ) + 5))) := by
          rw [ha_split]
          ring
    _ ≤ a ^ (2 * n + 1) * ∫ w in (0 : ℝ)..1, f w / g w := by gcongr
    _ = ∫ v in (0 : ℝ)..a, (1 - chordX t v) ^ n * (v ^ 2 / chordD t v) := hsub.symm

/-! ### Half-integer Beta integrals and elementary AM-GM remainder bound -/

/-- `halfBeta p q = ∫_0^1 (1 - x)^p * x^q * √x dx = B(p+1, q+3/2)`. -/
noncomputable def halfBeta (p q : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - x) ^ p * x ^ q * Real.sqrt x

/-- Exact rational formula for `halfBeta p q`. -/
def halfBetaRat : ℕ → ℕ → ℚ
  | 0, q => 2 / (2 * (q : ℚ) + 3)
  | p + 1, q => ((2 * (p : ℚ) + 2) / (2 * (q : ℚ) + 3)) * halfBetaRat p (q + 1)

private theorem hasDerivAt_id_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => y * Real.sqrt y) ((3 / 2 : ℝ) * Real.sqrt x) x := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [hasDerivAt_iff_tendsto_slope]
    simp only [Real.sqrt_zero, mul_zero]
    have hslope : (fun y : ℝ => slope (fun z => z * Real.sqrt z) 0 y) =ᶠ[nhdsWithin 0 ({0}ᶜ)] Real.sqrt := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [slope_def_field]
      simp only [Real.sqrt_zero, mul_zero, sub_zero]
      have hy0 : y ≠ 0 := hy
      field_simp [hy0]
    rw [Filter.tendsto_congr' hslope]
    have hcont : Filter.Tendsto Real.sqrt (nhdsWithin 0 ({0}ᶜ)) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Real.sqrt_zero] using hcont
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hsqrt : HasDerivAt Real.sqrt (2 * Real.sqrt x)⁻¹ x := by
      simpa [one_div] using Real.hasDerivAt_sqrt hx0
    have hmul := (hasDerivAt_id' x).mul hsqrt
    refine hmul.congr_deriv ?_
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
    have hs_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hxpos).ne'
    field_simp [hs_ne]
    nlinarith [hsq]

private theorem hasDerivAt_pow_mul_sqrt (q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => y ^ q * (y * Real.sqrt y))
      (((2 * (q : ℝ) + 3) / 2) * (x ^ q * Real.sqrt x)) x := by
  have h1 := hasDerivAt_pow q x
  have h2 := hasDerivAt_id_mul_sqrt hx
  refine (h1.mul h2).congr_deriv ?_
  cases q with
  | zero => simp
  | succ m =>
    simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]
    ring

theorem halfBeta_zero (q : ℕ) : halfBeta 0 q = 2 / (2 * (q : ℝ) + 3) := by
  unfold halfBeta
  simp only [pow_zero, one_mul]
  let F : ℝ → ℝ := fun y => (2 / (2 * (q : ℝ) + 3)) * (y ^ q * (y * Real.sqrt y))
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt F (x ^ q * Real.sqrt x) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have h := (hasDerivAt_pow_mul_sqrt q hx.1).const_mul (2 / (2 * (q : ℝ) + 3))
    refine h.congr_deriv ?_
    have hden : (2 * (q : ℝ) + 3) ≠ 0 := by positivity
    field_simp [hden]
  have hcont : Continuous (fun x : ℝ => x ^ q * Real.sqrt x) :=
    (continuous_pow q).mul Real.continuous_sqrt
  rw [integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable 0 1)]
  simp [F]

theorem halfBeta_succ_left (p q : ℕ) :
    halfBeta (p + 1) q = ((2 * (p : ℝ) + 2) / (2 * (q : ℝ) + 3)) * halfBeta p (q + 1) := by
  let u : ℝ → ℝ := fun x => (1 - x) ^ (p + 1)
  let u' : ℝ → ℝ := fun x => -((p : ℝ) + 1) * (1 - x) ^ p
  let v : ℝ → ℝ := fun x => (2 / (2 * (q : ℝ) + 3)) * (x ^ q * (x * Real.sqrt x))
  let v' : ℝ → ℝ := fun x => x ^ q * Real.sqrt x
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x := by
    intro x _
    have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    exact ((hasDerivAt_pow (p + 1) (1 - x)).comp x hinner).congr_deriv (by
      dsimp [u']; simp; ring)
  have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt v (v' x) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have h := (hasDerivAt_pow_mul_sqrt q hx.1).const_mul (2 / (2 * (q : ℝ) + 3))
    refine h.congr_deriv ?_
    have hden : (2 * (q : ℝ) + 3) ≠ 0 := by positivity
    dsimp [v']
    field_simp [hden]
  have hu'_int : IntervalIntegrable u' volume 0 1 :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow p)).intervalIntegrable 0 1
  have hv'_int : IntervalIntegrable v' volume 0 1 :=
    ((continuous_pow q).mul Real.continuous_sqrt).intervalIntegrable 0 1
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu'_int hv'_int
  have hbd : u 1 * v 1 - u 0 * v 0 = 0 := by
    simp [u, v]
  have hlhs : (∫ x in (0 : ℝ)..1, u x * v' x) = halfBeta (p + 1) q := by
    unfold halfBeta
    refine integral_congr fun x _ => ?_
    dsimp [u, v']
    ring
  have hrhs : (∫ x in (0 : ℝ)..1, u' x * v x) =
      -((2 * (p : ℝ) + 2) / (2 * (q : ℝ) + 3)) * halfBeta p (q + 1) := by
    unfold halfBeta
    rw [← integral_const_mul]
    refine integral_congr fun x _ => ?_
    dsimp [u', v]
    ring_nf
  rw [hlhs, hbd, hrhs] at hibp
  linarith

theorem halfBeta_succ_right (p q : ℕ) :
    halfBeta p (q + 1) = ((2 * (q : ℝ) + 3) / (2 * (p : ℝ) + 2 * (q : ℝ) + 5)) * halfBeta p q := by
  have hdiff : halfBeta p (q + 1) = halfBeta p q - halfBeta (p + 1) q := by
    unfold halfBeta
    rw [← integral_sub]
    · refine integral_congr fun x _ => ?_
      ring
    · exact (((continuous_const.sub continuous_id).pow p).mul (continuous_pow q) |>.mul
        Real.continuous_sqrt).intervalIntegrable 0 1
    · exact (((continuous_const.sub continuous_id).pow (p + 1)).mul (continuous_pow q) |>.mul
        Real.continuous_sqrt).intervalIntegrable 0 1
  rw [halfBeta_succ_left p q] at hdiff
  have hq : (2 * (q : ℝ) + 3) ≠ 0 := by positivity
  have hpq : (2 * (p : ℝ) + 2 * (q : ℝ) + 5) ≠ 0 := by positivity
  have hmul := congrArg (fun x => (2 * (q : ℝ) + 3) * x) hdiff
  field_simp [hq] at hmul
  rw [show ((2 * (q : ℝ) + 3) / (2 * (p : ℝ) + 2 * (q : ℝ) + 5)) * halfBeta p q =
      (2 * (q : ℝ) + 3) * halfBeta p q / (2 * (p : ℝ) + 2 * (q : ℝ) + 5) by ring, eq_div_iff hpq]
  linarith

theorem halfBeta_succ_both (p q : ℕ) :
    halfBeta (p + 1) (q + 1) =
      ((2 * (p : ℝ) + 2) * (2 * (q : ℝ) + 3) /
        ((2 * (p : ℝ) + 2 * (q : ℝ) + 5) * (2 * (p : ℝ) + 2 * (q : ℝ) + 7))) * halfBeta p q := by
  rw [halfBeta_succ_left p (q + 1), halfBeta_succ_right p (q + 1), halfBeta_succ_right p q]
  have h1 : (2 * ((q + 1 : ℕ) : ℝ) + 3) = 2 * (q : ℝ) + 5 := by push_cast; ring
  have h2 : (2 * (p : ℝ) + 2 * ((q + 1 : ℕ) : ℝ) + 5) = 2 * (p : ℝ) + 2 * (q : ℝ) + 7 := by
    push_cast; ring
  rw [h1, h2]
  have h5 : (2 * (q : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (p : ℝ) + 2 * (q : ℝ) + 7) ≠ 0 := by positivity
  have hpq5 : (2 * (p : ℝ) + 2 * (q : ℝ) + 5) ≠ 0 := by positivity
  field_simp [h5, h7, hpq5]

theorem halfBeta_eq_rat (p q : ℕ) : halfBeta p q = (halfBetaRat p q : ℝ) := by
  induction p generalizing q with
  | zero =>
    rw [halfBeta_zero]
    norm_num [halfBetaRat]
  | succ p ih =>
    rw [halfBeta_succ_left, ih (q + 1)]
    simp only [halfBetaRat, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_natCast]

theorem halfBeta_pos (p q : ℕ) : 0 < halfBeta p q := by
  induction p generalizing q with
  | zero => rw [halfBeta_zero]; positivity
  | succ p ih =>
    rw [halfBeta_succ_left]
    exact mul_pos (by positivity) (ih (q + 1))

/-- Elementary SOS inequality `(2 + x)(1 + x + x^2 + x^3) > 9 x` for all `x : ℝ`. -/
theorem two_add_x_mul_sum4_gt_nine_x (x : ℝ) :
    9 * x < (2 + x) * (1 + x + x ^ 2 + x ^ 3) := by
  have hid : (2 + x) * (1 + x + x ^ 2 + x ^ 3) - 9 * x =
      (x ^ 2 + (3 / 2 : ℝ) * x - 5 / 4) ^ 2 + (13 / 4 : ℝ) * (x - 9 / 26) ^ 2 + 5 / 104 := by
    ring
  have hsq1 : 0 ≤ (x ^ 2 + (3 / 2 : ℝ) * x - 5 / 4) ^ 2 := sq_nonneg _
  have hsq2 : 0 ≤ (13 / 4 : ℝ) * (x - 9 / 26) ^ 2 := by positivity
  linarith

theorem two_add_x_mul_geom_gt_nine_x (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    9 * x < (2 + x) * (∑ k ∈ Finset.range (n + 2), x ^ k) := by
  have hge4 : 1 + x + x ^ 2 + x ^ 3 ≤ ∑ k ∈ Finset.range (n + 2), x ^ k := by
    have hsplit : ∑ k ∈ Finset.range 4, x ^ k ≤ ∑ k ∈ Finset.range (n + 2), x ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ => pow_nonneg hx _
    have h4 : ∑ k ∈ Finset.range 4, x ^ k = 1 + x + x ^ 2 + x ^ 3 := by
      simp [Finset.sum_range_succ]
    linarith
  have h2x : 0 < 2 + x := by linarith
  calc
    9 * x < (2 + x) * (1 + x + x ^ 2 + x ^ 3) := two_add_x_mul_sum4_gt_nine_x x
    _ ≤ (2 + x) * (∑ k ∈ Finset.range (n + 2), x ^ k) := mul_le_mul_of_nonneg_left hge4 h2x.le

theorem chordD_ge_two_add_x_div_four {t : ℝ} (ht2 : t ^ 2 ≤ 1 / 4) {x : ℝ} (hx1 : x ≤ 1) :
    (2 + x) / 4 ≤ chordD t (Real.sqrt (x - t ^ 2)) := by
  rw [chordD_eq]
  have hx_eq : chordX t (Real.sqrt (x - t ^ 2)) = max x (t ^ 2) := by
    unfold chordX
    by_cases h : t ^ 2 ≤ x
    · rw [Real.sq_sqrt (by linarith), max_eq_left h]; ring
    · have hxlt : x - t ^ 2 ≤ 0 := by linarith
      rw [Real.sqrt_eq_zero_of_nonpos hxlt, zero_pow two_ne_zero, add_zero, max_eq_right (le_of_not_ge h)]
  have h2x : 0 ≤ 2 - x := by linarith
  by_cases h : t ^ 2 ≤ x
  · rw [hx_eq, max_eq_left h]
    nlinarith
  · rw [hx_eq, max_eq_right (le_of_not_ge h)]
    have h2t : 0 ≤ 2 - t ^ 2 := by linarith
    nlinarith

theorem chordD_ge_two_add_x_div_four_v {t v : ℝ} (ht2 : t ^ 2 ≤ 1 / 4)
    (hx1 : chordX t v ≤ 1) :
    (2 + chordX t v) / 4 ≤ chordD t v := by
  rw [chordD_eq]
  have h2x : 0 ≤ 2 - chordX t v := by linarith
  nlinarith

theorem one_sub_sq_div_chordD_sq_le {t v : ℝ} (ht2 : t ^ 2 ≤ 1 / 4)
    (hx0 : 0 ≤ chordX t v) (hx1 : chordX t v ≤ 1) :
    (1 - t ^ 2) / (chordD t v) ^ 2 ≤ 12 / (2 + chordX t v) ^ 2 := by
  let s := t ^ 2
  let x := chordX t v
  have hD_eq : chordD t v = 1 - (2 - x) * s := chordD_eq t v
  have hD_pos : 0 < chordD t v := by
    rw [hD_eq]
    have h2x : 0 ≤ 2 - x := by linarith
    nlinarith
  have h2x_pos : 0 < 2 + x := by linarith
  rw [div_le_div_iff₀ (sq_pos_of_pos hD_pos) (sq_pos_of_pos h2x_pos), hD_eq]
  have hid : 12 * (1 - (2 - x) * s) ^ 2 - (2 + x) ^ 2 * (1 - s) =
      (4 * s - 1) * (3 * s * (2 - x) ^ 2 + x ^ 2 + 4 * x - 8) := by
    ring
  have h1 : 4 * s - 1 ≤ 0 := by dsimp [s]; linarith
  have h2 : 3 * s * (2 - x) ^ 2 + x ^ 2 + 4 * x - 8 ≤ 0 := by
    have h3 : 3 * s * (2 - x) ^ 2 ≤ (3 / 4 : ℝ) * (2 - x) ^ 2 := by
      have : 0 ≤ (2 - x) ^ 2 := sq_nonneg _
      dsimp [s]
      nlinarith
    have hx2 : x ^ 2 ≤ x := by nlinarith
    linarith
  have hprod : 0 ≤ (4 * s - 1) * (3 * s * (2 - x) ^ 2 + x ^ 2 + 4 * x - 8) :=
    mul_nonneg_of_nonpos_of_nonpos h1 h2
  linarith

/-- First remainder bound term `T_1(n) = (2/9) B(n, n + 5/2)`. -/
noncomputable def remTerm1 (n : ℕ) : ℝ :=
  (2 / 9 : ℝ) * halfBeta (n - 1) (n + 1)

/-- Second remainder bound term `T_2(n) = (4(n+1)/27) B(n-1, n + 1/2)`. -/
noncomputable def remTerm2 (n : ℕ) : ℝ :=
  (4 * ((n : ℝ) + 1) / 27) * halfBeta (n - 2) (n - 1)

/-- Remainder upper-bound integrand `remIntegrand n t v` from `chordIntegrand_ge`. -/
noncomputable def remIntegrand (n : ℕ) (t v : ℝ) : ℝ :=
  let x := chordX t v
  let D := chordD t v
  let zNorm := ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
    (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖
  (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm)) +
    (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)

theorem remIntegrand_intervalIntegrable (n : ℕ) (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IntervalIntegrable (remIntegrand n t) volume 0 (Real.sqrt (1 - t ^ 2)) := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ht_m1 : -1 < t := by linarith
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  let zNormFn : ℝ → ℝ := fun v =>
    ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
      (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖
  have hx_cont : Continuous (chordX t) := by unfold chordX; exact continuous_const.add (continuous_pow 2)
  have hD_cont : Continuous (chordD t) := by
    unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
  have hz_cont : Continuous zNormFn := by
    dsimp [zNormFn]
    have hu : Continuous (fun v : ℝ => (t : ℂ) + (v : ℂ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hphi : Continuous (fun v : ℝ => chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) :=
      (hu.sub continuous_const).div (continuous_const.sub (continuous_const.mul hu))
        (fun v => one_sub_mul_u_ne_zero ht_m1 ht1 v)
    exact ((hu.pow _).mul (hphi.pow 2)).norm
  have h1z_ne : ∀ v ∈ Ico (0 : ℝ) a, 1 - zNormFn v ≠ 0 := by
    intro v hv
    have hx_lt : chordX t v < 1 := chordX_lt_one ht0 ht1 hv.1 hv.2
    have hx0 : 0 ≤ chordX t v := by unfold chordX; positivity
    have hz_lt : zNormFn v < 1 :=
      (norm_reflection_z_le ht_m1 ht1 n v).trans_lt (pow_lt_one₀ hx0 hx_lt (by omega))
    linarith
  have hcont_Ico : ContinuousOn (remIntegrand n t) (Ico 0 a) := by
    have hfrac1 : ContinuousOn (fun v => zNormFn v / (1 - zNormFn v)) (Ico 0 a) :=
      hz_cont.continuousOn.div (continuous_const.sub hz_cont).continuousOn h1z_ne
    have hfrac2 : ContinuousOn (fun v => zNormFn v / (1 - zNormFn v) ^ 2) (Ico 0 a) :=
      hz_cont.continuousOn.div ((continuous_const.sub hz_cont).pow 2).continuousOn
        (fun v hv => pow_ne_zero 2 (h1z_ne v hv))
    have h1 : ContinuousOn (fun v => (1 - chordX t v) ^ n * (v ^ 2 / chordD t v) *
        (zNormFn v / (1 - zNormFn v))) (Ico 0 a) :=
      ((((continuous_const.sub hx_cont).pow n).mul ((continuous_pow 2).div hD_cont
        fun v => (chordD_pos ht1 ht_m1 v).ne')).continuousOn).mul hfrac1
    have h2 : ContinuousOn (fun v => (2 * (n : ℝ) + 2) * (1 - chordX t v) ^ n *
        ((1 - t ^ 2) / chordD t v) * (zNormFn v / (1 - zNormFn v) ^ 2)) (Ico 0 a) :=
      (((continuous_const.mul ((continuous_const.sub hx_cont).pow n)).mul
        (continuous_const.div hD_cont fun v => (chordD_pos ht1 ht_m1 v).ne')).continuousOn).mul hfrac2
    exact h1.add h2
  let M : ℝ := 1 + (2 * (n : ℝ) + 2) / chordD t 0
  have hM_bound : ∀ v ∈ Ico (0 : ℝ) a, ‖remIntegrand n t v‖ ≤ M := by
    intro v hv
    let x := chordX t v
    let D := chordD t v
    let zNorm := zNormFn v
    have hx_lt : x < 1 := chordX_lt_one ht0 ht1 hv.1 hv.2
    have hx0 : 0 ≤ x := by dsimp [x, chordX]; positivity
    have h1x_pos : 0 < 1 - x := sub_pos.mpr hx_lt
    have hD_pos : 0 < D := chordD_pos ht1 ht_m1 v
    have hz_le : zNorm ≤ x ^ (n + 2) := norm_reflection_z_le ht_m1 ht1 n v
    have hz_le1 : zNorm ≤ 1 := hz_le.trans (pow_le_one₀ hx0 hx_lt.le)
    have h1z_ge : 1 - x ≤ 1 - zNorm := by
      have : x ^ (n + 2) ≤ x := pow_le_of_le_one hx0 hx_lt.le (by omega)
      linarith
    have hD_ge0 : chordD t 0 ≤ D := by unfold D chordD; nlinarith [sq_nonneg t, sq_nonneg v]
    have hD0_pos : 0 < chordD t 0 := chordD_pos ht1 ht_m1 0
    have hvD_le : v ^ 2 / D ≤ 1 := (sq_div_chordD_le_chordX ht_m1 ht1 v).trans hx_lt.le
    have ht1_nonneg : 0 ≤ 1 - t ^ 2 := by nlinarith
    have ht1_le1 : 1 - t ^ 2 ≤ 1 := by linarith [sq_nonneg t]
    have hterm1_nonneg : 0 ≤ (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm)) := by positivity
    have hterm2_nonneg : 0 ≤ (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2) := by
      positivity
    have hterm1_le : (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm)) ≤ 1 := by
      have h1 : (1 - x) ^ n ≤ 1 - x := pow_le_of_le_one h1x_pos.le (by linarith) (by omega)
      have h2 : zNorm / (1 - zNorm) ≤ 1 / (1 - x) := div_le_div₀ zero_le_one hz_le1 h1x_pos h1z_ge
      calc
        (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm))
            ≤ (1 - x) * 1 * (1 / (1 - x)) := by gcongr
        _ = 1 := by field_simp [h1x_pos.ne']
    have hterm2_le : (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2) ≤
        (2 * (n : ℝ) + 2) / chordD t 0 := by
      have h1 : (1 - x) ^ n ≤ (1 - x) ^ 2 := pow_le_pow_of_le_one h1x_pos.le (by linarith) hn
      have h2 : zNorm / (1 - zNorm) ^ 2 ≤ 1 / (1 - x) ^ 2 :=
        div_le_div₀ zero_le_one hz_le1 (sq_pos_of_pos h1x_pos) (pow_le_pow_left₀ h1x_pos.le h1z_ge 2)
      have h3 : (1 - t ^ 2) / D ≤ 1 / chordD t 0 := div_le_div₀ zero_le_one ht1_le1 hD0_pos hD_ge0
      have h3_nonneg : 0 ≤ (1 - t ^ 2) / D := div_nonneg ht1_nonneg hD_pos.le
      calc
        (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)
            ≤ (2 * (n : ℝ) + 2) * (1 - x) ^ 2 * (1 / chordD t 0) * (1 / (1 - x) ^ 2) := by gcongr
        _ = (2 * (n : ℝ) + 2) / chordD t 0 := by field_simp [h1x_pos.ne', hD0_pos.ne']
    change ‖(1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm)) +
      (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hterm1_nonneg hterm2_nonneg)]
    dsimp [M]
    linarith
  have hint_Ico : IntegrableOn (remIntegrand n t) (Ico 0 a) volume :=
    IntegrableOn.of_bound measure_Ico_lt_top
      (hcont_Ico.aestronglyMeasurable measurableSet_Ico) M
      (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ico] with v hv; exact hM_bound v hv)
  have hint_Ioc : IntegrableOn (remIntegrand n t) (Ioc 0 a) volume := by
    rwa [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set Ico_ae_eq_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha_pos.le).mpr hint_Ioc

private noncomputable def geomS (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range (n + 2), x ^ k

private theorem geomS_ge_one (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ geomS n x := by
  unfold geomS
  have h0 : (0 : ℕ) ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
  calc
    (1 : ℝ) = x ^ 0 := by simp
    _ ≤ ∑ k ∈ Finset.range (n + 2), x ^ k :=
      Finset.single_le_sum (fun k _ => pow_nonneg hx k) h0

private theorem continuous_geomS (n : ℕ) : Continuous (geomS n) := by
  unfold geomS
  exact continuous_finsetSum _ fun k _ => continuous_pow k

private noncomputable def remG1 (n : ℕ) (t v : ℝ) : ℝ :=
  (1 - chordX t v) ^ (n - 1) * (chordX t v) ^ (n + 2) * (v / chordD t v) / geomS n (chordX t v) * v

private noncomputable def remG2 (n : ℕ) (t v : ℝ) : ℝ :=
  (2 * (n : ℝ) + 2) * (1 - chordX t v) ^ (n - 2) * (chordX t v) ^ (n + 1) *
    ((1 - t ^ 2) / (chordD t v) ^ 2) / (geomS n (chordX t v)) ^ 2 * (v * v)

private noncomputable def remH1 (n : ℕ) (t x : ℝ) : ℝ :=
  (1 - x) ^ (n - 1) * x ^ (n + 2) *
    (Real.sqrt (x - t ^ 2) / (2 * chordD t (Real.sqrt (x - t ^ 2)))) / geomS n x

private noncomputable def remH2 (n : ℕ) (t x : ℝ) : ℝ :=
  (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt (x - t ^ 2) *
    ((1 - t ^ 2) / (chordD t (Real.sqrt (x - t ^ 2))) ^ 2) / (geomS n x) ^ 2

private theorem continuous_remG1 (n : ℕ) {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    Continuous (remG1 n t) := by
  unfold remG1
  have hx_cont : Continuous (chordX t) := by unfold chordX; exact continuous_const.add (continuous_pow 2)
  have hD_cont : Continuous (chordD t) := by
    unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
  have hS_ne : ∀ v : ℝ, geomS n (chordX t v) ≠ 0 := fun v => by
    have hx0 : 0 ≤ chordX t v := by unfold chordX; positivity
    linarith [geomS_ge_one n hx0]
  refine (((((continuous_const.sub hx_cont).pow (n - 1)).mul (hx_cont.pow (n + 2))).mul
    (continuous_id.div hD_cont fun v => (chordD_pos ht1 ht0 v).ne')).div
    ((continuous_geomS n).comp hx_cont) hS_ne).mul continuous_id

private theorem continuous_remG2 (n : ℕ) {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    Continuous (remG2 n t) := by
  unfold remG2
  have hx_cont : Continuous (chordX t) := by unfold chordX; exact continuous_const.add (continuous_pow 2)
  have hD_cont : Continuous (chordD t) := by
    unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
  have hS_ne : ∀ v : ℝ, geomS n (chordX t v) ≠ 0 := fun v => by
    have hx0 : 0 ≤ chordX t v := by unfold chordX; positivity
    linarith [geomS_ge_one n hx0]
  refine (((((continuous_const.mul ((continuous_const.sub hx_cont).pow (n - 2))).mul
    (hx_cont.pow (n + 1))).mul (continuous_const.div (hD_cont.pow 2) fun v =>
    pow_ne_zero 2 (chordD_pos ht1 ht0 v).ne')).div
    (((continuous_geomS n).comp hx_cont).pow 2) fun v => pow_ne_zero 2 (hS_ne v))).mul
    (continuous_id.mul continuous_id)

private theorem remIntegrand_integral_le_g (n : ℕ) (hn : 4 ≤ n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), remIntegrand n t v ≤
      (∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), remG1 n t v) +
        (∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), remG2 n t v) := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ht_m1 : -1 < t := by linarith
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  have hpointwise : ∀ v ∈ Ioo (0 : ℝ) a, remIntegrand n t v ≤ remG1 n t v + remG2 n t v := by
    intro v hv
    let x := chordX t v
    let D := chordD t v
    let zNorm := ‖((t : ℂ) + (v : ℂ) * Complex.I) ^ (2 * n + 2) *
      (chordBlaschke t ((t : ℂ) + (v : ℂ) * Complex.I)) ^ 2‖
    have hx_lt : x < 1 := chordX_lt_one ht0.le ht1 hv.1.le hv.2
    have hx0 : 0 ≤ x := by dsimp [x, chordX]; positivity
    have h1x_pos : 0 < 1 - x := sub_pos.mpr hx_lt
    have hS_ge : 1 ≤ geomS n x := geomS_ge_one n hx0
    have hgeom : (1 - x) * geomS n x = 1 - x ^ (n + 2) := by
      unfold geomS
      have h := mul_geom_sum x (n + 2)
      linarith
    have hz_eq : zNorm = x ^ (n + 1) * (v ^ 2 / D) := norm_reflection_z_eq t n v
    have hz_le : zNorm ≤ x ^ (n + 2) := norm_reflection_z_le ht_m1 ht1 n v
    have h1z_ge : (1 - x) * geomS n x ≤ 1 - zNorm := by linarith
    have h1xS_pos : 0 < (1 - x) * geomS n x := mul_pos h1x_pos (by linarith)
    have hD_pos : 0 < D := chordD_pos ht1 ht_m1 v
    have ht1_nonneg : 0 ≤ 1 - t ^ 2 := by nlinarith
    have ht1_div_D : 0 ≤ (1 - t ^ 2) / D := div_nonneg ht1_nonneg hD_pos.le
    have hterm1 : (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm)) ≤ remG1 n t v := by
      have hdiv : zNorm / (1 - zNorm) ≤ x ^ (n + 2) / ((1 - x) * geomS n x) :=
        div_le_div₀ (pow_nonneg hx0 _) hz_le h1xS_pos h1z_ge
      have hS_ne : geomS n x ≠ 0 := by linarith
      have h1x_ne : 1 - x ≠ 0 := h1x_pos.ne'
      have hexp : n = (n - 1) + 1 := by omega
      calc
        (1 - x) ^ n * (v ^ 2 / D) * (zNorm / (1 - zNorm))
            ≤ (1 - x) ^ n * (v ^ 2 / D) * (x ^ (n + 2) / ((1 - x) * geomS n x)) := by gcongr
        _ = (1 - x) ^ (n - 1) * x ^ (n + 2) * (v / D) / geomS n x * v := by
            nth_rw 1 [hexp]
            rw [pow_add, pow_one]
            have hcancel : (1 - x) ^ (n - 1) * (1 - x) * (v ^ 2 / D) * (x ^ (n + 2) / ((1 - x) * geomS n x)) =
                (1 - x) ^ (n - 1) * x ^ (n + 2) * (v / D) / geomS n x * v := by
              rw [show (1 - x) * geomS n x = (1 - x) * geomS n x from rfl]
              calc
                (1 - x) ^ (n - 1) * (1 - x) * (v ^ 2 / D) * (x ^ (n + 2) / ((1 - x) * geomS n x))
                    = ((1 - x) / (1 - x)) * ((1 - x) ^ (n - 1) * x ^ (n + 2) * (v / D) / geomS n x * v) := by
                        field_simp [hD_pos.ne', hS_ne, h1x_ne]
                _ = (1 - x) ^ (n - 1) * x ^ (n + 2) * (v / D) / geomS n x * v := by
                        rw [div_self h1x_ne, one_mul]
            exact hcancel
        _ = remG1 n t v := rfl
    have hterm2 : (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2) ≤
        remG2 n t v := by
      have hdiv : zNorm / (1 - zNorm) ^ 2 ≤ (x ^ (n + 1) * (v ^ 2 / D)) / ((1 - x) * geomS n x) ^ 2 := by
        rw [← hz_eq]
        exact div_le_div₀ (norm_nonneg _) le_rfl (sq_pos_of_pos h1xS_pos)
          (pow_le_pow_left₀ h1xS_pos.le h1z_ge 2)
      have hS_ne : geomS n x ≠ 0 := by linarith
      have h1x_ne : 1 - x ≠ 0 := h1x_pos.ne'
      have hpow1x : (1 - x) ^ n = (1 - x) ^ (n - 2) * (1 - x) ^ 2 := by
        rw [← pow_add]; congr 1; omega
      calc
        (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) * (zNorm / (1 - zNorm) ^ 2)
            ≤ (2 * (n : ℝ) + 2) * (1 - x) ^ n * ((1 - t ^ 2) / D) *
                ((x ^ (n + 1) * (v ^ 2 / D)) / ((1 - x) * geomS n x) ^ 2) := by gcongr
        _ = (2 * (n : ℝ) + 2) * (1 - x) ^ (n - 2) * x ^ (n + 1) *
              ((1 - t ^ 2) / D ^ 2) / (geomS n x) ^ 2 * (v * v) := by
            rw [hpow1x]
            calc
              (2 * (n : ℝ) + 2) * ((1 - x) ^ (n - 2) * (1 - x) ^ 2) * ((1 - t ^ 2) / D) *
                  ((x ^ (n + 1) * (v ^ 2 / D)) / ((1 - x) * geomS n x) ^ 2)
                  = ((1 - x) ^ 2 / (1 - x) ^ 2) *
                      ((2 * (n : ℝ) + 2) * (1 - x) ^ (n - 2) * x ^ (n + 1) *
                        ((1 - t ^ 2) / D ^ 2) / (geomS n x) ^ 2 * (v * v)) := by
                      rw [mul_pow]
                      field_simp [hD_pos.ne', hS_ne, h1x_ne]
              _ = (2 * (n : ℝ) + 2) * (1 - x) ^ (n - 2) * x ^ (n + 1) *
                    ((1 - t ^ 2) / D ^ 2) / (geomS n x) ^ 2 * (v * v) := by
                      rw [div_self (pow_ne_zero 2 h1x_ne), one_mul]
        _ = remG2 n t v := rfl
    exact add_le_add hterm1 hterm2
  have hg1_int : IntervalIntegrable (remG1 n t) volume 0 a :=
    (continuous_remG1 n ht_m1 ht1).intervalIntegrable 0 a
  have hg2_int : IntervalIntegrable (remG2 n t) volume 0 a :=
    (continuous_remG2 n ht_m1 ht1).intervalIntegrable 0 a
  have hLHS_int := remIntegrand_intervalIntegrable n (by omega) ht0.le ht1
  have hmono := integral_mono_on_of_le_Ioo ha_pos.le hLHS_int (hg1_int.add hg2_int) hpointwise
  rw [intervalIntegral.integral_add hg1_int hg2_int] at hmono
  exact hmono

private theorem remH1_continuousOn (n : ℕ) {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    ContinuousOn (remH1 n t) (Icc 0 1) := by
  unfold remH1
  have hD_cont : Continuous (chordD t) := by
    unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
  have hD_sqrt_cont : Continuous (fun x => chordD t (Real.sqrt (x - t ^ 2))) :=
    hD_cont.comp (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))
  have hS_ne_Icc : ∀ x ∈ Icc (0 : ℝ) 1, geomS n x ≠ 0 := fun x hx => by
    linarith [geomS_ge_one n hx.1]
  refine (((((continuous_const.sub continuous_id).pow (n - 1)).mul (continuous_pow (n + 2))).mul
    ((Real.continuous_sqrt.comp (continuous_id.sub continuous_const)).div
      (continuous_const.mul hD_sqrt_cont) fun x =>
      mul_ne_zero two_ne_zero (chordD_pos ht1 ht0 _).ne')).continuousOn).div
    (continuous_geomS n).continuousOn hS_ne_Icc

private theorem remH2_continuousOn (n : ℕ) {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) :
    ContinuousOn (remH2 n t) (Icc 0 1) := by
  unfold remH2
  have hD_cont : Continuous (chordD t) := by
    unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
  have hD_sqrt_cont : Continuous (fun x => chordD t (Real.sqrt (x - t ^ 2))) :=
    hD_cont.comp (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))
  have hS_ne_Icc : ∀ x ∈ Icc (0 : ℝ) 1, geomS n x ≠ 0 := fun x hx => by
    linarith [geomS_ge_one n hx.1]
  refine ((((((continuous_const.mul ((continuous_const.sub continuous_id).pow (n - 2))).mul
    (continuous_pow (n + 1))).mul (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))).mul
    (continuous_const.div (hD_sqrt_cont.pow 2) fun x =>
      pow_ne_zero 2 (chordD_pos ht1 ht0 _).ne')).continuousOn).div
    (((continuous_geomS n).pow 2).continuousOn) fun x hx => pow_ne_zero 2 (hS_ne_Icc x hx))

private theorem remG1_eq_remH1_integral (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), remG1 n t v) = ∫ x in (0 : ℝ)..1, remH1 n t x := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ht_m1 : -1 < t := by linarith
  have ht_lt1 : t < 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have ha2_eq : a ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hx_cont : Continuous (chordX t) := by unfold chordX; exact continuous_const.add (continuous_pow 2)
  have hsub : (∫ v in (0 : ℝ)..a, remG1 n t v) = ∫ x in (t ^ 2)..1, remH1 n t x := by
    have hcomp := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := chordX t) (f' := fun v => 2 * v) (g := remH1 n t) (a := 0) (b := a)
      hx_cont.continuousOn
      (fun v _ => by
        unfold chordX
        simpa using ((hasDerivAt_pow 2 v).const_add (t ^ 2)).congr_deriv (by simp))
      (fun v hv => by rw [min_eq_left ha_pos.le] at hv; linarith [hv.1])
    have hlim0 : chordX t 0 = t ^ 2 := by unfold chordX; ring
    have hlim1 : chordX t a = 1 := by unfold chordX; rw [ha2_eq]; ring
    rw [hlim0, hlim1] at hcomp
    rw [← hcomp]
    refine integral_congr fun v hv => ?_
    rw [uIcc_of_le ha_pos.le] at hv
    unfold remG1 remH1
    dsimp only [Function.comp_def]
    have hsqrt_v : Real.sqrt (chordX t v - t ^ 2) = v := by
      unfold chordX
      rw [add_sub_cancel_left, Real.sqrt_sq hv.1]
    rw [hsqrt_v]
    ring
  have hh_cont := remH1_continuousOn n ht_m1 ht_lt1
  have h0_t2 : IntervalIntegrable (remH1 n t) volume 0 (t ^ 2) :=
    (hh_cont.mono (Icc_subset_Icc_right ht2 |>.trans (Icc_subset_Icc_right (by norm_num)))).intervalIntegrable_of_Icc
      (sq_nonneg t)
  have ht2_1 : IntervalIntegrable (remH1 n t) volume (t ^ 2) 1 :=
    (hh_cont.mono (Icc_subset_Icc_left (sq_nonneg t))).intervalIntegrable_of_Icc (by linarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0_t2 ht2_1
  have hzero : (∫ x in (0 : ℝ)..(t ^ 2), remH1 n t x) = 0 := by
    have hcongr : ∀ x ∈ uIcc (0 : ℝ) (t ^ 2), remH1 n t x = 0 := fun x hx => by
      rw [uIcc_of_le (sq_nonneg t)] at hx
      unfold remH1
      rw [Real.sqrt_eq_zero_of_nonpos (by linarith [hx.2])]
      simp
    rw [integral_congr hcongr, integral_zero]
  linarith

private theorem remG2_eq_remH2_integral (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), remG2 n t v) = ∫ x in (0 : ℝ)..1, remH2 n t x := by
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ht_m1 : -1 < t := by linarith
  have ht_lt1 : t < 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have ha2_eq : a ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hx_cont : Continuous (chordX t) := by unfold chordX; exact continuous_const.add (continuous_pow 2)
  have hsub : (∫ v in (0 : ℝ)..a, remG2 n t v) = ∫ x in (t ^ 2)..1, remH2 n t x := by
    have hcomp := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := chordX t) (f' := fun v => 2 * v) (g := remH2 n t) (a := 0) (b := a)
      hx_cont.continuousOn
      (fun v _ => by
        unfold chordX
        simpa using ((hasDerivAt_pow 2 v).const_add (t ^ 2)).congr_deriv (by simp))
      (fun v hv => by rw [min_eq_left ha_pos.le] at hv; linarith [hv.1])
    have hlim0 : chordX t 0 = t ^ 2 := by unfold chordX; ring
    have hlim1 : chordX t a = 1 := by unfold chordX; rw [ha2_eq]; ring
    rw [hlim0, hlim1] at hcomp
    rw [← hcomp]
    refine integral_congr fun v hv => ?_
    rw [uIcc_of_le ha_pos.le] at hv
    unfold remG2 remH2
    dsimp only [Function.comp_def]
    have hsqrt_v : Real.sqrt (chordX t v - t ^ 2) = v := by
      unfold chordX
      rw [add_sub_cancel_left, Real.sqrt_sq hv.1]
    rw [hsqrt_v]
    ring
  have hh_cont := remH2_continuousOn n ht_m1 ht_lt1
  have h0_t2 : IntervalIntegrable (remH2 n t) volume 0 (t ^ 2) :=
    (hh_cont.mono (Icc_subset_Icc_right ht2 |>.trans (Icc_subset_Icc_right (by norm_num)))).intervalIntegrable_of_Icc
      (sq_nonneg t)
  have ht2_1 : IntervalIntegrable (remH2 n t) volume (t ^ 2) 1 :=
    (hh_cont.mono (Icc_subset_Icc_left (sq_nonneg t))).intervalIntegrable_of_Icc (by linarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0_t2 ht2_1
  have hzero : (∫ x in (0 : ℝ)..(t ^ 2), remH2 n t x) = 0 := by
    have hcongr : ∀ x ∈ uIcc (0 : ℝ) (t ^ 2), remH2 n t x = 0 := fun x hx => by
      rw [uIcc_of_le (sq_nonneg t)] at hx
      unfold remH2
      rw [Real.sqrt_eq_zero_of_nonpos (by linarith [hx.2])]
      simp
    rw [integral_congr hcongr, integral_zero]
  linarith

private theorem remH1_integral_lt (n : ℕ) (hn : 4 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (∫ x in (0 : ℝ)..1, remH1 n t x) < remTerm1 n := by
  have ht_m1 : -1 < t := by linarith
  have ht_lt1 : t < 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  let t₁Fn : ℝ → ℝ := fun x => (2 / 9 : ℝ) * ((1 - x) ^ (n - 1) * x ^ (n + 1) * Real.sqrt x)
  have ht₁_cont : ContinuousOn t₁Fn (Icc 0 1) :=
    (continuous_const.mul ((((continuous_const.sub continuous_id).pow (n - 1)).mul
      (continuous_pow (n + 1))).mul Real.continuous_sqrt)).continuousOn
  have hh₁_cont := remH1_continuousOn n ht_m1 ht_lt1
  have h1_le_t1 : ∀ x ∈ Icc (0 : ℝ) 1, remH1 n t x ≤ t₁Fn x := by
    intro x hx
    unfold remH1
    by_cases hxt : x ≤ t ^ 2
    · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
      simp only [zero_div, mul_zero]
      dsimp [t₁Fn]
      have h1x : 0 ≤ 1 - x := by linarith [hx.2]
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (pow_nonneg h1x _) (pow_nonneg hx.1 _))
        (Real.sqrt_nonneg x))
    · have hxpos : 0 < x := lt_of_le_of_lt (sq_nonneg t) (lt_of_not_ge hxt)
      have hsqrt_le : Real.sqrt (x - t ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith [sq_nonneg t])
      have hD_ge : (2 + x) / 4 ≤ chordD t (Real.sqrt (x - t ^ 2)) := chordD_ge_two_add_x_div_four ht2 hx.2
      have h2x_pos : 0 < 2 + x := by linarith [hx.1]
      have hD_pos : 0 < chordD t (Real.sqrt (x - t ^ 2)) := by linarith
      have hAMGM : 9 * x < (2 + x) * geomS n x := two_add_x_mul_geom_gt_nine_x n (by omega) hx.1
      have hS_ge1 : 1 ≤ geomS n x := geomS_ge_one n hx.1
      have h1x : 0 ≤ 1 - x := by linarith [hx.2]
      have hdiv_le : Real.sqrt (x - t ^ 2) / (2 * chordD t (Real.sqrt (x - t ^ 2)) * geomS n x) ≤
          Real.sqrt x / ((2 + x) / 2 * geomS n x) := by
        refine div_le_div₀ (Real.sqrt_nonneg x) hsqrt_le (by positivity) ?_
        have : (2 + x) / 2 * geomS n x = 2 * ((2 + x) / 4) * geomS n x := by ring
        rw [this]
        gcongr
      have hAMGM2 : Real.sqrt x / ((2 + x) / 2 * geomS n x) ≤ 2 * Real.sqrt x / (9 * x) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 2 * Real.sqrt x * ((2 + x) / 2 * geomS n x) - Real.sqrt x * (9 * x) =
            Real.sqrt x * ((2 + x) * geomS n x - 9 * x) := by ring
        have hpos_diff : 0 ≤ Real.sqrt x * ((2 + x) * geomS n x - 9 * x) :=
          mul_nonneg (Real.sqrt_nonneg x) (by linarith)
        linarith
      calc
        (1 - x) ^ (n - 1) * x ^ (n + 2) *
            (Real.sqrt (x - t ^ 2) / (2 * chordD t (Real.sqrt (x - t ^ 2)))) / geomS n x
            = (1 - x) ^ (n - 1) * x ^ (n + 2) *
                (Real.sqrt (x - t ^ 2) / (2 * chordD t (Real.sqrt (x - t ^ 2)) * geomS n x)) := by ring
        _ ≤ (1 - x) ^ (n - 1) * x ^ (n + 2) * (2 * Real.sqrt x / (9 * x)) :=
              mul_le_mul_of_nonneg_left (hdiv_le.trans hAMGM2)
                (mul_nonneg (pow_nonneg h1x _) (pow_nonneg hx.1 _))
        _ = t₁Fn x := by
              dsimp [t₁Fn]
              have hexp : n + 2 = (n + 1) + 1 := by omega
              rw [hexp, pow_succ]
              field_simp [hxpos.ne']
  have h1_lt_t1_mid : remH1 n t (1 / 2) < t₁Fn (1 / 2) := by
    unfold remH1
    have hxpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hsqrt_le : Real.sqrt (1 / 2 - t ^ 2) ≤ Real.sqrt (1 / 2) :=
      Real.sqrt_le_sqrt (by linarith [sq_nonneg t])
    have hD_ge : (2 + (1 / 2 : ℝ)) / 4 ≤ chordD t (Real.sqrt (1 / 2 - t ^ 2)) :=
      chordD_ge_two_add_x_div_four ht2 (by norm_num)
    have hAMGM : 9 * (1 / 2 : ℝ) < (2 + 1 / 2) * geomS n (1 / 2) :=
      two_add_x_mul_geom_gt_nine_x n (by omega) (by norm_num)
    have hS_ge1 : 1 ≤ geomS n (1 / 2) := geomS_ge_one n (by norm_num)
    have hD_pos : 0 < chordD t (Real.sqrt (1 / 2 - t ^ 2)) := by linarith
    have hsqrt_pos : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr hxpos
    have hdiv_le : Real.sqrt (1 / 2 - t ^ 2) / (2 * chordD t (Real.sqrt (1 / 2 - t ^ 2)) * geomS n (1 / 2)) ≤
        Real.sqrt (1 / 2) / ((2 + 1 / 2) / 2 * geomS n (1 / 2)) := by
      refine div_le_div₀ hsqrt_pos.le hsqrt_le (by positivity) ?_
      have : (2 + (1 / 2 : ℝ)) / 2 * geomS n (1 / 2) = 2 * ((2 + 1 / 2) / 4) * geomS n (1 / 2) := by ring
      rw [this]
      gcongr
    have hAMGM2 : Real.sqrt (1 / 2) / ((2 + 1 / 2) / 2 * geomS n (1 / 2)) <
        2 * Real.sqrt (1 / 2) / (9 * (1 / 2)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have : 0 < Real.sqrt (1 / 2) * ((2 + 1 / 2) * geomS n (1 / 2) - 9 * (1 / 2)) :=
        mul_pos hsqrt_pos (by linarith)
      linarith
    have hpow_pos : 0 < (1 - (1 / 2 : ℝ)) ^ (n - 1) * (1 / 2 : ℝ) ^ (n + 2) := by positivity
    calc
      (1 - (1 / 2 : ℝ)) ^ (n - 1) * (1 / 2 : ℝ) ^ (n + 2) *
          (Real.sqrt (1 / 2 - t ^ 2) / (2 * chordD t (Real.sqrt (1 / 2 - t ^ 2)))) / geomS n (1 / 2)
          = (1 - (1 / 2 : ℝ)) ^ (n - 1) * (1 / 2 : ℝ) ^ (n + 2) *
              (Real.sqrt (1 / 2 - t ^ 2) / (2 * chordD t (Real.sqrt (1 / 2 - t ^ 2)) * geomS n (1 / 2))) := by
                ring
      _ < (1 - (1 / 2 : ℝ)) ^ (n - 1) * (1 / 2 : ℝ) ^ (n + 2) * (2 * Real.sqrt (1 / 2) / (9 * (1 / 2))) :=
            mul_lt_mul_of_pos_left (hdiv_le.trans_lt hAMGM2) hpow_pos
      _ = t₁Fn (1 / 2) := by
            dsimp [t₁Fn]
            have hexp : n + 2 = (n + 1) + 1 := by omega
            rw [hexp, pow_succ]
            norm_num
            ring
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    zero_lt_one hh₁_cont ht₁_cont (fun x hx => h1_le_t1 x (Ioc_subset_Icc_self hx))
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, h1_lt_t1_mid⟩
  have ht1_val : (∫ x in (0 : ℝ)..1, t₁Fn x) = remTerm1 n := by
    unfold remTerm1 halfBeta
    dsimp [t₁Fn]
    rw [intervalIntegral.integral_const_mul]
  linarith

private theorem remH2_integral_le (n : ℕ) (hn : 4 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (∫ x in (0 : ℝ)..1, remH2 n t x) ≤ remTerm2 n := by
  have ht_m1 : -1 < t := by linarith
  have ht_lt1 : t < 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  let t₂Fn : ℝ → ℝ := fun x => (4 * ((n : ℝ) + 1) / 27) * ((1 - x) ^ (n - 2) * x ^ (n - 1) * Real.sqrt x)
  have ht₂_cont : ContinuousOn t₂Fn (Icc 0 1) :=
    (continuous_const.mul ((((continuous_const.sub continuous_id).pow (n - 2)).mul
      (continuous_pow (n - 1))).mul Real.continuous_sqrt)).continuousOn
  have hh₂_cont := remH2_continuousOn n ht_m1 ht_lt1
  have h2_le_t2 : ∀ x ∈ Icc (0 : ℝ) 1, remH2 n t x ≤ t₂Fn x := by
    intro x hx
    unfold remH2
    by_cases hxt : x ≤ t ^ 2
    · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
      simp only [mul_zero, zero_mul, zero_div]
      dsimp [t₂Fn]
      have h1x : 0 ≤ 1 - x := by linarith [hx.2]
      exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (pow_nonneg h1x _) (pow_nonneg hx.1 _))
        (Real.sqrt_nonneg x))
    · have hxpos : 0 < x := lt_of_le_of_lt (sq_nonneg t) (lt_of_not_ge hxt)
      have hsqrt_le : Real.sqrt (x - t ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith [sq_nonneg t])
      have hv2_eq : chordX t (Real.sqrt (x - t ^ 2)) = x := by
        unfold chordX
        rw [Real.sq_sqrt (by linarith)]
        ring
      have hD2_le : (1 - t ^ 2) / (chordD t (Real.sqrt (x - t ^ 2))) ^ 2 ≤ 12 / (2 + x) ^ 2 := by
        have h := one_sub_sq_div_chordD_sq_le (v := Real.sqrt (x - t ^ 2)) ht2
          (by rw [hv2_eq]; exact hx.1) (by rw [hv2_eq]; exact hx.2)
        rwa [hv2_eq] at h
      have hAMGM : 9 * x < (2 + x) * geomS n x := two_add_x_mul_geom_gt_nine_x n (by omega) hx.1
      have hS_ge1 : 1 ≤ geomS n x := geomS_ge_one n hx.1
      have h2x_pos : 0 < 2 + x := by linarith [hx.1]
      have hAMGM_sq : (81 : ℝ) * x ^ 2 ≤ ((2 + x) * geomS n x) ^ 2 := by
        have h9x_nonneg : 0 ≤ 9 * x := by linarith [hx.1]
        have heq1 : (81 : ℝ) * x ^ 2 = (9 * x) ^ 2 := by ring
        rw [heq1]
        exact pow_le_pow_left₀ h9x_nonneg hAMGM.le 2
      have hfrac_le : 12 / ((2 + x) * geomS n x) ^ 2 ≤ 12 / (81 * x ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hAMGM_sq
      have h1x : 0 ≤ 1 - x := by linarith [hx.2]
      have ht1_nonneg : 0 ≤ 1 - t ^ 2 := by nlinarith
      have hD_pos : 0 < chordD t (Real.sqrt (x - t ^ 2)) := chordD_pos ht_lt1 ht_m1 _
      have hexp1 : n + 1 = (n - 1) + 2 := by omega
      calc
        (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt (x - t ^ 2) *
            ((1 - t ^ 2) / (chordD t (Real.sqrt (x - t ^ 2))) ^ 2) / (geomS n x) ^ 2
            = (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt (x - t ^ 2) *
                (((1 - t ^ 2) / (chordD t (Real.sqrt (x - t ^ 2))) ^ 2) / (geomS n x) ^ 2) := by ring
        _ ≤ (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt x *
              ((12 / (2 + x) ^ 2) / (geomS n x) ^ 2) := by
              have hleft : (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt (x - t ^ 2) ≤
                  (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt x :=
                mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
              have hright : ((1 - t ^ 2) / (chordD t (Real.sqrt (x - t ^ 2))) ^ 2) / (geomS n x) ^ 2 ≤
                  (12 / (2 + x) ^ 2) / (geomS n x) ^ 2 :=
                div_le_div_of_nonneg_right hD2_le (sq_nonneg _)
              exact mul_le_mul hleft hright (by positivity) (by positivity)
        _ = (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt x *
              (12 / ((2 + x) * geomS n x) ^ 2) := by
              congr 1
              rw [div_div, ← mul_pow]
        _ ≤ (n + 1 : ℝ) * (1 - x) ^ (n - 2) * x ^ (n + 1) * Real.sqrt x * (12 / (81 * x ^ 2)) :=
              mul_le_mul_of_nonneg_left hfrac_le (by positivity)
        _ = t₂Fn x := by
              dsimp [t₂Fn]
              rw [hexp1, pow_add]
              field_simp [hxpos.ne']
              ring
  have hle : (∫ x in (0 : ℝ)..1, remH2 n t x) ≤ ∫ x in (0 : ℝ)..1, t₂Fn x :=
    intervalIntegral.integral_mono_on zero_le_one
      (hh₂_cont.intervalIntegrable_of_Icc zero_le_one)
      (ht₂_cont.intervalIntegrable_of_Icc zero_le_one) h2_le_t2
  have ht2_val : (∫ x in (0 : ℝ)..1, t₂Fn x) = remTerm2 n := by
    unfold remTerm2 halfBeta
    dsimp [t₂Fn]
    rw [intervalIntegral.integral_const_mul]
  exact hle.trans_eq ht2_val

theorem rem_integral_lt (n : ℕ) (hn : 4 ≤ n) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    ∫ v in (0 : ℝ)..Real.sqrt (1 - t ^ 2), remIntegrand n t v < remTerm1 n + remTerm2 n := by
  have h1 := remIntegrand_integral_le_g n hn ht0 (by linarith)
  have h2 := remG1_eq_remH1_integral n ht0.le ht1
  have h3 := remG2_eq_remH2_integral n ht0.le ht1
  have h4 := remH1_integral_lt n hn ht0.le ht1
  have h5 := remH2_integral_le n hn ht0.le ht1
  linarith

/-! ### Base case `n = 4` and induction for `n ≥ 4` -/

/-- Exact rational comparison for `n = 4`: `(T_1(4) + T_2(4))^2 < M_lb(4)^2`. -/
theorem rem_lt_main_four : remTerm1 4 + remTerm2 4 < mainTermLB 4 := by
  unfold remTerm1 remTerm2 mainTermLB
  rw [halfBeta_eq_rat, halfBeta_eq_rat, wallisI_eq_rat]
  simp only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  have hr : (2 / 9 : ℝ) * (halfBetaRat 3 5 : ℝ) + (4 * (4 + 1) / 27) * (halfBetaRat 2 3 : ℝ) =
      (((2 / 9 : ℚ) * halfBetaRat 3 5 + (20 / 27 : ℚ) * halfBetaRat 2 3 : ℚ) : ℝ) := by
    push_cast
    ring
  have hm : ((2 * (4 : ℝ) + 5) / (2 * ((4 : ℝ) + 3))) * (3 / 4 : ℝ) ^ 3 *
      (Real.sqrt 3 / 2) * (wallisIRat 4 : ℝ) =
      (((13 / 14 : ℚ) * (3 / 4 : ℚ) ^ 3 * (1 / 2 : ℚ) * wallisIRat 4 : ℚ) : ℝ) * Real.sqrt 3 := by
    push_cast
    norm_num
    ring
  rw [hr, hm]
  let r4 : ℚ := (2 / 9 : ℚ) * halfBetaRat 3 5 + (20 / 27 : ℚ) * halfBetaRat 2 3
  let m4 : ℚ := (13 / 14 : ℚ) * (3 / 4 : ℚ) ^ 3 * (1 / 2 : ℚ) * wallisIRat 4
  have hr4_pos : (0 : ℚ) < r4 := by norm_num [r4, halfBetaRat]
  have hm4_pos : (0 : ℚ) < m4 := by norm_num [m4, wallisIRat]
  have hsq : r4 ^ 2 < 3 * m4 ^ 2 := by
    norm_num [r4, m4, halfBetaRat, wallisIRat]
  have hsq_real : ((r4 : ℝ)) ^ 2 < ((m4 : ℝ) * Real.sqrt 3) ^ 2 := by
    have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    calc
      ((r4 : ℝ)) ^ 2 = ((r4 ^ 2 : ℚ) : ℝ) := by push_cast; ring
      _ < ((3 * m4 ^ 2 : ℚ) : ℝ) := by exact_mod_cast hsq
      _ = ((m4 : ℝ) * Real.sqrt 3) ^ 2 := by push_cast; rw [mul_pow, hs3]; ring
  have hm_pos : 0 ≤ (m4 : ℝ) * Real.sqrt 3 := by
    exact mul_nonneg (by exact_mod_cast hm4_pos.le) (Real.sqrt_nonneg 3)
  change (r4 : ℝ) < (m4 : ℝ) * Real.sqrt 3
  nlinarith

theorem mainTermLB_pos (n : ℕ) : 0 < mainTermLB n := by
  unfold mainTermLB
  have hI := wallisI_pos n
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  positivity

theorem remTerm1_pos (n : ℕ) : 0 < remTerm1 n := by
  unfold remTerm1
  have hB := halfBeta_pos (n - 1) (n + 1)
  positivity

theorem remTerm2_pos (n : ℕ) : 0 < remTerm2 n := by
  unfold remTerm2
  have hB := halfBeta_pos (n - 2) (n - 1)
  positivity

theorem mainTermLB_succ (n : ℕ) (hn : 1 ≤ n) :
    mainTermLB (n + 1) =
      (3 * ((n : ℝ) + 1) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) /
        (2 * ((n : ℝ) + 4) * (2 * (n : ℝ) + 5) ^ 2)) * mainTermLB n := by
  unfold mainTermLB
  rw [wallisI_succ]
  have hexp : (n + 1) - 1 = (n - 1) + 1 := by omega
  rw [hexp, pow_succ]
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have h4 : (n : ℝ) + 4 ≠ 0 := by positivity
  have h5 : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  push_cast
  field_simp [h3, h4, h5]
  ring

/-- Step ratio `r_1(n) = (T_1(n+1)/M_lb(n+1)) / (T_1(n)/M_lb(n)) < 1/2` for `n ≥ 4`. -/
theorem ratio1_succ_lt_half (n : ℕ) (hn : 4 ≤ n) :
    remTerm1 (n + 1) / mainTermLB (n + 1) < (1 / 2 : ℝ) * (remTerm1 n / mainTermLB n) := by
  have hM := mainTermLB_pos n
  have hT := remTerm1_pos n
  have hT_succ : remTerm1 (n + 1) =
      (2 * (n : ℝ) * (2 * (n : ℝ) + 5) / ((4 * (n : ℝ) + 5) * (4 * (n : ℝ) + 7))) * remTerm1 n := by
    unfold remTerm1
    have hp : (n + 1) - 1 = (n - 1) + 1 := by omega
    have hq : (n + 1) + 1 = (n + 1) + 1 := rfl
    rw [hp, hq, halfBeta_succ_both (n - 1) (n + 1)]
    have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      simp [Nat.cast_sub this]
    rw [hnm1]
    have h45 : 4 * (n : ℝ) + 5 ≠ 0 := by positivity
    have h47 : 4 * (n : ℝ) + 7 ≠ 0 := by positivity
    have he1 : 2 * ((n : ℝ) - 1) + 2 = 2 * (n : ℝ) := by ring
    have he2 : 2 * ((n : ℝ) + 1) + 3 = 2 * (n : ℝ) + 5 := by ring
    have he3 : 2 * ((n : ℝ) - 1) + 2 * ((n : ℝ) + 1) + 5 = 4 * (n : ℝ) + 5 := by ring
    have he4 : 2 * ((n : ℝ) - 1) + 2 * ((n : ℝ) + 1) + 7 = 4 * (n : ℝ) + 7 := by ring
    push_cast
    rw [he1, he2, he3, he4]
    ring
  rw [hT_succ, mainTermLB_succ n (by omega)]
  let r1 : ℝ :=
    (4 * (n : ℝ) * ((n : ℝ) + 4) * (2 * (n : ℝ) + 5) ^ 3) /
      (3 * ((n : ℝ) + 1) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) * (4 * (n : ℝ) + 5) * (4 * (n : ℝ) + 7))
  have hr1_eq :
      ((2 * (n : ℝ) * (2 * (n : ℝ) + 5) / ((4 * (n : ℝ) + 5) * (4 * (n : ℝ) + 7))) * remTerm1 n) /
        ((3 * ((n : ℝ) + 1) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) /
          (2 * ((n : ℝ) + 4) * (2 * (n : ℝ) + 5) ^ 2)) * mainTermLB n) =
      r1 * (remTerm1 n / mainTermLB n) := by
    dsimp [r1]
    have ha : (n : ℝ) + 1 ≠ 0 := by positivity
    have hb : (n : ℝ) + 3 ≠ 0 := by positivity
    have hc : (n : ℝ) + 4 ≠ 0 := by positivity
    have hd : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
    have he : 2 * (n : ℝ) + 7 ≠ 0 := by positivity
    have hf : 4 * (n : ℝ) + 5 ≠ 0 := by positivity
    have hg : 4 * (n : ℝ) + 7 ≠ 0 := by positivity
    field_simp [ha, hb, hc, hd, he, hf, hg, hM.ne']
    ring
  rw [hr1_eq]
  have hr1_lt : r1 < 1 / 2 := by
    let m : ℝ := (n : ℝ) - 4
    have hm : 0 ≤ m := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hn_eq : (n : ℝ) = m + 4 := by dsimp [m]; ring
    have hden_pos : 0 < 3 * ((n : ℝ) + 1) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) *
        (4 * (n : ℝ) + 5) * (4 * (n : ℝ) + 7) := by positivity
    dsimp [r1]
    rw [div_lt_iff₀ hden_pos]
    have hpoly :
        3 * ((n : ℝ) + 1) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) * (4 * (n : ℝ) + 5) * (4 * (n : ℝ) + 7) -
          2 * (4 * (n : ℝ) * ((n : ℝ) + 4) * (2 * (n : ℝ) + 5) ^ 3) =
        32 * m ^ 5 + 912 * m ^ 4 + 10354 * m ^ 3 + 58855 * m ^ 2 + 168954 * m + 198293 := by
      rw [hn_eq]
      ring
    have hpos_poly : 0 < 32 * m ^ 5 + 912 * m ^ 4 + 10354 * m ^ 3 +
        58855 * m ^ 2 + 168954 * m + 198293 := by positivity
    linarith
  have hpos_ratio : 0 < remTerm1 n / mainTermLB n := div_pos hT hM
  exact mul_lt_mul_of_pos_right hr1_lt hpos_ratio

/-- Step ratio `r_2(n) = (T_2(n+1)/M_lb(n+1)) / (T_2(n)/M_lb(n)) < 1/2` for `n ≥ 4`. -/
theorem ratio2_succ_lt_half (n : ℕ) (hn : 4 ≤ n) :
    remTerm2 (n + 1) / mainTermLB (n + 1) < (1 / 2 : ℝ) * (remTerm2 n / mainTermLB n) := by
  have hM := mainTermLB_pos n
  have hT := remTerm2_pos n
  have hT_succ : remTerm2 (n + 1) =
      (((n : ℝ) + 2) * (2 * ((n : ℝ) - 1)) * (2 * (n : ℝ) + 1) /
        (((n : ℝ) + 1) * (4 * (n : ℝ) - 1) * (4 * (n : ℝ) + 1))) * remTerm2 n := by
    unfold remTerm2
    have hp : (n + 1) - 2 = (n - 2) + 1 := by omega
    have hq : (n + 1) - 1 = (n - 1) + 1 := by omega
    rw [hp, hq, halfBeta_succ_both (n - 2) (n - 1)]
    have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      simp [Nat.cast_sub this]
    have hnm2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      have : 2 ≤ n := by omega
      simp [Nat.cast_sub this]
    rw [hnm1, hnm2]
    have he1 : 2 * ((n : ℝ) - 2) + 2 = 2 * ((n : ℝ) - 1) := by ring
    have he2 : 2 * ((n : ℝ) - 1) + 3 = 2 * (n : ℝ) + 1 := by ring
    have he3 : 2 * ((n : ℝ) - 2) + 2 * ((n : ℝ) - 1) + 5 = 4 * (n : ℝ) - 1 := by ring
    have he4 : 2 * ((n : ℝ) - 2) + 2 * ((n : ℝ) - 1) + 7 = 4 * (n : ℝ) + 1 := by ring
    rw [he1, he2, he3, he4]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : 4 * (n : ℝ) - 1 ≠ 0 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h3 : 4 * (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [h1, h2, h3]
    ring
  rw [hT_succ, mainTermLB_succ n (by omega)]
  let r2 : ℝ :=
    (4 * ((n : ℝ) + 2) * ((n : ℝ) - 1) * ((n : ℝ) + 4) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 5) ^ 2) /
      (3 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) * (4 * (n : ℝ) - 1) * (4 * (n : ℝ) + 1))
  have hr2_eq :
      ((((n : ℝ) + 2) * (2 * ((n : ℝ) - 1)) * (2 * (n : ℝ) + 1) /
          (((n : ℝ) + 1) * (4 * (n : ℝ) - 1) * (4 * (n : ℝ) + 1))) * remTerm2 n) /
        ((3 * ((n : ℝ) + 1) * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) /
          (2 * ((n : ℝ) + 4) * (2 * (n : ℝ) + 5) ^ 2)) * mainTermLB n) =
      r2 * (remTerm2 n / mainTermLB n) := by
    dsimp [r2]
    have ha : (n : ℝ) + 1 ≠ 0 := by positivity
    have hb : (n : ℝ) + 3 ≠ 0 := by positivity
    have hc : (n : ℝ) + 4 ≠ 0 := by positivity
    have hd : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
    have he : 2 * (n : ℝ) + 7 ≠ 0 := by positivity
    have hf : 4 * (n : ℝ) - 1 ≠ 0 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hg : 4 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [ha, hb, hc, hd, he, hf, hg, hM.ne']
    ring
  rw [hr2_eq]
  have hr2_lt : r2 < 1 / 2 := by
    let m : ℝ := (n : ℝ) - 4
    have hm : 0 ≤ m := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hn_eq : (n : ℝ) = m + 4 := by dsimp [m]; ring
    have h4m1_pos : 0 < 4 * (n : ℝ) - 1 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hden_pos : 0 < 3 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) *
        (4 * (n : ℝ) - 1) * (4 * (n : ℝ) + 1) := by positivity
    dsimp [r2]
    rw [div_lt_iff₀ hden_pos]
    have hpoly :
        3 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 3) * (2 * (n : ℝ) + 7) * (4 * (n : ℝ) - 1) * (4 * (n : ℝ) + 1) -
          2 * (4 * ((n : ℝ) + 2) * ((n : ℝ) - 1) * ((n : ℝ) + 4) * (2 * (n : ℝ) + 1) *
            (2 * (n : ℝ) + 5) ^ 2) =
        32 * m ^ 6 + 912 * m ^ 5 + 10458 * m ^ 4 + 61765 * m ^ 3 +
          199569 * m ^ 2 + 342243 * m + 255933 := by
      rw [hn_eq]
      ring
    have hpos_poly : 0 < 32 * m ^ 6 + 912 * m ^ 5 + 10458 * m ^ 4 + 61765 * m ^ 3 +
        199569 * m ^ 2 + 342243 * m + 255933 := by positivity
    linarith
  have hpos_ratio : 0 < remTerm2 n / mainTermLB n := div_pos hT hM
  exact mul_lt_mul_of_pos_right hr2_lt hpos_ratio

theorem rem_lt_main_of_ge_four (n : ℕ) (hn : 4 ≤ n) :
    remTerm1 n + remTerm2 n < mainTermLB n := by
  have hM := mainTermLB_pos n
  have hratio : remTerm1 n / mainTermLB n + remTerm2 n / mainTermLB n < 1 := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 4 := ⟨n - 4, by omega⟩
    clear hn hM
    induction m with
    | zero =>
      simp only [zero_add]
      have hM4 := mainTermLB_pos 4
      rw [← add_div, div_lt_one hM4]
      exact rem_lt_main_four
    | succ m ih =>
      have hm4 : 4 ≤ m + 4 := by omega
      have h1 := ratio1_succ_lt_half (m + 4) hm4
      have h2 := ratio2_succ_lt_half (m + 4) hm4
      have heq : (m + 1) + 4 = (m + 4) + 1 := by omega
      rw [heq]
      linarith
  rw [← add_div, div_lt_one hM] at hratio
  exact hratio

/-- Main theorem of Section 6: for all `n ≥ 4` and all `t ∈ (0, 1/2]`, the vertical-chord
integral `chordDeltaIntegral n t` is strictly positive. -/
theorem chordDeltaIntegral_pos_of_ge_four (n : ℕ) (hn : 4 ≤ n) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) :
    0 < chordDeltaIntegral n t := by
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 / 2 := ht.2
  have ht_lt1 : t < 1 := by linarith
  let a : ℝ := Real.sqrt (1 - t ^ 2)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by nlinarith)
  let mainFn : ℝ → ℝ := fun v => (1 - chordX t v) ^ n * (v ^ 2 / chordD t v)
  have hmain_cont : Continuous mainFn := by
    dsimp [mainFn]
    have hx : Continuous (chordX t) := by unfold chordX; exact continuous_const.add (continuous_pow 2)
    have hD : Continuous (chordD t) := by unfold chordD; exact continuous_const.add (continuous_const.mul (continuous_pow 2))
    exact ((continuous_const.sub hx).pow n).mul ((continuous_pow 2).div hD fun v =>
      (chordD_pos ht_lt1 (by linarith) v).ne')
  have hmain_int : IntervalIntegrable mainFn volume 0 a := hmain_cont.intervalIntegrable 0 a
  have hrem_lt := rem_integral_lt n hn ht0 ht1
  have hmain_ge := mainTerm_ge_lb n (by omega) ht0 ht1
  have hrem_lt_main := rem_lt_main_of_ge_four n hn
  have hrem_int : IntervalIntegrable (remIntegrand n t) volume 0 a :=
    remIntegrand_intervalIntegrable n (by omega) ht0.le ht_lt1
  have hchord_int : IntervalIntegrable (chordIntegrand n t) volume 0 a :=
    chordIntegrand_intervalIntegrable n (by omega) ht0.le ht_lt1
  have hmono : (∫ v in (0 : ℝ)..a, t * (mainFn v - remIntegrand n t v)) ≤
      ∫ v in (0 : ℝ)..a, chordIntegrand n t v := by
    apply integral_mono_on_of_le_Ioo ha_pos.le ((hmain_int.sub hrem_int).const_mul t) hchord_int
    intro v hv
    have hpt := chordIntegrand_ge n ht0 ht_lt1 hv.1 hv.2
    dsimp [mainFn, remIntegrand]
    linarith
  have hsplit : (∫ v in (0 : ℝ)..a, t * (mainFn v - remIntegrand n t v)) =
      t * ((∫ v in (0 : ℝ)..a, mainFn v) - (∫ v in (0 : ℝ)..a, remIntegrand n t v)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hmain_int hrem_int]
  have hint_pos : 0 < ∫ v in (0 : ℝ)..a, chordIntegrand n t v := by
    have h1 : 0 < t * ((∫ v in (0 : ℝ)..a, mainFn v) - (∫ v in (0 : ℝ)..a, remIntegrand n t v)) := by
      exact mul_pos ht0 (by linarith)
    linarith
  unfold chordDeltaIntegral
  exact mul_pos (div_pos (by norm_num) Real.pi_pos) hint_pos

theorem chordDelta_eq_chordDeltaIntegral (n : ℕ) (t : ℝ) :
    chordDelta n t = chordDeltaIntegral n t := rfl

theorem chordDelta_pos_of_ge_four (n : ℕ) (hn : 4 ≤ n) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) :
    0 < chordDelta n t :=
  chordDeltaIntegral_pos_of_ge_four n hn ht

end SharpL1.Analysis
