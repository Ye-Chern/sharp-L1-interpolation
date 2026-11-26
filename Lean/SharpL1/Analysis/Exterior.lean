import SharpL1.Analysis.Alternating
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar bounds on the exterior of the certificate region

These lemmas implement the decreasing node-speed factor argument in paper.tex,
section 7. The identification with the derivative of a moving node is separate.
-/

namespace SharpL1.Analysis

open Set

def speedDenominator (n : ℕ) (t y : ℝ) : ℝ :=
  n + 2 - 2 * (n + 1) * t * y + n * t ^ 2

noncomputable def speedFactor (n : ℕ) (t y : ℝ) : ℝ :=
  2 * (1 - y ^ 2) / speedDenominator n t y

theorem speedDenominator_decomposition (n : ℕ) (t y : ℝ) :
    speedDenominator n t y =
      (n + 1) * (1 - y ^ 2) + (n + 1) * (y - t) ^ 2 + 1 - t ^ 2 := by
  unfold speedDenominator
  ring

theorem speedDenominator_pos (n : ℕ) {t y : ℝ} (ht : |t| < 1) (hy : |y| ≤ 1) :
    0 < speedDenominator n t y := by
  have hty : 0 < 1 - t ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one t).2 ht)
  have hyy : 0 ≤ 1 - y ^ 2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one y).2 hy)
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [speedDenominator_decomposition]
  linarith [mul_nonneg hn hyy, mul_nonneg hn (sq_nonneg (y - t))]

theorem speedFactor_lt_one (n : ℕ) (hn : 1 ≤ n) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) : speedFactor n t y < 1 := by
  have hnn : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyy : 0 ≤ 1 - y ^ 2 := sub_nonneg.mpr ((sq_le_one_iff_abs_le_one y).2 hy)
  have hty : 0 < 1 - t ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one t).2 ht)
  rw [speedFactor, div_lt_one (speedDenominator_pos n ht hy), speedDenominator_decomposition]
  have hn' : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hnn) hyy, mul_nonneg hn' (sq_nonneg (y - t))]

/-- For positive interior t, the scalar speed factor decreases strictly as
the node moves through the interval [t,1]. -/
theorem speedFactor_strictAntiOn (n : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    StrictAntiOn (speedFactor n t) (Set.Icc t 1) := by
  intro y hy z hz hyz
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  have hy_abs : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hz_abs : |z| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hLy := speedDenominator_pos n ht_abs hy_abs
  have hLz := speedDenominator_pos n ht_abs hz_abs
  let c : ℝ := n + 2 + n * t ^ 2
  let b : ℝ := 2 * (n + 1) * t
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcb : 0 < c - b := by
    have hl : 0 < (n : ℝ) + 2 - n * t := by
      nlinarith [mul_nonneg hn (sub_nonneg.mpr ht1.le)]
    have hfactor := mul_pos (sub_pos.mpr ht1) hl
    dsimp [c, b]
    nlinarith only [hfactor]
  have hbt : 0 ≤ c - b * t := by
    have hh := mul_le_mul_of_nonneg_left ht1.le hb
    linarith
  have hbz : 0 ≤ c - b * z := by
    have hh := mul_le_mul_of_nonneg_left hz.2 hb
    linarith
  have hterm : 0 < 2 * t * (1 - t ^ 2) := by
    have hsq : 0 < 1 - t ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one t).2 ht_abs)
    positivity
  have hpositive : 0 < c * (y + z) - b * (1 + y * z) := by
    have heq : c * (y + z) - b * (1 + y * z) =
        2 * t * (1 - t ^ 2) + (z - t) * (c - b * t) + (y - t) * (c - b * z) := by
      dsimp [c, b]
      ring
    rw [heq]
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hterm
      (mul_nonneg (sub_nonneg.mpr hz.1) hbt)) (mul_nonneg (sub_nonneg.mpr hy.1) hbz)
  have hdiff : 2 * (1 - y ^ 2) * speedDenominator n t z -
      2 * (1 - z ^ 2) * speedDenominator n t y =
      2 * (z - y) * (c * (y + z) - b * (1 + y * z)) := by
    dsimp [speedDenominator, c, b]
    ring
  have hmul : 0 < 2 * (z - y) * (c * (y + z) - b * (1 + y * z)) := by positivity
  unfold speedFactor
  apply (div_lt_div_iff₀ hLz hLy).2
  exact sub_pos.mp (hdiff.symm ▸ hmul)

/-- Nonnegative weight in the alternating sum for the exterior derivative. -/
noncomputable def exteriorWeight (n : ℕ) (t y : ℝ) : ℝ :=
  if y < t then 0 else (y - t) ^ n * (1 - speedFactor n t y)

theorem exteriorWeight_nonneg (n : ℕ) (hn : 1 ≤ n) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) : 0 ≤ exteriorWeight n t y := by
  unfold exteriorWeight
  split
  · exact le_rfl
  · rename_i hyt
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr (le_of_not_gt hyt)) _)
      (sub_nonneg.mpr (speedFactor_lt_one n hn ht hy).le)

theorem exteriorWeight_monotoneOn (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    MonotoneOn (exteriorWeight n t) (Icc (-1) 1) := by
  intro y hy z hz hyz
  have ht' : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  by_cases hyt : y < t
  · rw [exteriorWeight, if_pos hyt]
    exact exteriorWeight_nonneg n hn ht' (abs_le.mpr hz)
  have hy' : t ≤ y := le_of_not_gt hyt
  have hz' : t ≤ z := hy'.trans hyz
  have hs := (speedFactor_strictAntiOn n ht ht1).antitoneOn ⟨hy', hy.2⟩ ⟨hz', hz.2⟩ hyz
  simp only [exteriorWeight, if_neg hyt, if_neg (not_lt_of_ge hz')]
  exact mul_le_mul
    (pow_le_pow_left₀ (sub_nonneg.mpr hy') (sub_le_sub_right hyz t) n)
    (sub_le_sub_left hs 1)
    (sub_nonneg.mpr (speedFactor_lt_one n hn ht' (abs_le.mpr hy)).le)
    (pow_nonneg (sub_nonneg.mpr hz') _)

/-- A nonnegative alternating contribution makes the exterior derivative
strictly negative on the open interval from 1/2 to 1. -/
theorem exterior_derivative_neg {n : ℕ} (hn : n ≠ 0) {t alt : ℝ}
    (ht : 1 / 2 < t) (ht1 : t < 1) (halt : 0 ≤ alt) :
    -1 + (2 * (1 - t)) ^ n - (2 : ℝ) ^ (n + 1) * alt < 0 := by
  have hpow := pow_lt_one₀ (by linarith : 0 ≤ 2 * (1 - t)) (by linarith) hn
  linarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1)) halt]

/-- The exterior node weights have a nonnegative alternating sum when the
nodes are listed in increasing order. -/
theorem exteriorWeight_alternating_nonneg (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (nodes : List ℝ)
    (hord : nodes.Pairwise (· ≤ ·)) (hbounded : ∀ y ∈ nodes, y ∈ Icc (-1) 1) :
    0 ≤ (nodes.map (exteriorWeight n t)).foldl (fun acc weight => weight - acc) 0 := by
  apply foldl_alternating_nonneg
  · rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun hy hz hyz =>
      exteriorWeight_monotoneOn n hn ht ht1 (hbounded _ hy) (hbounded _ hz) hyz) hord
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    exact exteriorWeight_nonneg n hn (abs_lt.mpr ⟨by linarith, ht1⟩) (abs_le.mpr (hbounded _ hy))

end SharpL1.Analysis
