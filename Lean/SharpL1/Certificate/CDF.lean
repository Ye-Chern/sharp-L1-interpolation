module

public import SharpL1.Certificate.Rounding

public section

/-!
# Triangular CDF recurrence and directed enclosure

The exact real recurrence and each integer recurrence traverse the same rows.
Each update reads two adjacent entries of the previous row. The sign branches
also specify the CDF convention for the all-zero subarray.
-/

namespace SharpL1.Certificate

@[expose] noncomputable def cdfMixed (l h : ℤ) (x y : ℝ) : ℝ :=
  (-(l : ℝ) * x + (h : ℝ) * y) / ((h : ℝ) - l)

private theorem scaledAverage_eq (s l h : ℤ) (x y : ℝ) :
    scaledAverage s l h x y = (s : ℝ) * cdfMixed l h x y := by
  rw [scaledAverage, cdfMixed, mul_div_assoc]

/-- Compute one row from adjacent entries of the previous row. -/
@[expose] def cdfEntries {α : Type} (zero one : α) (mix : ℤ → ℤ → α → α → α) :
    List ℤ → List ℤ → List α → List α
  | l :: lows, h :: highs, x :: y :: values =>
    (if h ≤ 0 then one else if 0 ≤ l then zero else mix l h x y) ::
      cdfEntries zero one mix lows highs (y :: values)
  | _, _, _ => []

/-- Advance the table by the indicated number of rows. -/
@[expose] def cdfRows {α : Type} (zero one : α) (mix : ℤ → ℤ → α → α → α)
    (knots : List ℤ) (gap : ℕ) (values : List α) : ℕ → List α
  | 0 => values
  | count + 1 =>
    cdfRows zero one mix knots (gap + 1)
      (cdfEntries zero one mix knots (knots.drop (gap + 1)) values) count

/-- Run the shared arithmetic table from singleton entries. -/
@[expose] def cdfRun {α : Type} (zero one : α) (mix : ℤ → ℤ → α → α → α)
    (knots : List ℤ) : α :=
  (cdfRows zero one mix knots 0 (knots.map fun x => if x ≤ 0 then one else zero)
    (knots.length - 1)).headD zero

/-- The real-valued recurrence, with CDF evaluated at zero. -/
@[expose] noncomputable def cdfExact (knots : List ℤ) : ℝ :=
  cdfRun 0 1 cdfMixed knots

/-- Lower directed enclosure in units of 1/s. -/
@[expose] def cdfLower (s : ℤ) (knots : List ℤ) : ℤ :=
  cdfRun 0 s lowerUpdate knots

/-- Upper directed enclosure in units of 1/s. -/
@[expose] def cdfUpper (s : ℤ) (knots : List ℤ) : ℤ :=
  cdfRun 0 s upperUpdate knots

private theorem cdfRun_rel {α β : Type} (R : α → β → Prop)
    (za oa : α) (zb ob : β) (ma : ℤ → ℤ → α → α → α) (mb : ℤ → ℤ → β → β → β)
    (hz : R za zb) (ho : R oa ob)
    (hm : ∀ l h x y x' y', l < 0 → 0 < h → R x x' → R y y' →
      R (ma l h x y) (mb l h x' y'))
    (knots : List ℤ) :
    R (cdfRun za oa ma knots) (cdfRun zb ob mb knots) := by
  have hentries (ls hs : List ℤ) (xs : List α) (ys : List β) (hxy : List.Forall₂ R xs ys) :
      List.Forall₂ R (cdfEntries za oa ma ls hs xs) (cdfEntries zb ob mb ls hs ys) := by
    induction ls generalizing hs xs ys with
    | nil => simp [cdfEntries]
    | cons l ls ih =>
      cases hs with
      | nil => simp [cdfEntries]
      | cons h hs =>
        cases hxy with
        | nil => simp [cdfEntries]
        | @cons x x' xs ys hx hrel =>
          cases hrel with
          | nil => simp [cdfEntries]
          | @cons y y' xs ys hy hrest =>
            simp only [cdfEntries]
            refine .cons ?_ (ih hs _ _ (.cons hy hrest))
            by_cases hh : h ≤ 0
            · simpa [hh] using ho
            · by_cases hl : 0 ≤ l
              · simpa [hh, hl] using hz
              · simpa [hh, hl] using hm l h x y x' y' (lt_of_not_ge hl) (lt_of_not_ge hh) hx hy
  have hrows (count gap : ℕ) (xs : List α) (ys : List β) (hxy : List.Forall₂ R xs ys) :
      List.Forall₂ R (cdfRows za oa ma knots gap xs count) (cdfRows zb ob mb knots gap ys count) := by
    induction count generalizing gap xs ys with
    | zero => exact hxy
    | succ count ih =>
      exact ih (gap + 1) _ _ (hentries knots (knots.drop (gap + 1)) xs ys hxy)
  have hleaves (ks : List ℤ) : List.Forall₂ R
      (ks.map fun x => if x ≤ 0 then oa else za)
      (ks.map fun x => if x ≤ 0 then ob else zb) := by
    induction ks with
    | nil => exact .nil
    | cons l ls ih =>
      refine .cons ?_ ih
      by_cases hl : l ≤ 0
      · simpa [hl] using ho
      · simpa [hl] using hz
  have hhead (xs : List α) (ys : List β) (h : List.Forall₂ R xs ys) :
      R (xs.headD za) (ys.headD zb) := by
    cases h with
    | nil => exact hz
    | cons hx _ => exact hx
  exact hhead _ _ (hrows (knots.length - 1) 0 _ _ (hleaves knots))

/-- Every lower update and the exact recurrence maintain their ordering. -/
theorem cdfLower_sound (s : ℤ) (knots : List ℤ) :
    (cdfLower s knots : ℝ) ≤ (s : ℝ) * cdfExact knots := by
  apply cdfRun_rel (α := ℤ) (β := ℝ) (fun x y => (x : ℝ) ≤ (s : ℝ) * y) 0 s 0 1 lowerUpdate cdfMixed
  · simp
  · simp
  · intro l h x y x' y' hl hh hx hy
    simpa [scaledAverage_eq] using lowerUpdate_sound s l h x y x' y' hl hh hx hy

/-- Every upper update and the exact recurrence maintain their ordering. -/
theorem cdfUpper_sound (s : ℤ) (knots : List ℤ) :
    (s : ℝ) * cdfExact knots ≤ (cdfUpper s knots : ℝ) := by
  apply cdfRun_rel (α := ℝ) (β := ℤ) (fun x y => (s : ℝ) * x ≤ (y : ℝ)) 0 1 0 s cdfMixed upperUpdate
  · simp
  · simp
  · intro l h x y x' y' hl hh hx hy
    simpa [scaledAverage_eq] using upperUpdate_sound s l h x' y' x y hl hh hx hy

end SharpL1.Certificate
