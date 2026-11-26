import SharpL1.Certificate.CDF
import SharpL1.Probability.WeightedExponential

/-! ## Probability semantics of the exact arithmetic table -/

namespace SharpL1.Certificate

private lemma cdfEntries_getElem? {α : Type} (zero one : α) (mix : ℤ → ℤ → α → α → α)
    (ls hs : List ℤ) (vs : List α) (i : ℕ) :
    (cdfEntries zero one mix ls hs vs)[i]? =
      match ls[i]?, hs[i]?, vs[i]?, vs[i + 1]? with
      | some l, some h, some x, some y =>
          some (if h ≤ 0 then one else if 0 ≤ l then zero else mix l h x y)
      | _, _, _, _ => none := by
  induction i generalizing ls hs vs with
  | zero =>
    cases ls with
    | nil => simp [cdfEntries]
    | cons l ls' =>
      cases hs with
      | nil => simp [cdfEntries]
      | cons h hs' =>
        cases vs with
        | nil => simp [cdfEntries]
        | cons x vs' =>
          cases vs' with
          | nil => simp [cdfEntries]
          | cons y ys' => simp [cdfEntries]
  | succ i ih =>
    cases ls with
    | nil => simp [cdfEntries]
    | cons l ls' =>
      cases hs with
      | nil => simp [cdfEntries]
      | cons h hs' =>
        cases vs with
        | nil => simp [cdfEntries]
        | cons x vs' =>
          cases vs' with
          | nil => simp [cdfEntries]
          | cons y ys' =>
            simpa [cdfEntries] using ih ls' hs' (y :: ys')

private def RowSpec (knots : List ℤ) (gap : ℕ) (values : List ℝ) : Prop :=
  ∀ i : ℕ,
    values[i]? =
      if i + gap < knots.length then
        some (Probability.weightedCdfZero
          (((knots.drop i).take (gap + 1)).map (fun x : ℤ => (x : ℝ))))
      else
        none

private lemma rowSpec_init (knots : List ℤ) :
    RowSpec knots 0 (knots.map fun x => if x ≤ 0 then (1 : ℝ) else 0) := by
  intro i
  by_cases hi : i < knots.length
  · have htake : (knots.drop i).take 1 = [knots[i]] := by
      rw [List.drop_eq_getElem_cons hi, show (1 : ℕ) = 0 + 1 by rfl,
        List.take_succ_cons, List.take_zero]
    simp only [hi, Nat.add_zero, ↓reduceIte, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, htake, List.map_cons, List.map_nil]
    congr 1
    by_cases hle : knots[i] ≤ 0
    · rw [if_pos hle]
      symm
      apply Probability.weightedCdfZero_nonpos
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact Int.cast_nonpos.mpr hle
    · rw [if_neg hle]
      have hpos : (0 : ℝ) < (knots[i] : ℝ) := Int.cast_pos.mpr (lt_of_not_ge hle)
      symm
      apply Probability.weightedCdfZero_nonneg_pos
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact hpos.le
      · exact ⟨(knots[i] : ℝ), by simp, hpos⟩
  · simp [hi]

private lemma rowSpec_step (knots : List ℤ) (hk : knots.Pairwise (· ≤ ·))
    (gap : ℕ) (values : List ℝ) (hv : RowSpec knots gap values) :
    RowSpec knots (gap + 1) (cdfEntries 0 1 cdfMixed knots (knots.drop (gap + 1)) values) := by
  intro i
  rw [cdfEntries_getElem?]
  by_cases hi : i + (gap + 1) < knots.length
  · have hi0 : i < knots.length := by omega
    have hi' : i + gap + 1 < knots.length := by omega
    have hig : i + gap < knots.length := by omega
    have hi1g : (i + 1) + gap < knots.length := by omega
    have hidrop : (knots.drop (gap + 1))[i]? = some knots[i + gap + 1] := by
      rw [List.getElem?_drop, show gap + 1 + i = i + gap + 1 by omega,
        List.getElem?_eq_getElem hi']
    have hvi : values[i]? = some (Probability.weightedCdfZero
        (((knots.drop i).take (gap + 1)).map (fun x : ℤ => (x : ℝ)))) := by
      simpa [hig] using hv i
    have hvi1 : values[i + 1]? = some (Probability.weightedCdfZero
        (((knots.drop (i + 1)).take (gap + 1)).map (fun x : ℤ => (x : ℝ)))) := by
      simpa [hi1g] using hv (i + 1)
    rw [List.getElem?_eq_getElem hi0, hidrop, hvi, hvi1]
    simp only [hi, ↓reduceIte]
    congr 1
    set l : ℤ := knots[i]
    set h : ℤ := knots[i + gap + 1]
    set mid : List ℤ := (knots.drop (i + 1)).take gap
    have hleft : (knots.drop i).take (gap + 1) = l :: mid := by
      rw [List.drop_eq_getElem_cons hi0, List.take_succ_cons]
    have hright : (knots.drop (i + 1)).take (gap + 1) = mid ++ [h] := by
      have hdrop1 : (knots.drop (i + 1))[gap]? = some h := by
        rw [List.getElem?_drop, show i + 1 + gap = i + gap + 1 by omega,
          List.getElem?_eq_getElem hi']
      rw [List.take_add_one, hdrop1]
      rfl
    have hfull : (knots.drop i).take (gap + 2) = l :: (mid ++ [h]) := by
      rw [List.drop_eq_getElem_cons hi0, List.take_succ_cons, hright]
    have hpw : (l :: (mid ++ [h])).Pairwise (· ≤ ·) :=
      hfull ▸ hk.drop.take
    have hcons := List.pairwise_cons.mp hpw
    have happ := List.pairwise_append.mp hcons.2
    have hl_le : ∀ x ∈ l :: (mid ++ [h]), l ≤ x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_rfl
      · exact hcons.1 x hx
    have h_le_h : ∀ x ∈ l :: (mid ++ [h]), x ≤ h := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hcons.1 h (by simp)
      · rcases List.mem_append.mp hx with hx | hx
        · exact happ.2.2 x hx h (by simp)
        · simp only [List.mem_singleton] at hx
          subst hx
          exact le_rfl
    rw [show (gap + 1) + 1 = gap + 2 by omega, hfull]
    by_cases hh : h ≤ 0
    · rw [if_pos hh]
      symm
      apply Probability.weightedCdfZero_nonpos
      intro c hc
      simp only [List.mem_map] at hc
      rcases hc with ⟨x, hx, rfl⟩
      exact Int.cast_nonpos.mpr ((h_le_h x hx).trans hh)
    · rw [if_neg hh]
      by_cases hl : 0 ≤ l
      · rw [if_pos hl]
        symm
        apply Probability.weightedCdfZero_nonneg_pos
        · intro c hc
          simp only [List.mem_map] at hc
          rcases hc with ⟨x, hx, rfl⟩
          exact_mod_cast hl.trans (hl_le x hx)
        · refine ⟨(h : ℝ), List.mem_map.mpr ⟨h, by simp, rfl⟩, ?_⟩
          exact Int.cast_pos.mpr (lt_of_not_ge hh)
      · rw [if_neg hl]
        have hl_lt : (l : ℝ) < 0 := Int.cast_lt_zero.mpr (lt_of_not_ge hl)
        have hh_gt : (0 : ℝ) < (h : ℝ) := Int.cast_pos.mpr (lt_of_not_ge hh)
        rw [hleft, hright]
        simp only [List.map_cons, List.map_append, List.map_nil]
        rw [Probability.weightedCdfZero_mixed hl_lt hh_gt (mid.map (fun x : ℤ => (x : ℝ))),
          cdfMixed]
  · have hi1g : ¬ (i + 1) + gap < knots.length := by omega
    have hvi1 : values[i + 1]? = none := by
      simpa [hi1g] using hv (i + 1)
    simp [hi, hvi1]

private lemma rowSpec_cdfRows (knots : List ℤ) (hk : knots.Pairwise (· ≤ ·)) :
    ∀ (count gap : ℕ) (values : List ℝ),
      RowSpec knots gap values →
      RowSpec knots (gap + count) (cdfRows 0 1 cdfMixed knots gap values count) := by
  intro count
  induction count with
  | zero =>
    intro gap values hv
    simpa [cdfRows] using hv
  | succ count ih =>
    intro gap values hv
    simpa [cdfRows, Nat.add_assoc, Nat.add_comm 1 count] using
      ih (gap + 1) (cdfEntries 0 1 cdfMixed knots (knots.drop (gap + 1)) values)
        (rowSpec_step knots hk gap values hv)

/-- On the empty knot list, `cdfExact` returns the checker default `0`
(whereas `weightedCdfZero [] = 1`). -/
theorem cdfExact_nil : cdfExact [] = 0 := by
  simp [cdfExact, cdfRun, cdfRows]

/-- The exact triangular CDF recurrence equals the closed zero-threshold CDF of
the corresponding weighted exponential sum for any nonempty nondecreasing knot list. -/
theorem cdfExact_eq_weightedCdfZero (knots : List ℤ) (hne : knots ≠ [])
    (hord : knots.Pairwise (· ≤ ·)) :
    cdfExact knots = Probability.weightedCdfZero (knots.map (fun x : ℤ => (x : ℝ))) := by
  have hpos : 0 < knots.length := List.length_pos_of_ne_nil hne
  have hrow := rowSpec_cdfRows knots hord (knots.length - 1) 0
    (knots.map fun x => if x ≤ 0 then (1 : ℝ) else 0) (rowSpec_init knots)
  have h0 := hrow 0
  have hlen : 0 + (0 + (knots.length - 1)) < knots.length := by omega
  have htake : (knots.drop 0).take (0 + (knots.length - 1) + 1) = knots := by
    simp [Nat.sub_add_cancel hpos]
  simp only [hlen, ↓reduceIte, htake] at h0
  change (cdfRows 0 1 cdfMixed knots 0
    (knots.map fun x => if x ≤ 0 then (1 : ℝ) else 0) (knots.length - 1)).headD 0 = _
  cases hres : cdfRows 0 1 cdfMixed knots 0
      (knots.map fun x => if x ≤ 0 then (1 : ℝ) else 0) (knots.length - 1) with
  | nil => simp [hres] at h0
  | cons a as =>
    rw [hres] at h0
    simpa using Option.some.inj h0

end SharpL1.Certificate
