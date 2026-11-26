module

public import SharpL1.Certificate.CDF
public import SharpL1.Certificate.CDFSigns
public import SharpL1.Certificate.RootRow
public import SharpL1.Certificate.Intervals

public section

/-!
# Executable finite interval certificate checker

A row carries the grid parameter T followed by the descending root brackets.
The order is supplied by the enclosing group of rows.
-/

namespace SharpL1.Certificate

structure Row where
  t : ℤ
  brackets : List (ℤ × ℤ)
  deriving Repr

@[expose] def gridScale : ℤ := 2 ^ 55

@[expose] def originGrid : ℤ := gridScale / 2 ^ 24

@[expose] def outerGrid : ℤ := gridScale / 2

structure Endpoint where
  row : Row
  lower : Signs ℤ
  upper : Signs ℤ
  deriving Repr

/-- Convert descending root brackets into ascending coefficient bounds. -/
@[expose] def coefficientLower (row : Row) : List ℤ :=
  row.brackets.map fun bracket => row.t - bracket.2

@[expose] def coefficientUpper (row : Row) : List ℤ :=
  row.brackets.map fun bracket => row.t - bracket.1

/-- The four coefficient lists entering H′, using exactly the same core. -/
@[expose] def evalAugmentations (cdf : List ℤ → ℤ) (s t : ℤ) (core : List ℤ) : Signs ℤ :=
  let left := t - s
  let right := t + s
  let sign := fun knots => cdfToSign s (cdf knots)
  ⟨sign core, sign (core ++ [right]), sign (left :: core), sign (left :: core ++ [right])⟩

@[expose] def evaluate (row : Row) : Endpoint :=
  ⟨row,
    evalAugmentations (cdfUpper gridScale) gridScale row.t (coefficientLower row),
    evalAugmentations (cdfLower gridScale) gridScale row.t (coefficientUpper row)⟩

@[expose] def checkEndpoint (n : ℕ) (p : Endpoint) : Bool :=
  decide (0 < p.row.t ∧ p.row.t ≤ outerGrid) &&
    checkRootRow gridScale p.row.t (n - 1) p.row.brackets &&
    decide (p.lower.core ≤ p.upper.core ∧ p.lower.plus ≤ p.upper.plus ∧
      p.lower.minus ≤ p.upper.minus ∧ p.lower.both ≤ p.upper.both)

@[expose] def checkTailTo (n : ℕ) (finish : ℤ) (previous : Endpoint) : List Endpoint → Bool
  | [] => decide (previous.row.t = finish)
  | current :: rest =>
    (decide (previous.row.t < current.row.t ∧ 0 < intervalMargin n previous.lower current.upper) &&
      checkEndpoint n current) && checkTailTo n finish current rest

@[expose] def checkStart (n : ℕ) (row : Row) : Bool :=
  let first := evaluate row
  (decide (3 ≤ n ∧ n ≤ 19 ∧ row.t = originGrid) && checkEndpoint n first) &&
    checkOrigin n gridScale row.t first.lower first.upper

@[expose] def checkOrder (n : ℕ) : List Row → Bool
  | [] => false
  | first :: rest =>
    checkStart n first && checkTailTo n outerGrid (evaluate first) (rest.map evaluate)

private theorem checkTailTo_append (n : ℕ) (finish : ℤ) (p : Endpoint)
    (xs ys : List Endpoint)
    (hxs : checkTailTo n (xs.getLastD p).row.t p xs = true)
    (hys : checkTailTo n finish (xs.getLastD p) ys = true) :
    checkTailTo n finish p (xs ++ ys) = true := by
  induction xs generalizing p with
  | nil => exact hys
  | cons q xs ih =>
    simp only [List.getLastD_cons, List.cons_append, checkTailTo, Bool.and_eq_true] at hxs hys ⊢
    exact ⟨hxs.1, ih q hxs.2 hys⟩

/-- Local pieces have their own kernel checks, then their certified endpoints
are identified to make a single partition. -/
inductive CheckedChunks (n : ℕ) : Row → List (List Row) → Prop
  | last {p : Row} (h : p.t = outerGrid) : CheckedChunks n p []
  | next {p : Row} {chunk : List Row} {rest : List (List Row)}
      (h : checkTailTo n (chunk.getLastD p).t (evaluate p) (chunk.map evaluate) = true)
      (tail : CheckedChunks n (chunk.getLastD p) rest) :
      CheckedChunks n p (chunk :: rest)

private theorem CheckedChunks.tailCheck {n : ℕ} {p : Row} {sections : List (List Row)}
    (h : CheckedChunks n p sections) :
    checkTailTo n outerGrid (evaluate p) (sections.flatten.map evaluate) = true := by
  induction h with
  | last ht => simp [checkTailTo, evaluate, ht]
  | @next p chunk rest hstep _ ih =>
    simp only [List.flatten_cons, List.map_append]
    apply checkTailTo_append
    · rw [List.getLastD_map]
      exact hstep
    · simpa only [List.getLastD_map] using ih

theorem checkOrder_of_chunks (n : ℕ) (first : Row) (sections : List (List Row))
    (hfirst : checkStart n first = true) (htail : CheckedChunks n first sections) :
    checkOrder n (first :: sections.flatten) = true := by
  simp only [checkOrder, Bool.and_eq_true]
  exact ⟨hfirst, htail.tailCheck⟩

/-- Checked root isolation and consistency of all four endpoint enclosures. -/
structure ValidEndpoint (n : ℕ) (p : Endpoint) : Prop where
  positive : 0 < p.row.t
  bounded : p.row.t ≤ outerGrid
  brackets : checkRootRow gridScale p.row.t (n - 1) p.row.brackets = true
  consistent : p.lower.core ≤ p.upper.core ∧ p.lower.plus ≤ p.upper.plus ∧
    p.lower.minus ≤ p.upper.minus ∧ p.lower.both ≤ p.upper.both

theorem checkEndpoint_sound (n : ℕ) (p : Endpoint) (h : checkEndpoint n p = true) :
    ValidEndpoint n p := by
  simp only [checkEndpoint, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A chain with validated endpoints and a strictly positive margin on every
adjacent interval. The head endpoint is supplied by its caller. -/
inductive ValidTail (n : ℕ) : Endpoint → List Endpoint → Prop
  | last {p : Endpoint} (h : p.row.t = outerGrid) : ValidTail n p []
  | step {p q : Endpoint} {rest : List Endpoint}
      (ordered : p.row.t < q.row.t)
      (margin : 0 < intervalMargin n p.lower q.upper)
      (valid : ValidEndpoint n q)
      (tail : ValidTail n q rest) : ValidTail n p (q :: rest)

theorem checkTail_sound (n : ℕ) (first : Endpoint) (rest : List Endpoint)
    (h : checkTailTo n outerGrid first rest = true) : ValidTail n first rest := by
  induction rest generalizing first with
  | nil =>
    exact .last (of_decide_eq_true h)
  | cons next rest ih =>
    simp only [checkTailTo, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .step h.1.1.1 h.1.1.2 (checkEndpoint_sound n next h.1.2) (ih next h.2)

/-- Any point after the initial endpoint and at or before the final endpoint
lies in a certified adjacent interval. Parameters are measured in grid units. -/
theorem ValidTail.covers {n : ℕ} {first : Endpoint} {rest : List Endpoint}
    (h : ValidTail n first rest) (z : ℝ)
    (hfirst : (first.row.t : ℝ) < z) (hlast : z ≤ (outerGrid : ℝ)) :
    ∃ p ∈ first :: rest, ∃ q ∈ rest, (p.row.t : ℝ) ≤ z ∧ z ≤ (q.row.t : ℝ) ∧
      0 < intervalMargin n p.lower q.upper := by
  induction h with
  | last ht =>
    exact False.elim ((hfirst.not_ge) (by simpa [ht] using hlast))
  | @step p q tail _ margin _ _ ih =>
    by_cases hz : z ≤ (q.row.t : ℝ)
    · exact ⟨p, by simp, q, by simp, hfirst.le, hz, margin⟩
    · obtain ⟨a, ha, b, hb, haz, hzb, ham⟩ := ih (lt_of_not_ge hz)
      exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, haz, hzb, ham⟩

theorem checkOrder_sound (n : ℕ) (rows : List Row) (h : checkOrder n rows = true) :
    3 ≤ n ∧ n ≤ 19 ∧
    ∃ first rest, rows.map evaluate = first :: rest ∧ first.row.t = originGrid ∧
      ValidEndpoint n first ∧ checkOrigin n gridScale first.row.t first.lower first.upper = true ∧
      ValidTail n first rest := by
  cases rows with
  | nil => simp [checkOrder] at h
  | cons row rows =>
    simp only [checkOrder, checkStart, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1, h.1.1.1.2.1, evaluate row, rows.map evaluate, rfl,
      h.1.1.1.2.2, checkEndpoint_sound n (evaluate row) h.1.1.2, h.1.2,
      checkTail_sound n (evaluate row) (rows.map evaluate) h.2⟩

end SharpL1.Certificate
