/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.RotationCertificate
public import ErdosOverlap.Numerics.FourierPolynomial

/-!
# Row-oriented exact rotation-grid certificates

Every row stores one integer pair per cosine term. The recursive checks reject
every length mismatch, inspect each adjacent state only once, and establish
semantic correctness independently of how the row-indexing function is stored.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def initialRowCheck : List (CosineTerm × RotationSeed) → List (ℤ × ℤ) → Bool
  | [], [] => true
  | (_, seed) :: seeds, state :: row =>
      decide (state = seed.initial) && initialRowCheck seeds row
  | _, _ => false

@[expose] def transitionRowCheck :
    List (CosineTerm × RotationSeed) → List (ℤ × ℤ) → List (ℤ × ℤ) → Bool
  | [], [], [] => true
  | (_, seed) :: seeds, previous :: prev, next :: rest =>
      decide (next = rotationStep seed.step.1 seed.step.2 previous) &&
        transitionRowCheck seeds prev rest
  | _, _, _ => false

@[expose] def rotationSeedsCheck (seeds : List (CosineTerm × RotationSeed)) : Bool :=
  seeds.all (fun p => p.2.check p.1.frequency)

@[expose] def RowCorrect (seeds : List (CosineTerm × RotationSeed))
    (row : List (ℤ × ℤ)) (j : ℕ) : Prop :=
  List.Forall₂ (fun p state =>
    state = rotationIter p.2.step.1 p.2.step.2 p.2.initial j) seeds row

@[expose] noncomputable def RowTrigCorrect (terms : List CosineTerm)
    (row : List (ℤ × ℤ)) (j : ℕ) : Prop :=
  List.Forall₂ (fun term state =>
    Real.cos ((term.frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ) ∈
      rotationCoordinateBox state.1 (rotationRadius rotationSeedError rotationSeedError j) ∧
    Real.sin ((term.frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ) ∈
      rotationCoordinateBox state.2 (rotationRadius rotationSeedError rotationSeedError j)) terms row

theorem initialRowCheck_sound {seeds : List (CosineTerm × RotationSeed)}
    {row : List (ℤ × ℤ)} (h : initialRowCheck seeds row = true) : RowCorrect seeds row 0 := by
  induction seeds generalizing row with
  | nil =>
    cases row with
    | nil => exact List.Forall₂.nil
    | cons state rest => simp [initialRowCheck] at h
  | cons p seeds ih =>
    cases row with
    | nil => simp [initialRowCheck] at h
    | cons state rest =>
      rcases p with ⟨term, seed⟩
      simp only [initialRowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      exact List.Forall₂.cons h.1 (ih h.2)

theorem transitionRowCheck_sound {seeds : List (CosineTerm × RotationSeed)}
    {previous next : List (ℤ × ℤ)} {j : ℕ}
    (hprev : RowCorrect seeds previous j) (h : transitionRowCheck seeds previous next = true) :
    RowCorrect seeds next (j + 1) := by
  unfold RowCorrect at hprev ⊢
  induction hprev generalizing next with
  | nil =>
    cases next with
    | nil => exact List.Forall₂.nil
    | cons state rest => simp [transitionRowCheck] at h
  | @cons p state seeds previous hstate htail ih =>
    cases next with
    | nil => simp [transitionRowCheck] at h
    | cons next rest =>
      rcases p with ⟨term, seed⟩
      simp only [transitionRowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      apply List.Forall₂.cons
      · change next = rotationIter seed.step.1 seed.step.2 seed.initial (j + 1)
        rw [h.1, hstate]
        rfl
      · exact ih h.2

theorem RowCorrect.length_eq {seeds : List (CosineTerm × RotationSeed)}
    {row : List (ℤ × ℤ)} {j : ℕ} (h : RowCorrect seeds row j) :
    seeds.length = row.length := List.Forall₂.length_eq h

/-- Initial correctness and every preceding transition certify any finite grid prefix. -/
theorem rowCorrect_of_checked_transitions (seeds : List (CosineTerm × RotationSeed))
    (rows : ℕ → List (ℤ × ℤ)) (n : ℕ)
    (hzero : initialRowCheck seeds (rows 0) = true)
    (htransition : ∀ j, j + 1 < n → transitionRowCheck seeds (rows j) (rows (j + 1)) = true)
    {j : ℕ} (hj : j < n) : RowCorrect seeds (rows j) j := by
  induction j with
  | zero => exact initialRowCheck_sound hzero
  | succ j ih =>
    exact transitionRowCheck_sound (ih (by omega)) (htransition j hj)

@[expose] def rotationGridRowsCheck (seeds : List (CosineTerm × RotationSeed))
    (rows : ℕ → List (ℤ × ℤ)) (n : ℕ) : Bool :=
  initialRowCheck seeds (rows 0) &&
    (List.range (n - 1)).all (fun j => transitionRowCheck seeds (rows j) (rows (j + 1)))

theorem rotationGridRowsCheck_sound {seeds : List (CosineTerm × RotationSeed)}
    {rows : ℕ → List (ℤ × ℤ)} {n j : ℕ}
    (h : rotationGridRowsCheck seeds rows n = true) (hj : j < n) :
    RowCorrect seeds (rows j) j := by
  simp only [rotationGridRowsCheck, Bool.and_eq_true, List.all_eq_true] at h
  apply rowCorrect_of_checked_transitions seeds rows n h.1 _ hj
  intro k hk
  exact h.2 k (List.mem_range.mpr (by omega))

/-- A bounded chunk of transitions, suitable for independently compiled proof leaves. -/
@[expose] def transitionRowRangeCheck (seeds : List (CosineTerm × RotationSeed))
    (rows : ℕ → List (ℤ × ℤ)) (start count : ℕ) : Bool :=
  (List.range count).all (fun k =>
    transitionRowCheck seeds (rows (start + k)) (rows (start + k + 1)))

theorem transitionRowRangeCheck_sound {seeds : List (CosineTerm × RotationSeed)}
    {rows : ℕ → List (ℤ × ℤ)} {start count j : ℕ}
    (h : transitionRowRangeCheck seeds rows start count = true)
    (hl : start ≤ j) (hu : j < start + count) :
    transitionRowCheck seeds (rows j) (rows (j + 1)) = true := by
  simp only [transitionRowRangeCheck, List.all_eq_true] at h
  have hk := h (j - start) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hl] using hk

/-- A checked seed controls its exact orbit at every natural index, independently
of the finite storage layout used by a particular numerical certificate. -/
theorem RotationSeed.iter_trig_mem {seed : RotationSeed} {frequency : ℚ}
    (h : seed.check frequency = true) (j : ℕ) :
    Real.cos ((frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ) ∈
      rotationCoordinateBox (rotationIter seed.step.1 seed.step.2 seed.initial j).1
        (rotationRadius rotationSeedError rotationSeedError j) ∧
    Real.sin ((frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ) ∈
      rotationCoordinateBox (rotationIter seed.step.1 seed.step.2 seed.initial j).2
        (rotationRadius rotationSeedError rotationSeedError j) := by
  obtain ⟨hcs, hi, hs⟩ := RotationSeed.check_sound h
  have hb := rotationIter_mem_boxes seed.initial hcs
    (rotationAngle_norm ((2 * frequency / 1024 : ℚ) : ℝ))
    (rotationAngle_norm ((frequency / 1024 : ℚ) : ℝ)) hi hs j
  rw [rotationAngle_pow, ← rotationAngle_add] at hb
  have he : (j : ℝ) * ((2 * frequency / 1024 : ℚ) : ℝ) + ((frequency / 1024 : ℚ) : ℝ) =
      ((frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ) := by
    push_cast
    ring
  rw [he] at hb
  exact hb

theorem RowCorrect.trig_of_seed_checks {seeds : List (CosineTerm × RotationSeed)}
    {row : List (ℤ × ℤ)} {j : ℕ} (hrow : RowCorrect seeds row j)
    (hseeds : ∀ p ∈ seeds, p.2.check p.1.frequency = true) :
    RowTrigCorrect (seeds.map Prod.fst) row j := by
  unfold RowCorrect at hrow
  unfold RowTrigCorrect
  revert hseeds
  induction hrow with
  | nil => intro _; exact List.Forall₂.nil
  | @cons p state seeds row hstate htail ih =>
    intro hseeds
    simp only [List.map_cons]
    apply List.Forall₂.cons
    · rw [hstate]
      exact RotationSeed.iter_trig_mem (hseeds p (List.mem_cons_self)) j
    · apply ih
      intro q hq
      exact hseeds q (List.mem_cons_of_mem p hq)

theorem RowCorrect.trig {seeds : List (CosineTerm × RotationSeed)}
    {row : List (ℤ × ℤ)} {j : ℕ} (hrow : RowCorrect seeds row j)
    (hseeds : rotationSeedsCheck seeds = true) : RowTrigCorrect (seeds.map Prod.fst) row j := by
  apply hrow.trig_of_seed_checks
  simpa only [rotationSeedsCheck, List.all_eq_true] using hseeds

/-- Final semantic interface for a checked finite row-oriented trigonometric grid. -/
theorem rotationGrid_trig_mem {seeds : List (CosineTerm × RotationSeed)}
    {rows : ℕ → List (ℤ × ℤ)} {n j : ℕ}
    (hseeds : rotationSeedsCheck seeds = true)
    (hrows : rotationGridRowsCheck seeds rows n = true) (hj : j < n) :
    RowTrigCorrect (seeds.map Prod.fst) (rows j) j :=
  (rotationGridRowsCheck_sound hrows hj).trig hseeds

end
end ErdosOverlap.Numerics
