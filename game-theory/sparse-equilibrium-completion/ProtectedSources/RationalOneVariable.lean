/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic
@[expose] public section
namespace SparseCompletion.RationalElimination

/-- Computable maximum, with none exactly for an empty list. -/
def maximum? : List ℚ → Option ℚ
  | [] => none
  | x :: xs => match maximum? xs with
    | none => some x
    | some y => some (max x y)

/-- Computable minimum, with none exactly for an empty list. -/
def minimum? : List ℚ → Option ℚ
  | [] => none
  | x :: xs => match minimum? xs with
    | none => some x
    | some y => some (min x y)

theorem maximum_none_iff (xs : List ℚ) : maximum? xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [maximum?]
  | cons x xs =>
    simp only [maximum?, List.cons_ne_nil, iff_false]
    cases maximum? xs <;> simp

theorem minimum_none_iff (xs : List ℚ) : minimum? xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [minimum?]
  | cons x xs =>
    simp only [minimum?, List.cons_ne_nil, iff_false]
    cases minimum? xs <;> simp

theorem maximum_spec {xs : List ℚ} {u : ℚ} (h : maximum? xs = some u) :
    u ∈ xs ∧ ∀ x ∈ xs, x ≤ u := by
  induction xs generalizing u with
  | nil => simp [maximum?] at h
  | cons x xs ih =>
    cases he : maximum? xs with
    | none =>
      have hempty := (maximum_none_iff xs).mp he
      subst xs
      have heq : x = u := by simpa [maximum?] using h
      subst u
      simp
    | some y =>
      have hxy : max x y = u := by simpa [maximum?, he] using h
      subst u
      obtain ⟨hy, hall⟩ := ih he
      constructor
      · rcases le_total x y with hxy | hyx
        · simp only [max_eq_right hxy]; exact List.mem_cons_of_mem x hy
        · simp only [max_eq_left hyx]; exact List.mem_cons_self
      · intro z hz
        rcases List.mem_cons.mp hz with hz | hz
        · rw [hz]; exact le_max_left x y
        · exact le_trans (hall z hz) (le_max_right x y)

theorem minimum_spec {xs : List ℚ} {u : ℚ} (h : minimum? xs = some u) :
    u ∈ xs ∧ ∀ x ∈ xs, u ≤ x := by
  induction xs generalizing u with
  | nil => simp [minimum?] at h
  | cons x xs ih =>
    cases he : minimum? xs with
    | none =>
      have hempty := (minimum_none_iff xs).mp he
      subst xs
      have heq : x = u := by simpa [minimum?] using h
      subst u
      simp
    | some y =>
      have hxy : min x y = u := by simpa [minimum?, he] using h
      subst u
      obtain ⟨hy, hall⟩ := ih he
      constructor
      · rcases le_total x y with hxy | hyx
        · simp only [min_eq_left hxy]; exact List.mem_cons_self
        · simp only [min_eq_right hyx]; exact List.mem_cons_of_mem x hy
      · intro z hz
        rcases List.mem_cons.mp hz with hz | hz
        · rw [hz]; exact min_le_left x y
        · exact le_trans (min_le_right x y) (hall z hz)

/-- Prefer the greatest lower bound; if absent use the least upper bound;
if both lists are empty use zero. This is an executable rational value. -/
def select (lower upper : List ℚ) : ℚ :=
  match maximum? lower, minimum? upper with
  | some l, _ => l
  | none, some u => u
  | none, none => 0

theorem select_bounds (lower upper : List ℚ)
    (hpairs : ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u) :
    (∀ l ∈ lower, l ≤ select lower upper) ∧
    (∀ u ∈ upper, select lower upper ≤ u) := by
  cases hl : maximum? lower with
  | some l =>
    obtain ⟨hmem, hall⟩ := maximum_spec hl
    constructor
    · simpa only [select, hl] using hall
    · intro u hu
      simpa only [select, hl] using hpairs l hmem u hu
  | none =>
    have hempty := (maximum_none_iff lower).mp hl
    subst lower
    cases hu : minimum? upper with
    | none =>
      have hempty := (minimum_none_iff upper).mp hu
      subst upper
      simp
    | some u =>
      obtain ⟨_, hall⟩ := minimum_spec hu
      constructor
      · simp
      · simpa only [select, maximum?, hu] using hall

/-- A row denotes a*x+b<=c. -/
structure Row where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq, Repr

def Row.Holds (r : Row) (x : ℚ) : Prop := r.a*x+r.b ≤ r.c

def Row.endpoint (r : Row) : ℚ := (r.c-r.b)/r.a

def lowerBounds (rows : List Row) : List ℚ :=
  (rows.filter (fun r => r.a < 0)).map Row.endpoint

def upperBounds (rows : List Row) : List ℚ :=
  (rows.filter (fun r => 0 < r.a)).map Row.endpoint

def candidate (rows : List Row) : ℚ := select (lowerBounds rows) (upperBounds rows)

/-- Precisely the one-variable Fourier--Motzkin residual conditions. -/
def Eliminated (rows : List Row) : Prop :=
  (∀ r ∈ rows, r.a = 0 → r.b ≤ r.c) ∧
  ∀ l ∈ rows, l.a < 0 → ∀ u ∈ rows, 0 < u.a → l.endpoint ≤ u.endpoint

theorem row_positive_iff (r : Row) (ha : 0 < r.a) (x : ℚ) :
    r.Holds x ↔ x ≤ r.endpoint := by
  unfold Row.Holds Row.endpoint
  rw [le_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

theorem row_negative_iff (r : Row) (ha : r.a < 0) (x : ℚ) :
    r.Holds x ↔ r.endpoint ≤ x := by
  unfold Row.Holds Row.endpoint
  rw [div_le_iff_of_neg ha]
  constructor <;> intro h <;> nlinarith

theorem feasible_implies_eliminated (rows : List Row) (x : ℚ)
    (hx : ∀ r ∈ rows, r.Holds x) : Eliminated rows := by
  constructor
  · intro r hr ha
    have hh := hx r hr
    simpa only [Row.Holds,ha,zero_mul,zero_add] using hh
  · intro l hl hla u hu hua
    exact le_trans ((row_negative_iff l hla x).mp (hx l hl))
      ((row_positive_iff u hua x).mp (hx u hu))

theorem candidate_feasible (rows : List Row) (h : Eliminated rows) :
    ∀ r ∈ rows, r.Holds (candidate rows) := by
  have hpairs : ∀ l ∈ lowerBounds rows, ∀ u ∈ upperBounds rows, l ≤ u := by
    intro l hl u hu
    obtain ⟨rl, hrl, rfl⟩ := List.mem_map.mp hl
    obtain ⟨ru, hru, rfl⟩ := List.mem_map.mp hu
    have hrl' := List.mem_filter.mp hrl
    have hru' := List.mem_filter.mp hru
    exact h.2 rl hrl'.1 (by simpa using hrl'.2) ru hru'.1 (by simpa using hru'.2)
  have hb := select_bounds (lowerBounds rows) (upperBounds rows) hpairs
  intro r hr
  rcases lt_trichotomy r.a 0 with ha | ha | ha
  · apply (row_negative_iff r ha _).mpr
    exact hb.1 r.endpoint (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,by simpa⟩,rfl⟩)
  · have hh := h.1 r hr ha
    simpa only [Row.Holds,ha,zero_mul,zero_add] using hh
  · apply (row_positive_iff r ha _).mpr
    exact hb.2 r.endpoint (List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨hr,by simpa⟩,rfl⟩)

theorem eliminated_iff_exists (rows : List Row) :
    Eliminated rows ↔ ∃ x : ℚ, ∀ r ∈ rows, r.Holds x :=
  ⟨fun h => ⟨candidate rows,candidate_feasible rows h⟩,
   fun ⟨x,hx⟩ => feasible_implies_eliminated rows x hx⟩

end SparseCompletion.RationalElimination
