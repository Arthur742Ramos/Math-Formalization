/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalOneVariableFinite
public import Mathlib.Data.Finset.Max
@[expose] public section
namespace SparseCompletion.RationalElimination

/-- Endpoint sets use invariant finite-set operations, without choosing a list
or a noncomputable equivalence to a finite ordinal. -/
def indexedLower {I : Type*} [Fintype I] (a b c : I → ℚ) : Finset ℚ :=
  (Finset.univ.filter fun i => a i < 0).image fun i => (c i-b i)/a i

def indexedUpper {I : Type*} [Fintype I] (a b c : I → ℚ) : Finset ℚ :=
  (Finset.univ.filter fun i => 0 < a i).image fun i => (c i-b i)/a i

/-- Actual computable rational extraction for arbitrary finite row types. -/
def generalCandidate {I : Type*} [Fintype I] (a b c : I → ℚ) : ℚ :=
  if hl : (indexedLower a b c).Nonempty then (indexedLower a b c).max' hl
  else if hu : (indexedUpper a b c).Nonempty then (indexedUpper a b c).min' hu
  else 0

def FintypeEliminated {I : Type*} [Fintype I] (a b c : I → ℚ) : Prop :=
  (∀ i, a i = 0 → b i ≤ c i) ∧
  ∀ i, a i < 0 → ∀ j, 0 < a j → (c i-b i)/a i ≤ (c j-b j)/a j

theorem indexed_lower_mem {I : Type*} [Fintype I] (a b c : I → ℚ) (x : ℚ) :
    x ∈ indexedLower a b c ↔ ∃ i, a i < 0 ∧ (c i-b i)/a i=x := by
  simp only [indexedLower,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

theorem indexed_upper_mem {I : Type*} [Fintype I] (a b c : I → ℚ) (x : ℚ) :
    x ∈ indexedUpper a b c ↔ ∃ i, 0 < a i ∧ (c i-b i)/a i=x := by
  simp only [indexedUpper,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

theorem indexed_candidate_bounds {I : Type*} [Fintype I] (a b c : I → ℚ)
    (hpairs : ∀ i, a i < 0 → ∀ j, 0 < a j → (c i-b i)/a i ≤ (c j-b j)/a j) :
    (∀ i, a i < 0 → (c i-b i)/a i ≤ generalCandidate a b c) ∧
    (∀ j, 0 < a j → generalCandidate a b c ≤ (c j-b j)/a j) := by
  by_cases hl : (indexedLower a b c).Nonempty
  · have hmem := Finset.max'_mem (indexedLower a b c) hl
    obtain ⟨i,hi,heq⟩ := (indexed_lower_mem a b c _).mp hmem
    constructor
    · intro j hj
      simpa only [generalCandidate,dite_eq_left hl] using
        Finset.le_max' (indexedLower a b c) ((c j-b j)/a j)
          ((indexed_lower_mem a b c _).mpr ⟨j,hj,rfl⟩)
    · intro j hj
      simpa only [generalCandidate,dite_eq_left hl,←heq] using hpairs i hi j hj
  · constructor
    · intro i hi
      exact (hl ⟨_,(indexed_lower_mem a b c _).mpr ⟨i,hi,rfl⟩⟩).elim
    · intro j hj
      have hu : (indexedUpper a b c).Nonempty :=
        ⟨_,(indexed_upper_mem a b c _).mpr ⟨j,hj,rfl⟩⟩
      simpa only [generalCandidate,dite_eq_right hl,dite_eq_left hu] using
        Finset.min'_le (indexedUpper a b c) ((c j-b j)/a j)
          ((indexed_upper_mem a b c _).mpr ⟨j,hj,rfl⟩)

theorem fintype_candidate_feasible {I : Type*} [Fintype I] (a b c : I → ℚ)
    (h : FintypeEliminated a b c) :
    ∀ i, a i*generalCandidate a b c+b i ≤ c i := by
  have hb := indexed_candidate_bounds a b c h.2
  intro i
  rcases lt_trichotomy (a i) 0 with ha | ha | ha
  · exact (row_negative_iff ⟨a i,b i,c i⟩ ha _).mpr (hb.1 i ha)
  · simpa only [ha,zero_mul,zero_add] using h.1 i ha
  · exact (row_positive_iff ⟨a i,b i,c i⟩ ha _).mpr (hb.2 i ha)

theorem fintype_eliminated_iff_exists {I : Type*} [Fintype I] (a b c : I → ℚ) :
    FintypeEliminated a b c ↔ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  constructor
  · intro h
    exact ⟨generalCandidate a b c,fintype_candidate_feasible a b c h⟩
  · rintro ⟨x,hx⟩
    constructor
    · intro i hi
      simpa only [hi,zero_mul,zero_add] using hx i
    · intro i hi j hj
      exact le_trans ((row_negative_iff ⟨a i,b i,c i⟩ hi x).mp (hx i))
        ((row_positive_iff ⟨a j,b j,c j⟩ hj x).mp (hx j))

instance fintypeEliminatedDecidable {I : Type*} [Fintype I] (a b c : I → ℚ) :
    Decidable (FintypeEliminated a b c) := by
  unfold FintypeEliminated
  infer_instance

def solveFintype {I : Type*} [Fintype I] (a b c : I → ℚ) : Option ℚ :=
  if FintypeEliminated a b c then some (generalCandidate a b c) else none

theorem solve_fintype_some_sound {I : Type*} [Fintype I] {a b c : I → ℚ} {x : ℚ}
    (h : solveFintype a b c = some x) : ∀ i, a i*x+b i ≤ c i := by
  unfold solveFintype at h
  split at h
  next he =>
    have hx : generalCandidate a b c = x := Option.some.inj h
    rw [←hx]
    exact fintype_candidate_feasible a b c he
  next he => simp at h

theorem solve_fintype_none_iff {I : Type*} [Fintype I] (a b c : I → ℚ) :
    solveFintype a b c = none ↔ ¬ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  simp only [solveFintype,ite_eq_right_iff,Option.some_ne_none,imp_false]
  exact not_congr (fintype_eliminated_iff_exists a b c)

end SparseCompletion.RationalElimination
