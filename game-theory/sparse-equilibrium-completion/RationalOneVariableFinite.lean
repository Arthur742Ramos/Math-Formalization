/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalOneVariable
@[expose] public section
namespace SparseCompletion.RationalElimination

instance eliminatedDecidable (rows : List Row) : Decidable (Eliminated rows) := by
  unfold Eliminated
  infer_instance

/-- Finite exact rational decision and reconstruction; no feasibility oracle. -/
def solve (rows : List Row) : Option ℚ :=
  if Eliminated rows then some (candidate rows) else none

theorem solve_some_sound {rows : List Row} {x : ℚ} (h : solve rows = some x) :
    ∀ r ∈ rows, r.Holds x := by
  unfold solve at h
  split at h
  next he =>
    have hx : candidate rows = x := Option.some.inj h
    rw [←hx]
    exact candidate_feasible rows he
  next he => simp at h

theorem solve_none_iff (rows : List Row) :
    solve rows = none ↔ ¬ ∃ x : ℚ, ∀ r ∈ rows, r.Holds x := by
  simp only [solve, ite_eq_right_iff, Option.some_ne_none, imp_false]
  exact not_congr (eliminated_iff_exists rows)

/-- Literal finite coefficient arrays are enumerated by List.ofFn. -/
def finiteRows {n : ℕ} (a b c : Fin n → ℚ) : List Row :=
  List.ofFn fun i => ⟨a i,b i,c i⟩

def finiteCandidate {n : ℕ} (a b c : Fin n → ℚ) : ℚ := candidate (finiteRows a b c)

def FiniteEliminated {n : ℕ} (a b c : Fin n → ℚ) : Prop :=
  (∀ i, a i = 0 → b i ≤ c i) ∧
  ∀ i, a i < 0 → ∀ j, 0 < a j → (c i-b i)/a i ≤ (c j-b j)/a j

theorem finite_eliminated_iff {n : ℕ} (a b c : Fin n → ℚ) :
    FiniteEliminated a b c ↔ Eliminated (finiteRows a b c) := by
  unfold FiniteEliminated Eliminated finiteRows
  constructor
  · intro h
    constructor
    · intro r hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      exact h.1 i
    · intro l hl hla u hu hua
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
      exact h.2 i hla j hua
  · intro h
    constructor
    · intro i hi
      exact h.1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩) hi
    · intro i hi j hj
      exact h.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩) hi _ (List.mem_ofFn.mpr ⟨j,rfl⟩) hj

theorem finite_candidate_feasible {n : ℕ} (a b c : Fin n → ℚ)
    (h : FiniteEliminated a b c) :
    ∀ i, a i*finiteCandidate a b c+b i ≤ c i := by
  intro i
  exact candidate_feasible _ ((finite_eliminated_iff a b c).mp h) _
    (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem finite_eliminated_iff_exists {n : ℕ} (a b c : Fin n → ℚ) :
    FiniteEliminated a b c ↔ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  constructor
  · intro h
    exact ⟨finiteCandidate a b c,finite_candidate_feasible a b c h⟩
  · rintro ⟨x,hx⟩
    apply (finite_eliminated_iff a b c).mpr
    apply feasible_implies_eliminated _ x
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hx i

instance finiteEliminatedDecidable {n : ℕ} (a b c : Fin n → ℚ) :
    Decidable (FiniteEliminated a b c) := by
  unfold FiniteEliminated
  infer_instance

def solveFinite {n : ℕ} (a b c : Fin n → ℚ) : Option ℚ :=
  if FiniteEliminated a b c then some (finiteCandidate a b c) else none

theorem solve_finite_some_sound {n : ℕ} {a b c : Fin n → ℚ} {x : ℚ}
    (h : solveFinite a b c = some x) : ∀ i, a i*x+b i ≤ c i := by
  unfold solveFinite at h
  split at h
  next he =>
    have hx : finiteCandidate a b c = x := Option.some.inj h
    rw [←hx]
    exact finite_candidate_feasible a b c he
  next he => simp at h

theorem solve_finite_none_iff {n : ℕ} (a b c : Fin n → ℚ) :
    solveFinite a b c = none ↔ ¬ ∃ x : ℚ, ∀ i, a i*x+b i ≤ c i := by
  simp only [solveFinite, ite_eq_right_iff, Option.some_ne_none, imp_false]
  exact not_congr (finite_eliminated_iff_exists a b c)

end SparseCompletion.RationalElimination
