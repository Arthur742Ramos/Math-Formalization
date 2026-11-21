module

public import GroupMean
public import MeanEvents
public import SimultaneousAdjustment
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Sampling

open Filter Finset OpenProblems
open scoped Classical
variable {X : Type*}

/-- All tester labels from other groups, with repetitions retained. -/
@[expose] noncomputable def exteriorList {g s : ℕ} (j : Fin g) (ys : {k : Fin g // k ≠ j} → Fin s → X) :=
  ((univ : Finset ({k : Fin g // k ≠ j} × Fin s)).toList).map fun z => ys z.1 z.2

theorem length_exterior {g s : ℕ} (j : Fin g) (ys : {k : Fin g // k ≠ j} → Fin s → X) :
    (exteriorList j ys).length = (g-1)*s := by
  simp [exteriorList,Fintype.card_subtype_compl]

theorem exterior_mem {g s : ℕ} (j k : Fin g) (t : Fin s) (ne : k ≠ j) (ys : Fin g → Fin s → X) :
    ys k t ∈ exteriorList j (fun a => ys a) := by
  apply List.mem_map.mpr
  exact ⟨(⟨k,ne⟩,t),by simp,rfl⟩

/-- Apply the group adjustment bound at every possible registered exterior
list, before conditioning on whether other groups are adjustable. -/
theorem group_failure {g n s : ℕ} (G : SimpleGraph X) (T : Finset X) (θ ε : ℝ) (he : 0 ≤ ε)
    (Xs : Fin g → Fin n → List (Finset X))
    [Nonempty T] [∀ j i, Nonempty ↥(tupleSpace (Xs j i))]
    (j : Fin g)
    (local_bound : ∀ o : {k : Fin g // k ≠ j} → Fin s → T,
      let ex := exteriorList j (fun k u => (o k u : X))
      let draws := (Fintype.piFinset fun i => tupleSpace (Xs j i)) ×ˢ
        (Fintype.piFinset fun _ : Fin s => T)
      ((draws.filter fun z => ¬Adjustable G θ (Xs j) (fun _ => ex) z.1 z.2).card:ℝ) ≤ ε*draws.card) :
    mean (fun p : (∀ j i, ↥(tupleSpace (Xs j i))) × (Fin g → Fin s → T) =>
      indicator (¬Adjustable G θ (Xs j)
        (fun _ => exteriorList j (fun k t => (p.2 k t : X)))
        (fun i => (p.1 j i).val) (fun t => (p.2 j t).val))) ≤ ε := by
  classical
  let R (j : Fin g) := ∀ i, ↥(tupleSpace (Xs j i))
  let tests (_ : Fin g) := Fin s → T
  apply mean_group R tests j (fun o ref ys => indicator (¬Adjustable G θ (Xs j)
    (fun _ => exteriorList j (fun k t => (o k t : X))) (fun i => (ref i).val) (fun t => (ys t).val)))
  intro o
  apply product_event_bound (fun i => tupleSpace (Xs j i)) (fun _ : Fin s => T)
    (fun ref ys => ¬Adjustable G θ (Xs j) (fun _ => exteriorList j (fun k t => (o k t : X))) ref ys) ε he
  convert local_bound o using 1
  apply congrArg Nat.cast
  apply congrArg Finset.card
  ext z
  simp [Fintype.mem_piFinset]

end InducedDegreeRepetition.Sampling
