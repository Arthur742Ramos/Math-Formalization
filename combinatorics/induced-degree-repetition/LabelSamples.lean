module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

public section
namespace InducedDegreeRepetition.Restriction

open Finset
open scoped Classical
variable {X : Type*} {I : Type*} [Fintype I]

@[expose] def labels {S : Finset X} (R : Finset S) : Finset X := R.map (Function.Embedding.subtype _)

@[simp] theorem card_labels {S : Finset X} (R : Finset S) : (labels R).card = R.card := card_map _
theorem labels_subset {S : Finset X} (R : Finset S) : labels R ⊆ S := by
  rintro _ h
  obtain ⟨x,_,rfl⟩ := mem_map.mp h
  exact x.2
@[simp] theorem labels_univ (S : Finset X) : labels (univ : Finset S) = S := by
  classical
  ext x
  simp [labels]
@[simp] theorem labels_filter {S : Finset X} (R : Finset S) (p : X → Prop) :
    labels (R.filter fun x => p x) = (labels R).filter p := by
  classical
  ext x
  simp [labels]

@[expose] def forget {S : Finset X} (v : I → S) : I → X := fun i => v i

theorem all_label_lists (S : Finset X) :
    (univ : Finset (I → S)).map (⟨forget,fun _ _ h => funext fun i => Subtype.ext (congrFun h i)⟩ :
      (I → S) ↪ (I → X)) = Fintype.piFinset (fun _ : I => S) := by
  classical
  ext ys
  simp only [mem_map,mem_univ,true_and,Fintype.mem_piFinset]
  constructor
  · rintro ⟨v,rfl⟩
    exact fun i => (v i).2
  · intro h
    exact ⟨fun i => ⟨ys i,h i⟩,rfl⟩

theorem count_label_event (S : Finset X) (p : (I → X) → Prop) :
    (((Fintype.piFinset (fun _ : I => S)).filter p).card : ℝ) =
    ∑ v : I → S, if p (forget v) then (1:ℝ) else 0 := by
  classical
  rw [← sum_boole,← all_label_lists,sum_map]
  rfl

end InducedDegreeRepetition.Restriction
