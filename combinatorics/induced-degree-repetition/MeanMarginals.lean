module

public import GroupMean
public import MeanEvents
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {I J X Y : Type*}

theorem mean_add [Fintype X] (f g : X → ℝ) :
    mean (fun x => f x+g x) = mean f+mean g := by simp only [mean,sum_add_distrib,add_div]

theorem mean_comm [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  simp only [mean,← sum_div]
  rw [sum_comm]
  ring

theorem mean_over_pool (T : Finset X) (f : X → ℝ) : mean (fun y : T => f y) = (∑ y ∈ T, f y)/T.card := by
  rw [mean,Fintype.card_coe,← sum_subtype (F:=(inferInstance : Fintype T)) T (fun _ => Iff.rfl) f]

/-- Marginal on one tuple group and one tester from any group. -/
theorem group_tester_mean [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype X] [Nonempty X]
    (R : I → Type*) [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)]
    (i k : I) (j : J) (f : R i → X → ℝ) :
    mean (fun p : (∀ i, R i) × (I → J → X) => f (p.1 i) (p.2 k j)) =
      mean (fun y => mean (fun x => f x y)) := by
  classical
  rw [mean_prod (fun (v : ∀ i, R i) (w : I → J → X) => f (v i) (w k j))]
  have eq (v : ∀ i, R i) :
      mean (fun w : I → J → X => f (v i) (w k j)) = mean (f (v i)) := by
    rw [mean_coordinate (fun _ : I => J → X) k (fun a => f (v i) (a j)),mean_coordinate (fun _ : J => X) j]
  simp_rw [eq]
  rw [mean_coordinate R i (fun x => mean (f x)),mean_comm]

theorem mean_flatten [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype X]
    (f : (I × J → X) → ℝ) :
    mean (fun w : I → J → X => f (fun z => w z.1 z.2)) = mean f := by
  let e : (I → J → X) ≃ (I × J → X) :=
    ⟨fun w z => w z.1 z.2,fun w i j => w (i,j),fun _ => rfl,fun _ => rfl⟩
  exact mean_equiv e _ _ (fun _ => rfl)

end InducedDegreeRepetition.Sampling
