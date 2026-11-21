module

public import AdaptiveErrors
public import GoodWitness
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V I : Type*} [Fintype I]

theorem retained_errors (G : SimpleGraph V) (p v κ : ℝ) (vp : 0 < v) (kp : 0 ≤ κ)
    (x : I ↪ V) (E : Finset V) (eW : E ⊆ univ.map x)
    (mom : fourthMoment (fun i j => centered G p (x i) (x j)) univ ≤ κ^2)
    (other : Finset I) :
    ∃ good ⊆ E, (E.card:ℝ)-good.card ≤ E.card*κ/v^2+other.card ∧
      (∀ y ∈ good, |(degreeOn G E y:ℝ)-p*E.card| ≤ v) ∧
      ∀ i, x i ∈ good → i ∉ other := by
  classical
  let K := univ.filter (fun i => x i ∈ E)
  have eq : K.map x = E := by
    ext y
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_map.mp h
      exact (mem_filter.mp hi).2
    · intro h
      obtain ⟨i,_,rfl⟩ := mem_map.mp (eW h)
      exact mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  have card : K.card=E.card := (card_map _).symm.trans (congrArg Finset.card eq)
  let A := fun i j => centered G p (x i) (x j)
  let base := univ.filter (fun i => v < |∑ j ∈ K, A i j|)
  have h := exceptional_rows A univ K (subset_univ _) v κ vp.le kp mom
  change (base.card:ℝ)*v^2 ≤ K.card*κ at h
  have cap := (le_div_iff₀ (by positivity : 0<v^2)).mpr h
  rw [card] at cap
  let bad := (base∪other).map x
  let good := E \ bad
  have loss : (E.card:ℝ)-good.card ≤ bad.card := by
    have le := card_le_card (show E ⊆ good∪bad by
      intro y hy
      by_cases b : y ∈ bad
      · exact mem_union_right _ b
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hy,b⟩))
    exact sub_le_iff_le_add.mpr (by rw [add_comm]; exact_mod_cast le.trans (card_union_le good bad))
  have badsize : (bad.card:ℝ) ≤ base.card+other.card := by dsimp [bad]; rw [card_map]; exact_mod_cast card_union_le base other
  refine ⟨good,sdiff_subset,by linarith,?_,?_⟩
  · intro y hy
    obtain ⟨i,_,rfl⟩ := mem_map.mp (eW (mem_sdiff.mp hy).1)
    have safe : i ∉ base := fun m => (mem_sdiff.mp hy).2 (mem_map.mpr ⟨i,mem_union_left _ m,rfl⟩)
    have ok : |∑ j ∈ K, A i j| ≤ v := le_of_not_gt (fun excess => safe (mem_filter.mpr ⟨mem_univ _,excess⟩))
    rw [← centered_degree]
    convert ok using 2
    conv_lhs => rw [← eq,sum_map]
  · intro i hi m
    exact (mem_sdiff.mp hi).2 (mem_map.mpr ⟨i,mem_union_right _ m,rfl⟩)

end InducedDegreeRepetition.Sampling
