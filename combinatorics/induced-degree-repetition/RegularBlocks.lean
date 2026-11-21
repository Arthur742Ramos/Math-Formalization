module

public import DependentChoice
public import RemainingStatements
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition

open Finset OpenProblems
open scoped Classical

structure SavedBlock (V : Type*) where
  vertices : Finset V
  inner : Bool
  outer : Bool

/-- The block saved earlier determines the common colour of all cross-edges. -/
@[expose] def Follows {V : Type*} (G : SimpleGraph V) (A B : SavedBlock V) : Prop :=
  Disjoint A.vertices B.vertices ∧
  ∀ x ∈ A.vertices, ∀ y ∈ B.vertices, adj G x y = A.outer

/-- Four possible colour pairs suffice to recover a regular union from the
successful rounds of the density reduction. -/
theorem regular_block_union {V : Type*} (G : SimpleGraph V) (L : List (SavedBlock V))
    (s k : ℕ) (enough : 4*k ≤ L.length)
    (size : ∀ A ∈ L, A.vertices.card = s)
    (inside : ∀ A ∈ L, Homogeneous G (A.inner = true) A.vertices)
    (chain : L.Pairwise (Follows G)) :
    ∃ U : Finset V, U.card = k*s ∧ ∃ d, degreeClass G U d = U := by
  classical
  let col := fun i : Fin L.length => ((L.get i).inner,(L.get i).outer)
  obtain ⟨c,hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card col (n := k) (by
    simpa [Fintype.card_prod] using enough)
  obtain ⟨I,hI,cardI⟩ := exists_subset_card_eq hc
  let A := fun i : Fin L.length => (L.get i).vertices
  have colors (i) (hi : i ∈ I) := (mem_filter.mp (hI hi)).2
  have sizes (i) : (A i).card = s := size _ (List.get_mem ..)
  have dj : (I : Set (Fin L.length)).PairwiseDisjoint A := by
    intro i _ j _ hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · exact ((List.pairwise_iff_get.mp chain) i j hh).1
    · exact ((List.pairwise_iff_get.mp chain) j i hh).1.symm
  have between (i) (hi : i ∈ I) (j) (hj : j ∈ I) (hn : i ≠ j) (x) (hx : x ∈ A i)
      (y) (hy : y ∈ A j) : G.Adj x y ↔ c.2 = true := by
    have sym (x y : V) : adj G x y = adj G y x := by simp only [adj,G.adj_comm x y]
    have v : adj G x y = c.2 := by
      rcases lt_or_gt_of_ne hn with hh | hh
      · exact (((List.pairwise_iff_get.mp chain) i j hh).2 x hx y hy).trans (congrArg Prod.snd (colors i hi))
      · exact (sym x y).trans ((((List.pairwise_iff_get.mp chain) j i hh).2 y hy x hx).trans
          (congrArg Prod.snd (colors j hj)))
    simpa [adj] using (congrArg (· = true) v).to_iff
  let U := I.biUnion A
  let d₀ := if c.1 then s-1 else 0
  let d₁ := if c.2 then s else 0
  refine ⟨U,by simp [U,card_biUnion dj,sizes,cardI],d₀+(k-1)*d₁,?_⟩
  apply filter_true_of_mem
  intro x hx
  obtain ⟨i,hi,hxi⟩ := mem_biUnion.mp hx
  have own : degreeOn G (A i) x = d₀ := by
    have h := inside _ (List.get_mem L i)
    have col₀ : (L.get i).inner = c.1 := congrArg Prod.fst (colors i hi)
    by_cases c₀ : c.1 = true
    · have eqn : (A i).filter (G.Adj x) = (A i).erase x := by
        ext y
        simp only [mem_filter, mem_erase]
        exact ⟨fun ⟨hy,hxy⟩ => ⟨hxy.ne.symm,hy⟩,fun ⟨hne,hy⟩ =>
          ⟨hy,(h x hxi y hy hne.symm).mpr (col₀.trans c₀)⟩⟩
      simp [degreeOn,eqn,card_erase_of_mem hxi,sizes,d₀,c₀]
    · have eqn : (A i).filter (G.Adj x) = ∅ := filter_false_of_mem fun y hy hxy =>
        c₀ (col₀.symm.trans ((h x hxi y hy hxy.ne).mp hxy))
      simp [degreeOn,eqn,d₀,c₀]
  have other (j) (hj : j ∈ I) (hne : j ≠ i) : degreeOn G (A j) x = d₁ := by
    by_cases c₁ : c.2 = true
    · have eqn := filter_true_of_mem (s := A j) (p := G.Adj x)
          (fun y hy => (between i hi j hj hne.symm x hxi y hy).mpr c₁)
      simp [degreeOn,eqn,sizes,d₁,c₁]
    · have eqn := filter_false_of_mem (s := A j) (p := G.Adj x) (fun y hy h =>
          c₁ ((between i hi j hj hne.symm x hxi y hy).mp h))
      simp [degreeOn,eqn,d₁,c₁]
  have split : degreeOn G U x = ∑ j ∈ I, degreeOn G (A j) x := by
    simp only [degreeOn,U,filter_biUnion]
    exact card_biUnion (fun j hj l hl hn => (dj hj hl hn).mono (filter_subset ..) (filter_subset ..))
  rw [split, ← add_sum_erase I _ hi, own]
  congr 1
  calc
    _ = ∑ _ ∈ I.erase i, d₁ := sum_congr rfl fun j hj => other j (mem_erase.mp hj).2 (mem_erase.mp hj).1
    _ = _ := by simp [card_erase_of_mem hi,cardI]

end InducedDegreeRepetition
