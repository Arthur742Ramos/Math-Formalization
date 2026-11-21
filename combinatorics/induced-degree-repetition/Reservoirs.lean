module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {V I : Type*} [Fintype I]

/-- Reserve half of the host for testers and equal-sized, pairwise disjoint pools
for the auxiliary positions. -/
theorem reserve_pools (B : Finset V) (n : ℕ) (enough : Fintype.card I*n + B.card/2 ≤ B.card) :
    ∃ T ⊆ B, T.card = B.card/2 ∧ ∃ pool : I → Finset V,
      (∀ i, pool i ⊆ B ∧ (pool i).card = n ∧ Disjoint (pool i) T) ∧
      ∀ i j, i ≠ j → Disjoint (pool i) (pool j) := by
  classical
  obtain ⟨T,hT,sz⟩ := exists_subset_card_eq (s:=B) (Nat.div_le_self _ 2)
  have space : Fintype.card (I × Fin n) ≤ Fintype.card ↥(B \ T) := by
    rw [Fintype.card_coe,card_sdiff_of_subset hT,sz,Fintype.card_prod,Fintype.card_fin]
    omega
  let emb : I × Fin n ↪ ↥(B \ T) := Classical.choice (Function.Embedding.nonempty_of_card_le space)
  let pos (i : I) : Fin n ↪ V :=
    ⟨fun k => (emb (i,k)).val,fun a b h => by
      have := emb.injective (Subtype.ext h)
      exact (Prod.mk.inj this).2⟩
  let pool (i : I) := (univ : Finset (Fin n)).map (pos i)
  have outside (i) : pool i ⊆ B \ T := by
    intro x hx
    obtain ⟨k,_,rfl⟩ := mem_map.mp hx
    exact (emb (i,k)).2
  refine ⟨T,hT,sz,pool,fun i => ⟨(outside i).trans sdiff_subset,by simp [pool],?_⟩,?_⟩
  · exact disjoint_left.mpr fun _ hx ht => (mem_sdiff.mp (outside i hx)).2 ht
  · intro i j diff
    apply disjoint_left.mpr
    intro x hx hz
    obtain ⟨k,_,rfl⟩ := mem_map.mp hx
    obtain ⟨l,_,eq⟩ := mem_map.mp hz
    exact diff (Prod.mk.inj (emb.injective (Subtype.ext eq))).1.symm

end InducedDegreeRepetition.Sampling
