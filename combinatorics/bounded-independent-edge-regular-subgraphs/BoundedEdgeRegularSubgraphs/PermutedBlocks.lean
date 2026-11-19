module

public import BoundedEdgeRegularSubgraphs.ConsecutiveBlocks
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# A partition with at least half of its blocks in a prescribed family
-/

public section

open Finset Function
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem exists_perm_map_finset {n : ℕ} (A B : Finset (Fin n)) (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin n), A.map σ.toEmbedding = B := by
  classical
  let a := A.card
  let b := n - A.card
  have hA : Aᶜ.card = b := by simp [b, Finset.card_compl]
  have hB : Bᶜ.card = b := by simp [b, Finset.card_compl, ← h]
  let u : Fin a ⊕ Fin b ≃ Fin n := finSumEquivOfFinset rfl hA
  let v : Fin a ⊕ Fin b ≃ Fin n := finSumEquivOfFinset h.symm hB
  let τ := u.symm.trans v
  refine ⟨τ, ?_⟩
  ext x
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := (A.orderIsoOfFin rfl).surjective ⟨y, hy⟩
    have hyu : u (Sum.inl i) = y := by
      rw [show u (Sum.inl i) = (A.orderIsoOfFin rfl i).val from rfl]
      exact congrArg Subtype.val hi
    change v (u.symm y) ∈ B
    rw [← hyu, u.symm_apply_apply]
    exact (B.orderIsoOfFin h.symm i).property
  · intro hx
    obtain ⟨i, hi⟩ := (B.orderIsoOfFin h.symm).surjective ⟨x, hx⟩
    refine ⟨u (Sum.inl i), (A.orderIsoOfFin rfl i).property, ?_⟩
    change v (u.symm (u (Sum.inl i))) = x
    rw [u.symm_apply_apply]
    exact congrArg Subtype.val hi

private theorem card_perm_fibre_eq {n : ℕ} (A B C : Finset (Fin n)) (h : B.card = C.card) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π ↦ A.map π.toEmbedding = B)).card =
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π ↦ A.map π.toEmbedding = C)).card := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_map_finset B C h
  have hσ' : C.map σ.symm.toEmbedding = B := by
    rw [← hσ, Finset.map_map]
    have he : σ.toEmbedding.trans σ.symm.toEmbedding = Function.Embedding.refl (Fin n) := by
      ext1 x
      exact σ.symm_apply_apply x
    rw [he, Finset.map_refl]
  apply Finset.card_bij (fun π _ ↦ π.trans σ)
  · intro π hπ
    have he := (Finset.mem_filter.mp hπ).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [show (π.trans σ).toEmbedding = π.toEmbedding.trans σ.toEmbedding from rfl, ← Finset.map_map, he, hσ]
  · intro π _ ρ _ hπ
    ext1 i
    exact σ.injective (congrFun (congrArg (fun e : Equiv.Perm (Fin n) ↦ (e : Fin n → Fin n)) hπ) i)
  · intro π hπ
    have he := (Finset.mem_filter.mp hπ).2
    refine ⟨π.trans σ.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [show (π.trans σ.symm).toEmbedding = π.toEmbedding.trans σ.symm.toEmbedding from rfl,
        ← Finset.map_map, he, hσ']
    · ext1 i
      exact σ.apply_symm_apply (π i)

private theorem card_good_perm_mul_two_ge {n m : ℕ} (A : Finset (Fin n)) (hA : A.card = m)
    (Good : Finset (Fin n) → Prop) [DecidablePred Good]
    (hGood : n.choose m ≤ 2 * (((Finset.univ : Finset (Fin n)).powersetCard m).filter Good).card) :
    Fintype.card (Equiv.Perm (Fin n)) ≤
      2 * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π ↦ Good (A.map π.toEmbedding))).card := by
  classical
  let P : Finset (Equiv.Perm (Fin n)) := Finset.univ
  let S : Finset (Finset (Fin n)) := Finset.univ.powersetCard m
  let G := S.filter Good
  let f (π : Equiv.Perm (Fin n)) := A.map π.toEmbedding
  let F := P.filter (fun π ↦ Good (f π))
  let t := (P.filter (fun π ↦ f π = A)).card
  have hS (π : Equiv.Perm (Fin n)) : f π ∈ S := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, (Finset.card_map _).trans hA⟩
  have hFibre (B : Finset (Fin n)) (hB : B ∈ S) : (P.filter (fun π ↦ f π = B)).card = t :=
    card_perm_fibre_eq A B A ((Finset.mem_powersetCard.mp hB).2.trans hA.symm)
  have hP : P.card = S.card * t := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S) (fun π _ ↦ hS π)]
    calc
      _ = ∑ _ ∈ S, t := Finset.sum_congr rfl hFibre
      _ = _ := by simp
  have hF : F.card = G.card * t := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := G) (fun π hπ ↦
      Finset.mem_filter.mpr ⟨hS π, (Finset.mem_filter.mp hπ).2⟩)]
    calc
      _ = ∑ _ ∈ G, t := by
        apply Finset.sum_congr rfl
        intro B hB
        obtain ⟨hBS, hBG⟩ := Finset.mem_filter.mp hB
        have he : F.filter (fun π ↦ f π = B) = P.filter (fun π ↦ f π = B) := by
          ext π
          simp only [F, Finset.mem_filter]
          exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.symm ▸ hBG⟩, h.2⟩⟩
        rw [he, hFibre B hBS]
      _ = _ := by simp
  have hSG : S.card ≤ 2 * G.card := by simpa only [S, G, Finset.card_powersetCard, card_univ, Fintype.card_fin] using hGood
  have h := Nat.mul_le_mul_right t hSG
  change P.card ≤ 2 * F.card
  rw [hP, hF, ← Nat.mul_assoc]
  exact h

/-- A half-density family of m-subsets contains at least half of the full
blocks of some permutation of the consecutive partition. -/
theorem exists_permuted_blocks_half_good (n m : ℕ) (Good : Finset (Fin n) → Prop) [DecidablePred Good]
    (hGood : n.choose m ≤ 2 * (((Finset.univ : Finset (Fin n)).powersetCard m).filter Good).card) :
    ∃ σ : Equiv.Perm (Fin n), n / m ≤ 2 * ((Finset.univ : Finset (Fin (n / m))).filter
      (fun i ↦ Good ((consecutiveVertexBlock n m i).map σ.toEmbedding))).card := by
  classical
  let b := n / m
  let I : Finset (Fin b) := Finset.univ
  let P : Finset (Equiv.Perm (Fin n)) := Finset.univ
  let u (π : Equiv.Perm (Fin n)) (i : Fin b) : ℕ :=
    if Good ((consecutiveVertexBlock n m i).map π.toEmbedding) then 1 else 0
  have hCol (i : Fin b) : P.card ≤ 2 * ∑ π ∈ P, u π i := by
    simpa only [P, u, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one, Finset.card_univ] using
      card_good_perm_mul_two_ge (consecutiveVertexBlock n m i) (card_consecutiveVertexBlock n m i) Good hGood
  have hTotal : P.card * b ≤ 2 * ∑ π ∈ P, ∑ i ∈ I, u π i := by
    calc
      _ = ∑ _ ∈ I, P.card := by simp [I, mul_comm]
      _ ≤ ∑ i ∈ I, 2 * ∑ π ∈ P, u π i := Finset.sum_le_sum (fun i _ ↦ hCol i)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  by_contra! h
  have hRow (π : Equiv.Perm (Fin n)) : 2 * ∑ i ∈ I, u π i < b := by
    simpa only [I, u, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one, b] using h π
  have hlt : (∑ π ∈ P, 2 * ∑ i ∈ I, u π i) < ∑ _ ∈ P, b :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun π _ ↦ hRow π)
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hlt
  exact (not_lt_of_ge hTotal) hlt

end BoundedEdgeRegularSubgraphs
