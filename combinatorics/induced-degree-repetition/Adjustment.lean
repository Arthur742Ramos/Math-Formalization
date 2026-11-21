module

public import IntegerTotals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

open Finset

variable {X Y : Type*}

/-- A tuple's possible replacements, with its registered exterior profile already fixed. -/
@[expose] noncomputable def profileFiber (pool : Finset X) (entry : X → Y → ℤ) (s : Y → ℤ) : Finset X := by
  classical exact pool.filter fun x => entry x = s

/-- The family compatible with the current counts at all rows except j. -/
@[expose] noncomputable def otherFiber (pool : Finset X) (entry : X → Y → ℤ) (s : Y → ℤ) (j : Y) :
    Finset X := by classical exact pool.filter fun x => ∀ k, k ≠ j → entry x k = s k

private theorem fiber_sub_other (pool : Finset X) (entry : X → Y → ℤ) (s : Y → ℤ) (j : Y) :
    profileFiber pool entry s ⊆ otherFiber pool entry s j := by
  classical
  intro x hx
  obtain ⟨h,he⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨h,fun k _ => congrFun he k⟩

/-- Counts with conditional mass at least λ after fixing the other rows. -/
@[expose] noncomputable def allowedCounts [DecidableEq Y] (L : ℕ) (weight : ℝ) (pool : Finset X)
    (entry : X → Y → ℤ) (s : Y → ℤ) (j : Y) : Finset ℤ := by
  classical
  exact (Icc 0 (L : ℤ)).filter fun v =>
    weight * (otherFiber pool entry s j).card ≤
      ((profileFiber pool entry (Function.update s j v)).card : ℝ)

/-- The deterministic edit induction in Lemma 11. A replacement is an actual member of
its exterior-compatible pool. The row tests apply to every sufficiently large family
obtained by fixing the other rows, including profiles reached during earlier edits. -/
theorem simultaneous_edits (L₀ L : ℕ) :
    ∃ n₀ C : ℕ, ∀ {ι X Y : Type} [DecidableEq Y]
      (I A B : Finset ι) (R : Finset Y) (pool : ι → Finset X) (entry : ι → X → Y → ℤ)
      (s₀ : ι → Y → ℤ) (length : ι → ℕ) (weight cut : ι → ℝ)
      (lower upper : ι → ℤ) (target : Y → ℤ),
      A ⊆ I → B ⊆ I → Disjoint A B → n₀ ≤ A.card → n₀ ≤ B.card →
      (∀ i ∈ I, length i ≤ L ∧ 0 < weight i ∧ weight i ≤ 1 ∧ 0 < cut i ∧
        cut i ≤ weight i ^ R.card * (profileFiber (pool i) (entry i) (s₀ i)).card) →
      (∀ i ∈ I, ∀ j, s₀ i j ∈ Icc 0 (length i : ℤ)) →
      (∀ i ∈ I, ∀ (s : Y → ℤ) j, j ∈ R → cut i ≤ (otherFiber (pool i) (entry i) s j).card →
        let T := allowedCounts (length i) (weight i) (pool i) (entry i) s j
        T.Nonempty ∧ low T ≤ lower i ∧ upper i ≤ high T ∧
        (i ∈ A → 1 < T.card ∧ T ⊆ Icc 0 (L₀ : ℤ)) ∧
        (i ∈ B → ∀ q, TestModulus L₀ q → ∃ x ∈ T, ∃ y ∈ T, ¬ (q : ℤ) ∣ x-y)) →
      (∀ j ∈ R, (∑ i ∈ I, lower i) + C ≤ target j ∧
        target j ≤ (∑ i ∈ I, upper i) - C ∧ Even (target j - ∑ i ∈ I, s₀ i j)) →
      ∃ replacements : (i : I) → X,
        (∀ i : I, replacements i ∈ pool i) ∧
        (∀ j ∈ R, (∑ i : I, entry i (replacements i) j) = target j) ∧
        (∀ (i : I) j, j ∉ R → entry i (replacements i) j = s₀ i j) := by
  classical
  obtain ⟨n,C,arithmetic⟩ := integer_totals L₀ L
  refine ⟨n,C,?_⟩
  intro ι X Y _ I A B R pool entry s₀ length weight cut lower upper target hA hB hd hnA hnB
    hbudget hinitial htest htarget
  let count := fun i (s : Y → ℤ) => ((profileFiber (pool i) (entry i) s).card : ℝ)
  have advance (J : Finset Y) (hJ : J ⊆ R) :
      ∃ s : ι → Y → ℤ, (∀ i ∈ I, weight i ^ J.card * count i (s₀ i) ≤ count i (s i)) ∧
        (∀ j ∈ J, (∑ i ∈ I, s i j) = target j) ∧ (∀ i j, j ∉ J → s i j = s₀ i j) := by
    induction J using Finset.induction_on with
    | empty => exact ⟨s₀,by simp,by simp,by simp⟩
    | @insert j J hj ih =>
      have jR := hJ (mem_insert_self ..)
      have sub : J ⊆ R := (subset_insert ..).trans hJ
      obtain ⟨s,hm,hs,hrest⟩ := ih sub
      let T := fun i => allowedCounts (length i) (weight i) (pool i) (entry i) (s i) j
      have tests (i) (hi : i ∈ I) := htest i hi (s i) j jR (by
        obtain ⟨_,hp,h1,_,hc⟩ := hbudget i hi
        calc
          cut i ≤ _ := hc
          _ ≤ weight i ^ J.card * count i (s₀ i) := mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hp.le h1 (card_le_card sub)) (Nat.cast_nonneg _)
          _ ≤ count i (s i) := hm i hi
          _ ≤ _ := Nat.cast_le.mpr (card_le_card (fiber_sub_other (pool i) (entry i) (s i) j)))
      obtain ⟨hl,hh,he⟩ := htarget j jR
      obtain ⟨v,E,_,_,hv,hE,hvsum⟩ := arithmetic I A B T (fun i => s₀ i j) hA hB hd hnA hnB
        (fun i hi => ⟨(tests i hi).1,fun _ hx => by
          obtain ⟨hx',_⟩ := mem_filter.mp hx
          have hb := mem_Icc.mp hx'
          have hlen := (hbudget i hi).1
          exact mem_Icc.mpr ⟨hb.1,by omega⟩,by
            have hb := mem_Icc.mp (hinitial i hi j)
            have hlen := (hbudget i hi).1
            exact mem_Icc.mpr ⟨hb.1,by omega⟩⟩)
        (fun i hi => (tests i (hA hi)).2.2.2.1 hi)
        (fun i hi => (tests i (hB hi)).2.2.2.2 hi) (target j)
        ((add_le_add_left (sum_le_sum fun i hi => (tests i hi).2.1) _).trans hl)
        (hh.trans (sub_le_sub_right (sum_le_sum fun i hi => (tests i hi).2.2.1) _)) he
      let next := fun i => Function.update (s i) j (v i)
      refine ⟨next,?_,?_,?_⟩
      · intro i hi
        obtain ⟨_,hp,h1,_,_⟩ := hbudget i hi
        have keep : weight i * count i (s i) ≤ count i (next i) := by
          by_cases hiE : i ∈ E
          · have hv' : v i = s i j := (hE i hiE).trans (hrest i j hj).symm
            simp only [next,hv',Function.update_eq_self]
            exact mul_le_of_le_one_left (Nat.cast_nonneg _) h1
          · obtain ⟨_,hprob⟩ := mem_filter.mp (hv i hi hiE)
            exact (mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ) |>.mpr
              (card_le_card (fiber_sub_other (pool i) (entry i) (s i) j))) hp.le).trans hprob
        rw [card_insert_of_notMem hj, pow_succ']
        rw [mul_assoc]
        exact (mul_le_mul_of_nonneg_left (hm i hi) hp.le).trans keep
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · simpa [next] using hvsum
        · have hne : k ≠ j := ne_of_mem_of_not_mem hk hj
          simpa [next,Function.update_of_ne hne] using hs k hk
      · intro i k hk
        have hne : k ≠ j := fun h => hk (h ▸ mem_insert_self ..)
        simpa [next,Function.update_of_ne hne] using hrest i k (fun h => hk (mem_insert_of_mem h))
  obtain ⟨s,hm,hs,hrest⟩ := advance R Subset.rfl
  have pos (i : I) : (profileFiber (pool i) (entry i) (s i)).Nonempty := by
    apply card_pos.mp
    have h := hbudget i i.property
    have h' := h.2.2.2.1.trans_le (h.2.2.2.2.trans (hm i i.property))
    exact Nat.cast_pos.mp (show 0 < ((profileFiber (pool i) (entry i) (s i)).card : ℝ) from h')
  choose x hx using pos
  have he (i : I) := (mem_filter.mp (hx i)).2
  refine ⟨x, fun i => (mem_filter.mp (hx i)).1, ?_, ?_⟩
  · intro j hj
    simpa [he, Finset.sum_attach] using (show (∑ i : I, s i j) = target j by
      simpa only [← Finset.sum_attach I (fun i => s i j), attach_eq_univ] using hs j hj)
  · intro i j hj
    rw [he i]
    exact hrest i j hj

end InducedDegreeRepetition
