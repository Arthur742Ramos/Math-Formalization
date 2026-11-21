module

public import RegularSelection
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

open Finset
open scoped Classical

private theorem delete_bad_sets {V : Type*} (A : Finset V) (F : Finset (Finset V))
    (hne : ∀ S ∈ F, S.Nonempty) :
    ∃ T ⊆ A, A.card ≤ T.card + F.card ∧ ∀ S ∈ F, ¬ S ⊆ T := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨A,Subset.rfl,by simp,by simp⟩
  | @insert S F hS ih =>
    obtain ⟨T,hT,hc,hfree⟩ := ih fun S' h => hne _ (mem_insert_of_mem h)
    obtain ⟨x,hx⟩ := hne S (mem_insert_self ..)
    refine ⟨T.erase x,(erase_subset ..).trans hT,?_,?_⟩
    · rw [card_insert_of_notMem hS]
      by_cases h : x ∈ T
      · have := card_erase_add_one h; omega
      · simpa [erase_eq_of_notMem h] using hc.trans (by omega)
    · intro S' h hh
      rcases mem_insert.mp h with rfl | h
      · exact (mem_erase.mp (hh hx)).1 rfl
      · exact hfree _ h (hh.trans (erase_subset ..))

private theorem counts_as_sum {α : Type*} (U : Finset α) (p : α → Prop) :
    ((U.filter p).card : ℝ) = ∑ x ∈ U, if p x then (1:ℝ) else 0 := by
  classical
  rw [← sum_filter]; simp

private theorem exchange_counts {V W : Type*} (S : Finset V) (T : Finset W) (R : V → W → Prop) :
    (∑ x ∈ S, ((T.filter (R x)).card : ℝ)) = ∑ y ∈ T, ((S.filter fun x => R x y).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ S, ∑ y ∈ T, if R x y then (1:ℝ) else 0 :=
      sum_congr rfl fun x _ => counts_as_sum T (R x)
    _ = ∑ y ∈ T, ∑ x ∈ S, if R x y then (1:ℝ) else 0 := sum_comm
    _ = _ := sum_congr rfl fun y _ => (counts_as_sum S fun x => R x y).symm

/-- Quantitative dependent random choice. Every s-subset of the resulting large
set has at least a λ fraction of the tester set as common neighbors. The proof
counts all ordered samples with replacement and deletes one point per bad set. -/
theorem dependent_choice {V W : Type*} (H : Finset V) (Y : Finset W) (R : V → W → Prop)
    (s t target : ℕ) (hs : 0 < s) (hY : Y.Nonempty) (d b : ℝ) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (degree : ∀ x ∈ H, d*Y.card ≤ ((Y.filter (R x)).card : ℝ))
    (budget : (target : ℝ) + (H.card : ℝ)^s * b^t < H.card * d^t) :
    ∃ T ⊆ H, target ≤ T.card ∧ ∀ S ⊆ T, S.card = s →
      b*Y.card ≤ ((Y.filter fun y => ∀ x ∈ S, R x y).card : ℝ) := by
  classical
  let Ω := Fintype.piFinset fun _ : Fin t => Y
  let A := fun ω : Fin t → W => H.filter fun x => ∀ i, R x (ω i)
  let N := fun S : Finset V => Y.filter fun y => ∀ x ∈ S, R x y
  let F := (H.powersetCard s).filter fun S => ((N S).card : ℝ) < b*Y.card
  let B := fun ω : Fin t → W => F.filter fun S => S ⊆ A ω
  have cardΩ : Ω.card = Y.card^t := by simp [Ω]
  have Ωpos : 0 < (Ω.card : ℝ) := by rw [cardΩ,Nat.cast_pow]; positivity [card_pos.mpr hY]
  have restrict (Z : Finset W) (hz : Z ⊆ Y) :
      (Ω.filter fun ω => ∀ i, ω i ∈ Z) = Fintype.piFinset fun _ : Fin t => Z := by
    ext f
    simp only [mem_filter,Fintype.mem_piFinset,Ω]
    exact ⟨And.right,fun h => ⟨fun i => hz (h i),h⟩⟩
  have single (x : V) : (Ω.filter fun ω => ∀ i, R x (ω i)) =
      Fintype.piFinset fun _ : Fin t => Y.filter (R x) := by
    rw [← restrict _ (filter_subset ..)]
    ext f
    simp only [mem_filter,Fintype.mem_piFinset,Ω]
    grind
  have totalA : (Ω.card : ℝ) * (H.card * d^t) ≤ ∑ ω ∈ Ω, ((A ω).card : ℝ) := by
    rw [show (∑ ω ∈ Ω, ((A ω).card : ℝ)) = ∑ x ∈ H,
      ((Ω.filter fun ω => ∀ i, R x (ω i)).card : ℝ) from by
        convert! exchange_counts Ω H (fun ω x => ∀ i, R x (ω i)) using 1 <;>
          apply sum_congr rfl <;> intro x _ <;> congr 1 <;> apply congrArg Finset.card <;> ext y <;> simp [A]]
    calc
      _ = ∑ _ ∈ H, (d*(Y.card:ℝ))^t := by simp [cardΩ, mul_pow]; ring
      _ ≤ _ := sum_le_sum fun x hx => by
        rw [single]
        simp only [Fintype.card_piFinset_const,Nat.cast_pow]
        exact pow_le_pow_left₀ (by positivity) (degree x hx) t
  have multiple (S) (hS : S ∈ F) : (Ω.filter fun ω => S ⊆ A ω) =
      Fintype.piFinset fun _ : Fin t => N S := by
    have hSH := (mem_powersetCard.mp (mem_filter.mp hS).1).1
    rw [← restrict _ (filter_subset ..)]
    ext f
    simp only [A,Ω,mem_filter,Fintype.mem_piFinset,subset_iff]
    grind
  have cardF : F.card ≤ H.card^s :=
    (card_filter_le ..).trans (by rw [card_powersetCard]; exact Nat.choose_le_pow ..)
  have totalB : (∑ ω ∈ Ω, ((B ω).card : ℝ)) ≤ (Ω.card : ℝ) * ((H.card : ℝ)^s * b^t) := by
    rw [show (∑ ω ∈ Ω, ((B ω).card : ℝ)) = ∑ S ∈ F, ((Ω.filter fun ω => S ⊆ A ω).card : ℝ)
      from by
        convert! exchange_counts Ω F (fun ω S => S ⊆ A ω) using 1 <;>
          apply sum_congr rfl <;> intro x _ <;> congr 1 <;> apply congrArg Finset.card <;> ext y <;> simp [B]]
    calc
      _ ≤ ∑ _ ∈ F, (b*(Y.card:ℝ))^t := sum_le_sum fun S hS => by
        rw [multiple S hS]
        simp only [Fintype.card_piFinset_const,Nat.cast_pow]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (mem_filter.mp hS).2.le t
      _ = F.card * (b*(Y.card:ℝ))^t := by simp
      _ ≤ (H.card : ℝ)^s * (b*(Y.card:ℝ))^t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast cardF) (by positivity)
      _ = _ := by rw [cardΩ,Nat.cast_pow,mul_pow]; ring
  have win : ∃ ω ∈ Ω, target + (B ω).card ≤ (A ω).card := by
    by_contra! h
    have bad := sum_le_sum (s := Ω) fun ω hω =>
      (show ((A ω).card : ℝ) ≤ (target : ℝ) + (B ω).card by exact_mod_cast (h ω hω).le)
    rw [sum_add_distrib,sum_const,nsmul_eq_mul] at bad
    nlinarith [mul_lt_mul_of_pos_left budget Ωpos]
  obtain ⟨ω,_,hw⟩ := win
  obtain ⟨T,hT,cardT,free⟩ := delete_bad_sets (A ω) (B ω) (fun S h => by
    have hh := (mem_powersetCard.mp (mem_filter.mp (mem_filter.mp h).1).1).2
    exact card_pos.mp (by omega))
  refine ⟨T,hT.trans (filter_subset ..),by omega,?_⟩
  intro S hST hcard
  by_contra! bad
  have hSA := hST.trans hT
  exact free S (mem_filter.mpr ⟨mem_filter.mpr
    ⟨mem_powersetCard.mpr ⟨hSA.trans (filter_subset ..),hcard⟩,bad⟩,hSA⟩) hST

end InducedDegreeRepetition
