module

public import Ramsey
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

open Finset
open scoped Classical

/-- Finite multicolour Ramsey with a bound independent of the host. -/
theorem palette_ramsey {κ : Type*} (C : Finset κ) (s : ℕ) :
    ∃ R : ℕ, ∀ {V : Type} (S : Finset V) (color : V → V → κ),
      R ≤ S.card → (∀ x y, color x y = color y x) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → color x y ∈ C) →
      ∃ (T : Finset V) (k : κ), T ⊆ S ∧ T.card = s ∧
        ∀ x ∈ T, ∀ y ∈ T, x ≠ y → color x y = k := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    refine ⟨2,?_⟩
    intro V S color hS _ hmem
    obtain ⟨x,hx,y,hy,hn⟩ := one_lt_card.mp (show 1 < S.card by omega)
    exact (notMem_empty _ (hmem x hx y hy hn)).elim
  | @insert k C hk ih =>
    obtain ⟨R,ih⟩ := ih
    refine ⟨4^(max s R),?_⟩
    intro V S color hS hsym hmem
    let G : SimpleGraph V :=
      { Adj := fun x y => x ≠ y ∧ color x y = k
        symm := ⟨fun x y h => ⟨h.1.symm,(hsym y x).trans h.2⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
    obtain ⟨T,hTS,hT,pos | neg⟩ := ramsey_colored_witness G _ S hS
    · obtain ⟨U,hUT,hU⟩ := exists_subset_card_eq (s := T) (n := s) (by omega)
      exact ⟨U,k,hUT.trans hTS,hU,fun x hx y hy hn => ((pos x (hUT hx) y (hUT hy) hn).mpr trivial).2⟩
    · obtain ⟨U,j,hUT,hU,hc⟩ := ih T color (by omega) hsym (fun x hx y hy hn => by
        apply (mem_insert.mp (hmem x (hTS hx) y (hTS hy) hn)).resolve_left
        exact fun he => (neg x hx y hy hn).mp ⟨hn,he⟩)
      exact ⟨U,j,hUT.trans hTS,hU,hc⟩

/-- In a sparse symmetric forbidden relation, k vertices can be chosen with
no forbidden pair. Reflexive forbidden pairs ensure distinct choices. -/
theorem select_avoiding_sparse {V : Type*} (S : Finset V) (bad : V → V → Prop)
    (k : ℕ) (hS : S.Nonempty) (self : ∀ x ∈ S, bad x x)
    (symm : ∀ x y, bad x y → bad y x)
    (few : (∑ x ∈ S, ((S.filter (bad x)).card : ℝ)) * (8*(k+1:ℝ)) ≤ (S.card : ℝ)^2) :
    ∃ T ⊆ S, T.card = k ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬bad x y := by
  classical
  let m := (S.card : ℝ)
  let a := m/(2*((k:ℝ)+1))
  let N := fun x => S.filter (bad x)
  let L := S.filter fun x => ((N x).card : ℝ) ≤ a
  let H := S \ L
  have hm : 0 < m := by dsimp [m]; exact_mod_cast card_pos.mpr hS
  have ha : 0 < a := by dsimp [a]; positivity
  have eqn : a*(2*((k:ℝ)+1)) = m := div_mul_cancel₀ _ (by positivity)
  have freq : (H.card : ℝ) * a ≤ ∑ x ∈ S, ((N x).card : ℝ) := by
    calc
      _ = ∑ _ ∈ H, a := by simp
      _ ≤ ∑ x ∈ H, ((N x).card : ℝ) := sum_le_sum fun x hx => by
        obtain ⟨hxS,hxL⟩ := mem_sdiff.mp (show x ∈ H from hx)
        exact (lt_of_not_ge fun he => hxL (mem_filter.mpr ⟨hxS,he⟩)).le
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => Nat.cast_nonneg _
  have light : m < 2*L.card := by
    have hpart : (H.card : ℝ) + L.card = m := by
      dsimp [H,m]; exact_mod_cast card_sdiff_add_card_eq_card (show L ⊆ S from filter_subset ..)
    have hsmall : (H.card : ℝ)* (4*m) ≤ m^2 := by
      calc
        _ = ((H.card : ℝ)*a) * (8*((k:ℝ)+1)) := by rw [← eqn]; ring
        _ ≤ _ := (mul_le_mul_of_nonneg_right freq (by positivity)).trans few
    nlinarith [show 0 < m^2 by positivity, mul_pos hm hm,
      (mul_le_mul_iff_left₀ hm).mp (show (4*H.card) * m ≤ m * m by nlinarith)]
  have build (j : ℕ) (hj : j ≤ k) : ∃ T ⊆ L, T.card = j ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬bad x y := by
    induction j with
    | zero => exact ⟨∅,empty_subset _,card_empty,by simp⟩
    | succ j ih =>
      obtain ⟨T,hTL,hT,hh⟩ := ih (by omega)
      let E := T.biUnion N
      have hcount : (E.card : ℝ) ≤ (j:ℝ)*a := by
        calc
          _ ≤ ∑ x ∈ T, ((N x).card : ℝ) := by exact_mod_cast (card_biUnion_le (s := T) (t := N))
          _ ≤ ∑ _ ∈ T, a := sum_le_sum fun x hx => (mem_filter.mp (hTL hx)).2
          _ = _ := by simp [hT]
      have jbound : (j:ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast (show j ≤ k+1 by omega)
      have less : E.card < L.card := by
        exact_mod_cast (show (E.card : ℝ) < L.card by nlinarith [mul_le_mul_of_nonneg_right jbound ha.le])
      obtain ⟨v,hvL,hvE⟩ := exists_mem_notMem_of_card_lt_card less
      have clean (x) (hx : x ∈ T) : ¬bad x v := fun he => hvE (mem_biUnion.mpr
        ⟨x,hx,mem_filter.mpr ⟨(mem_filter.mp hvL).1,he⟩⟩)
      have hvT : v ∉ T := fun hv => clean v hv (self v (mem_filter.mp hvL).1)
      refine ⟨insert v T,insert_subset hvL hTL,by simp [hvT,hT],?_⟩
      intro x hx y hy hn
      rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hy with rfl | hy
      · exact (hn rfl).elim
      · exact fun he => clean _ hy (symm _ _ he)
      · exact clean _ ((mem_insert.mp hx).resolve_left hn)
      · exact hh _ hx _ hy hn
  obtain ⟨T,ht,hc,hh⟩ := build k le_rfl
  exact ⟨T,ht.trans (filter_subset ..),hc,hh⟩

end InducedDegreeRepetition
