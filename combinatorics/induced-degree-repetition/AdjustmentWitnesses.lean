module

public import AdjustmentLengths
public import ConditionalResidues
public import GraphRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Edit

open Filter Finset OpenProblems
open scoped Topology Classical

/-- A test on integer atoms. The finite set of requirements comprises one range
test and, for the longer tuples, one test per arithmetic modulus. -/
@[expose] def Meets (L : ℕ) (θ : ℝ) (test : Option ℕ) (k l : ℕ) : Prop :=
  match test with
  | none => (k:ℝ) ≤ θ*L/5 ∧ (1-θ/5)*L ≤ (l:ℝ)
  | some q => ¬ Nat.ModEq q k l

@[expose] def Witnesses {P : Type*} (Q : Finset P) (f : P → ℕ)
    (L : ℕ) (θ w₀ : ℝ) (test : Option ℕ) : Prop :=
  ∃ k l, Meets L θ test k l ∧
    w₀*Q.card ≤ ((Q.filter fun p => f p=k).card:ℝ) ∧
    w₀*Q.card ≤ ((Q.filter fun p => f p=l).card:ℝ)

theorem witnesses_mono {P : Type*} (Q : Finset P) (f : P → ℕ) (L : ℕ) (θ w₀ w₁ : ℝ)
    (test : Option ℕ) (le : w₀ ≤ w₁) (h : Witnesses Q f L θ w₁ test) : Witnesses Q f L θ w₀ test := by
  obtain ⟨k,l,ok,hk,hl⟩ := h
  have m := mul_le_mul_of_nonneg_right le (Nat.cast_nonneg Q.card : (0:ℝ)≤Q.card)
  exact ⟨k,l,ok,m.trans hk,m.trans hl⟩

@[expose] def RowEstimate (u τ c θ : ℝ) (L : ℕ) (tests : List (Option ℕ)) : Prop :=
  ∃ β w₀ : ℝ, 0 < β ∧ 0 < w₀ ∧ ∀ᶠ r : ℕ in atTop,
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B Y : Finset (Fin N))
      (Xs : List (Finset (Fin N))) (Q : Finset (List (Fin N))),
    Core G B r u τ c → Positional B Y Xs r u → Xs.length = L → Q ⊆ tupleSpace Xs →
      Real.exp (-budget L*r)*(tupleSpace Xs).card ≤ Q.card →
      ∃ E ⊆ Y, (E.card:ℝ) ≤ Real.exp (-β*r)*Y.card ∧ ∀ y ∈ Y, y ∉ E →
        ∀ t ∈ tests, Witnesses Q (tupleDegree (adj G) y) L θ w₀ t

theorem combine_rows (u τ c θ : ℝ) (L : ℕ) (s t : List (Option ℕ))
    (h : RowEstimate u τ c θ L s) (g : RowEstimate u τ c θ L t) :
    RowEstimate u τ c θ L (s++t) := by
  obtain ⟨β,w₀,bp,lp,hs⟩ := h
  obtain ⟨γ,w₁,gp,mp,ht⟩ := g
  let b := min β γ/2
  have pos : 0 < b := by dsimp [b]; positivity
  obtain ⟨r₀,hr₀⟩ := exists_nat_gt (Real.log 2/b)
  refine ⟨b,min w₀ w₁,pos,lt_min lp mp,?_⟩
  filter_upwards [hs,ht,eventually_ge_atTop r₀] with r hs ht hr
  intro N G B Y Xs Q core positional len sub mass
  obtain ⟨E,eY,e,he⟩ := hs N G B Y Xs Q core positional len sub mass
  obtain ⟨F,fY,f,hf⟩ := ht N G B Y Xs Q core positional len sub mass
  refine ⟨E∪F,union_subset eY fY,?_,?_⟩
  · have half : Real.log 2 ≤ b*r :=
      (by have z := (div_lt_iff₀ pos).mp (hr₀.trans_le (by exact_mod_cast hr : (r₀:ℝ)≤r)); linarith)
    have term (x : ℝ) (cap : min β γ ≤ x) : Real.exp (-x*r) ≤ Real.exp (-b*r)/2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ)<2),← Real.exp_log (by norm_num : (0:ℝ)<2),← Real.exp_add,Real.exp_le_exp]
      have bound : 2*b ≤ x := by dsimp [b]; linarith
      nlinarith [mul_le_mul_of_nonneg_right bound (Nat.cast_nonneg r : (0:ℝ)≤r)]
    have ec := e.trans (mul_le_mul_of_nonneg_right (term _ (min_le_left ..)) (Nat.cast_nonneg _))
    have fc := f.trans (mul_le_mul_of_nonneg_right (term _ (min_le_right ..)) (Nat.cast_nonneg _))
    have card : ((E∪F).card:ℝ) ≤ E.card+F.card := by exact_mod_cast card_union_le E F
    linarith
  · intro y hy out test incl
    rcases List.mem_append.mp incl with ins|int
    · exact witnesses_mono _ _ _ _ _ _ _ (min_le_left ..) (he y hy (fun w => out (mem_union_left _ w)) test ins)
    · exact witnesses_mono _ _ _ _ _ _ _ (min_le_right ..) (hf y hy (fun w => out (mem_union_right _ w)) test int)

theorem range_rows (u τ c θ : ℝ) (hu : 0 < u) (hτ : 0 < τ) (hθ : 0 < θ) (L : ℕ)
    (bound : budget L ≤ θ*(u/16)*L/10) : RowEstimate u τ c θ L [none] := by
  obtain ⟨β,w₀,bp,lp,range⟩ := conditional_range_on_core u (min τ 1) c θ hu (lt_min hτ zero_lt_one)
    (min_le_right ..) hθ L (budget L) bound
  refine ⟨β,w₀,bp,lp,?_⟩
  filter_upwards [range] with r hr
  intro N G B Y Xs Q core pos len sub mass
  have weak : Core G B r u (min τ 1) c := by
    refine ⟨core.1,?_⟩
    intro X hx Z hz dis x z b
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left τ 1)
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans (core.2 X hx Z hz dis x z b)
  obtain ⟨E,ey,e,out⟩ := hr N G B Y Xs Q weak pos len sub mass
  refine ⟨E,ey,e,?_⟩
  intro y hy good t ht
  have eq := List.mem_singleton.mp ht
  subst t
  obtain ⟨k,l,hk,hl,h₁,h₂⟩ := out y hy good
  exact ⟨k,l,⟨hk,hl⟩,h₁,h₂⟩

end InducedDegreeRepetition.Edit
