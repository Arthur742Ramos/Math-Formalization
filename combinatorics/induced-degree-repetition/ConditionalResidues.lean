module

public import RestrictedAtoms
public import ConditioningBound
public import DyadicRates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.OpenProblems

open Finset Filter Duality Residues
open scoped Classical Topology

private theorem tuples_nonempty {V : Type*} (l : List (Finset V))
    (h : ∀ X ∈ l, X.Nonempty) : (tupleSpace l).Nonempty := by
  induction l with
  | nil => exact singleton_nonempty _
  | cons X l ih =>
    obtain ⟨x,hx⟩ := h X (by simp)
    obtain ⟨p,hp⟩ := ih fun Z hz => h Z (by simp [hz])
    exact ⟨x::p,mem_map.mpr ⟨(x,p),mem_product.mpr ⟨hx,hp⟩,rfl⟩⟩

set_option maxHeartbeats 900000 in
/-- Lemma 8. A positive fraction of a conditioned tuple family realizes each of
two distinct residues, outside an exponentially small set of testers. -/
theorem conditional_residues : ConditionalResidues := by
  classical
  intro q hq u τ c hu hτ hc
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨a,ha,rnd⟩ := random_restrictions q hq u τ c hu hτ hc
  obtain ⟨κ,hκ,levels⟩ := all_level_bounds q (by omega) a ha
  refine ⟨residueRate a κ,rate_limit a κ ha hκ,?_⟩
  intro j _
  dsimp only
  intro D _ hd
  let A := levelRate a κ j
  have ap : 0 < A := by dsimp [A,levelRate]; positivity
  have gap : D < A := by rw [dyadic_rate] at hd; change D < A/2 at hd; linarith
  obtain ⟨K,hK,amp⟩ := levels j 1 zero_lt_one
  obtain ⟨C,β,hC,hβ,prob⟩ := rnd K hK
  obtain ⟨ξ,hξ,hhalf,rates⟩ := conditioning_rates D A C β (2^j) gap hC hβ (by positivity)
  refine ⟨u/16,ξ/((2^j:ℕ)+1),by positivity,by positivity,?_⟩
  filter_upwards [amp,prob,rates] with r amp prob rate
  intro N G B Y Xs Q core positional len sub mass
  let f := tupleDegree (adj G)
  let heavy (y : Fin N) (s : ZMod q) := (1-ξ)*Q.card <
    ((Q.filter fun P => (f y P : ZMod q) = s).card:ℝ)
  let E := Y.filter (fun y => ∃ s, heavy y s)
  have ey : E ⊆ Y := filter_subset ..
  have bp : 0 < (B.card:ℝ) := pos_of_mul_pos_left ((Real.exp_pos _).trans_le core.1) (Real.exp_pos _).le
  have nonempty (X) (hx : X ∈ Xs) : X.Nonempty := by
    apply card_pos.mp
    exact_mod_cast (mul_pos bp (Real.exp_pos _)).trans_le (positional.2 X hx).1.2
  have tp := tuples_nonempty _ nonempty
  have qp : 0 < Q.card := by
    exact_mod_cast (mul_pos (Real.exp_pos _) (show 0 < ((tupleSpace Xs).card:ℝ) by exact_mod_cast card_pos.mpr tp)).trans_le mass
  have ecut : (E.card:ℝ) ≤ B.card*Real.exp (-u*r/8) := by
    by_contra! large
    have en : E.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos bp (Real.exp_pos _)).trans large)
    have le : Large B E r u 8 := ⟨ey.trans positional.1.1,large.le⟩
    let n := ⌈C*r⌉₊
    let lists := Fintype.piFinset fun _ : Fin n => E
    let bad (ys : Fin n → Fin N) := ∃ X ∈ Xs, HeavyRestriction q G X ys r K a
    let t (y : Fin N) := if h : ∃ s, heavy y s then h.choose else 0
    have high (y) (hy : y ∈ E) : heavy y (t y) := by
      have h := (mem_filter.mp hy).2
      simp only [t,dite_eq_left h]
      exact h.choose_spec
    have rare (X) (hx : X ∈ Xs) :
        ((lists.filter fun ys => HeavyRestriction q G X ys r K a).card:ℝ) ≤
          Real.exp (-β*(r:ℝ)^2)*lists.card := by
      obtain ⟨⟨xb,xc⟩,dis⟩ := positional.2 X hx
      have cut : B.card*Real.exp (-u*r/8) ≤ B.card*Real.exp (-u*r/16) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (Nat.cast_nonneg _)
        nlinarith [mul_nonneg hu.le (Nat.cast_nonneg r : (0:ℝ)≤r)]
      exact prob N G B X E core (dis.mono_right ey) ⟨xb,cut.trans xc⟩ le
    have union := union_bad_lists Xs lists (fun X ys => HeavyRestriction q G X ys r K a)
      _ (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) rare
    have per (ys : Fin n → Fin N) (_ : ys ∈ lists) (good : ¬bad ys) :=
      typical_atom G ys Xs a K A j len nonempty
        (amp (Fin n → ZMod q) (ZModModule.char_nsmul_eq_zero q))
        (fun X hx h => good ⟨X,hx,h⟩) (fun i => t (ys i))
    apply conditioning_impossible Q (tupleSpace Xs) E n (fun P y => (f y P : ZMod q) = t y)
      bad (Real.exp (-D*r)) (Real.exp (-A*r)) ((2^j:ℕ)*Real.exp (-β*(r:ℝ)^2)) ξ
      hξ hhalf (Real.exp_pos _).le tp en sub mass rate ?_ ?_ ?_
    · intro y hy
      convert (high y hy).le using 1
      apply congrArg Nat.cast
      apply congrArg Finset.card
      ext p
      simp
    · intro ys hy good
      convert per ys hy good using 1
      apply congrArg Nat.cast
      apply congrArg Finset.card
      ext P
      simp [f]
    · rw [len] at union
      convert union using 1
      · apply congrArg Nat.cast
        apply congrArg Finset.card
        ext ys
        simp [bad,lists,Fintype.mem_piFinset]
      · ring
  refine ⟨E,ey,ecut.trans ?_,?_⟩
  · calc
      _ = Real.exp (-(u/16)*r)*(B.card*Real.exp (-u*r/16)) := by
        rw [mul_left_comm,← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left positional.1.2 (Real.exp_pos _).le
  · intro y hy out
    apply separated_atoms Q (f y) (2^j) _ ξ hξ (by linarith) qp
    · intro s
      exact le_of_not_gt fun h => out (mem_filter.mpr ⟨hy,s,h⟩)
    · intro P hP
      exact (List.countP_le_length ..).trans ((tuple_len (sub hP)).trans len).le

end InducedDegreeRepetition.OpenProblems
