module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sigma

public section
namespace InducedDegreeRepetition

open Finset
open scoped Classical

/-- For a uniform reference, bound the number of draws landing in a small cell of
its profile partition. This applies to both successive exposures in Lemma 11. -/
theorem small_profile_cells {X S : Type*} [Fintype S] (pool : Finset X) (p : X → S)
    (v : ℝ) (hv : 0 ≤ v) :
    ((pool.filter fun x => (((pool.filter fun y => p y = p x).card : ℝ) < v)).card : ℝ) ≤
      Fintype.card S * v := by
  classical
  let small := univ.filter fun s => (((pool.filter fun y => p y = s).card : ℝ) < v)
  have eqn := sum_card_fiberwise_eq_card_filter pool small p
  have ha : (pool.filter fun x => p x ∈ small) =
      pool.filter fun x => (((pool.filter fun y => p y = p x).card : ℝ) < v) := by
    ext; simp [small]
  rw [← ha, ← eqn, Nat.cast_sum]
  calc
    _ ≤ ∑ _ ∈ small, v := sum_le_sum fun i hi => ((mem_filter.mp hi).2).le
    _ = (small.card : ℝ) * v := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_univ _)) hv

private theorem unionBound {α β : Type*} [DecidableEq β] (T : Finset α) (E : α → Finset β) :
      ((T.biUnion E).card : ℝ) ≤ ∑ i ∈ T, ((E i).card : ℝ) := by
    exact_mod_cast card_biUnion_le (s := T) (t := E)

/-- The leave-one-out union bound in Lemma 11. For each possible profile on *all
other rows*, the exceptional tester set can depend on those rows and that profile.
In the uniform product space of row lists the bound holds simultaneously, before
any targets are chosen. The profile type may depend on the omitted row. -/
theorem exceptional_profile_lists {I Y : Type*} [Fintype I] [Fintype Y]
    (S : I → Type*) [∀ i, Fintype (S i)]
    (bad : (i : I) → ({j : I // j ≠ i} → Y) → S i → Finset Y)
    (ε : ℝ) (h : ∀ i ys s, ((bad i ys s).card : ℝ) ≤ ε * Fintype.card Y) :
    ((univ.filter fun ys : I → Y =>
      ∃ (i : I) (s : S i), ys i ∈ bad i (fun j => ys j) s).card : ℝ) ≤
      (∑ i, (Fintype.card (S i) : ℝ)) * ε * Fintype.card (I → Y) := by
  classical
  let event (i : I) (s : S i) := univ.filter fun ys : I → Y => ys i ∈ bad i (fun j => ys j) s
  have single (i : I) (s : S i) : ((event i s).card : ℝ) ≤ ε * Fintype.card (I → Y) := by
    let Rest := {j : I // j ≠ i} → Y
    let cells := univ.sigma fun ys : Rest => bad i ys s
    have same : (event i s).card = cells.card := by
      apply card_bij' (fun ys _ => ⟨fun j => ys j, ys i⟩)
        (fun p _ => (Equiv.funSplitAt i Y).symm (p.2,p.1))
      · intro a _
        exact (Equiv.funSplitAt i Y).symm_apply_apply a
      · rintro ⟨ys,y⟩ _
        have hh := (Equiv.funSplitAt i Y).apply_symm_apply (y,ys)
        exact congrArg (fun p : Y × Rest => (⟨p.2,p.1⟩ : (_ : Rest) × Y)) hh
      · intro a ha
        simpa [cells, event] using ha
      · rintro ⟨ys,y⟩ hy
        have hh := (Equiv.funSplitAt i Y).apply_symm_apply (y,ys)
        change ((Equiv.funSplitAt i Y).symm (y,ys) i,
          fun j : {j : I // j ≠ i} => (Equiv.funSplitAt i Y).symm (y,ys) j) = (y,ys) at hh
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        rw [show ((Equiv.funSplitAt i Y).symm (y,ys)) i = y from congrArg Prod.fst hh,
          show (fun j : {j : I // j ≠ i} => (Equiv.funSplitAt i Y).symm (y,ys) j) = ys from
            congrArg Prod.snd hh]
        exact (mem_sigma.mp hy).2
    have hc := Fintype.card_congr (Equiv.funSplitAt i Y)
    rw [Fintype.card_prod] at hc
    rw [same, card_sigma, Nat.cast_sum, hc, Nat.cast_mul]
    calc
      _ ≤ ∑ _ : Rest, ε * Fintype.card Y := sum_le_sum fun ys _ => h i ys s
      _ = _ := by simp [Rest]; ring
  have allEvents : (univ.filter fun ys : I → Y =>
      ∃ (i : I) (s : S i), ys i ∈ bad i (fun j => ys j) s) =
      univ.biUnion fun i => univ.biUnion (event i) := by ext; simp [event]
  rw [allEvents]
  calc
    _ ≤ ∑ i, ((univ.biUnion (event i)).card : ℝ) := unionBound _ _
    _ ≤ ∑ i, ∑ _ : S i, ε * Fintype.card (I → Y) :=
      sum_le_sum fun i _ => (unionBound univ (event i)).trans (sum_le_sum fun s _ => single i s)
    _ = (∑ i, (Fintype.card (S i) : ℝ)) * ε * Fintype.card (I → Y) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, sum_mul, mul_assoc]

end InducedDegreeRepetition
