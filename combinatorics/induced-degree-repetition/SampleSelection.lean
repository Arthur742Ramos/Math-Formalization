module

public import ExteriorLists
public import TesterMoments
public import ReferenceCounts
public import DrawCollisions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V : Type}

theorem sample_selection {g n s : ℕ} (G : SimpleGraph V) (T : Finset V) [Nonempty T] (p θ : ℝ)
    (Xs : Fin g → Fin n → List (Finset V)) [∀ j i, Nonempty ↥(tupleSpace (Xs j i))]
    (m : ℕ) (v κ count ε D : ℝ) (vp : 0 < v) (kp : 0 < κ) (cp : 0 < count) (ep : 0 ≤ ε)
    (coll : ((g*s:ℕ):ℝ)^2/T.card ≤ 1/8)
    (spectrum : mean (fun ys : Fin g × Fin s → T => fourthMoment (fun i j => centered G p (ys i) (ys j)) univ) ≤ κ^2/8)
    (refBound : ∀ j, mean (fun y : T => mean (fun ref : ∀ i, tupleSpace (Xs j i) =>
      ((∑ i, (tupleDegree (adj G) y (ref i):ℝ))-p*m)^2)) ≤ D)
    (total : ((g*s:ℕ):ℝ)*(g*(D/v^2)) ≤ count/8) (eg : g*ε ≤ 1/8)
    (edit : ∀ j (o : {k : Fin g // k ≠ j} → Fin s → T),
      let ex := exteriorList j (fun k t => (o k t:V))
      let draws := (Fintype.piFinset fun i => tupleSpace (Xs j i)) ×ˢ (Fintype.piFinset fun _ : Fin s => T)
      ((draws.filter fun z => ¬Adjustable G θ (Xs j) (fun _ => ex) z.1 z.2).card:ℝ) ≤ ε*draws.card) :
    ∃ (ref : ∀ j i, ↥(tupleSpace (Xs j i))) (ys : Fin g → Fin s → T),
      Function.Injective (fun z : Fin g × Fin s => ys z.1 z.2) ∧
      fourthMoment (fun i j : Fin g × Fin s => centered G p (ys i.1 i.2) (ys j.1 j.2)) univ ≤ κ^2 ∧
      ((univ.filter (fun z : Fin g × Fin s => ∃ j, v < |(∑ i, (tupleDegree (adj G) (ys z.1 z.2) (ref j i):ℝ))-p*m|)).card:ℝ) ≤ count ∧
      ∀ j, Adjustable G θ (Xs j) (fun _ => exteriorList j (fun k t => (ys k t:V))) (fun i => (ref j i).val)
        (fun t => (ys j t).val) := by
  classical
  let R (j : Fin g) := ∀ i, ↥(tupleSpace (Xs j i))
  let Ω := (∀ j, R j) × (Fin g → Fin s → T)
  let fail (z : Ω) (j : Fin g) := ¬Adjustable G θ (Xs j) (fun _ => exteriorList j (fun k t => (z.2 k t:V)))
    (fun i => (z.1 j i).val) (fun t => (z.2 j t).val)
  let err (j : Fin g) (ref : R j) (y : T) := (∑ i, (tupleDegree (adj G) y (ref i):ℝ))-p*m
  let bad (z : Ω) := (univ.filter (fun k : Fin g × Fin s => ∃ j, v < |err j (z.1 j) (z.2 k.1 k.2)|)).card
  let mom (w : Fin g × Fin s → T) := fourthMoment (fun i j => centered G p (w i) (w j)) univ
  have ignore (f : (Fin g × Fin s → T) → ℝ) :
      mean (fun z : Ω => f (fun k => z.2 k.1 k.2)) = mean f := by
    rw [mean_prod (fun (_ : ∀ j,R j) (ys : Fin g → Fin s → T) => f (fun k => ys k.1 k.2)),mean_const,mean_flatten]
  have c₀ := ignore (fun w => indicator (¬Function.Injective w))
  have c₁ : mean (fun z : Ω => indicator (¬Function.Injective (fun k : Fin g × Fin s => z.2 k.1 k.2))) ≤ 1/8 := by
    rw [c₀]
    have h := collision_mean (I:=Fin g × Fin s) (X:=T)
    convert h.trans (by simpa [Fintype.card_prod] using coll : (Fintype.card (Fin g × Fin s):ℝ)^2 / Fintype.card T ≤ 1/8) using 1
    apply congrArg mean
    funext w
    by_cases inj : Function.Injective w <;> simp [indicator,inj]
  have c₂ : mean (fun z : Ω => indicator (κ^2 < mom (fun k => z.2 k.1 k.2))) ≤ 1/8 := by
    rw [ignore (fun w => indicator (κ^2 < mom w))]
    have h := mean_markov mom (κ^2) (by positivity) (fun w => by dsimp [mom,fourthMoment]; positivity)
    apply h.trans
    rw [div_le_iff₀ (by positivity : 0 < κ^2)]
    linarith
  have c₃ : mean (fun z : Ω => indicator (count < (bad z:ℝ))) ≤ 1/8 := by
    have h := mean_markov (fun z : Ω => (bad z:ℝ)) count cp (fun _ => Nat.cast_nonneg _)
    apply h.trans
    rw [div_le_iff₀ cp]
    apply (reference_bad_count (s:=s) R err v D vp refBound).trans
    linarith
  have c₄ := (mean_union (fun j (z : Ω) => fail z j) ε (fun j => group_failure G T θ ε ep Xs j (edit j))).trans
    (by simpa using eg : (Fintype.card (Fin g):ℝ)*ε ≤ 1/8)
  obtain ⟨z,inj,small,few,edits⟩ := choose_four _ _ _ _ c₁ c₂ c₃ c₄
  exact ⟨z.1,z.2,not_not.mp inj,le_of_not_gt small,le_of_not_gt few,fun j => not_not.mp (fun h => edits ⟨j,h⟩)⟩

end InducedDegreeRepetition.Sampling
