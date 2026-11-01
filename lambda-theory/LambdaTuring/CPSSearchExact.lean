/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.HeadSearch
public meta import LambdaTuring.HeadSearch

@[expose] public section

open Nat.Partrec

namespace LambdaTuring

/-- If strict search is undefined, either a first undefined test blocks it,
    or every test is defined and positive. -/
theorem strictSearch_none_cases (p : Nat →. Nat) (start : Nat)
    (hnone : (Nat.rfind (fun n => (fun v => v = 0) <$> p n)).map (fun d => d + start) = Part.none) :
    (∃ d, p d = Part.none ∧ ∀ j, j < d → ∃ v, v + 1 ∈ p j) ∨
      (∀ j, ∃ v, v + 1 ∈ p j) := by
  classical
  by_cases hall : ∀ j, ∃ v, v + 1 ∈ p j
  · exact Or.inr hall
  · have hex : ∃ j, ¬ ∃ v, v + 1 ∈ p j := by simpa using hall
    let d := Nat.find hex
    have hbad : ¬ ∃ v, v + 1 ∈ p d := Nat.find_spec hex
    have hprior : ∀ j, j < d → ∃ v, v + 1 ∈ p j := by
      intro j hj
      exact Classical.not_not.mp (Nat.find_min hex hj)
    have hblocked : p d = Part.none := by
      apply Part.eq_none_iff.2
      intro m hm
      cases m with
      | succ v => exact hbad ⟨v, by simpa using hm⟩
      | zero =>
        let test : Nat →. Bool := fun n => (fun v => v = 0) <$> p n
        have hz : true ∈ test d := by
          change true ∈ Part.map (fun v : Nat => decide (v = 0)) (p d)
          exact (Part.mem_map_iff _).2 ⟨0, hm, by simp⟩
        have hp : ∀ {j}, j < d → false ∈ test j := by
          intro j hj
          obtain ⟨v, hv⟩ := hprior j hj
          change false ∈ Part.map (fun v : Nat => decide (v = 0)) (p j)
          exact (Part.mem_map_iff _).2 ⟨v + 1, hv, by simp⟩
        have hd : d ∈ Nat.rfind test := Nat.mem_rfind.2 ⟨hz, hp⟩
        have hx : d + start ∈ (Nat.rfind test).map (fun k => k + start) :=
          (Part.mem_map_iff _).2 ⟨d, hd, rfl⟩
        rw [hnone] at hx
        simp at hx
    exact Or.inl ⟨d, hblocked, hprior⟩

/-- The missing hypotheses are explicit: head standardization and conversion
    from ordinary CPS representation to observable head progress. -/
theorem cpsMinimize_code_conditional {G : Term} {f : Nat.Partrec.Code}
    (hg : CPSRepresents G (Nat.Partrec.Code.eval f))
    (standardization : WeakNormalizationImpliesHeadAccessible)
    (progress : ∀ (x : Nat), (∀ j, ∃ v, v + 1 ∈ Nat.Partrec.Code.eval f
        (Nat.pair x.unpair.1 (x.unpair.2 + j))) →
      SearchHeadPositive G x.unpair.1 x.unpair.2) :
    CPSRepresents (cpsMinimize G) (Nat.Partrec.Code.eval (.rfind' f)) := by
  constructor
  · exact cpsMinimize_closed hg.1
  · intro x K
    constructor
    · intro m hm
      exact cpsMinimize_code_success hg x m K hm
    · intro hnone
      let p : Nat →. Nat := fun j => Nat.Partrec.Code.eval f (Nat.pair x.unpair.1 (j + x.unpair.2))
      have hsearch : (Nat.rfind (fun n => (fun v => v = 0) <$> p n)).map
          (fun d => d + x.unpair.2) = Part.none := by
        simpa [p, Nat.Partrec.Code.eval, Nat.unpaired] using hnone
      rcases strictSearch_none_cases p x.unpair.2 hsearch with ⟨d, hblocked, hprior⟩ | hall
      · apply cpsMinimize_finite_blocked hg x d K
        · intro j hj
          simpa [p, Nat.add_comm] using hprior j hj
        · simpa [p, Nat.add_comm] using hblocked
      · have hall' : ∀ j, ∃ v, v + 1 ∈ Nat.Partrec.Code.eval f
            (Nat.pair x.unpair.1 (x.unpair.2 + j)) := by
          intro j
          simpa [p, Nat.add_comm] using hall j
        exact noNormal_backward (cpsMinimize_run hg.1 x K)
          (cpsSearchLoop_head_positive_no_normal standardization hg.1 x.unpair.1 x.unpair.2 K (progress x hall'))

theorem primrec_cpsMinimize : Primrec cpsMinimize := by
  unfold cpsMinimize cpsSearchLoop lambdaFix fixDelta cpsSearchBody
  repeat' first | exact Primrec.id | exact Primrec.const _ |
    apply primrec_abs.comp | apply primrec_app.comp

#print axioms strictSearch_none_cases
#print axioms cpsMinimize_code_conditional
#print axioms primrec_cpsMinimize

end LambdaTuring
