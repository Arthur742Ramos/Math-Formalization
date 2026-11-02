/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSWithSuccessor
public meta import LambdaTuring.CPSWithSuccessor

@[expose] public section

namespace LambdaTuring

def selfApply : Term := .abs (.app (.var 0) (.var 0))
def omegaTerm : Term := .app selfApply selfApply
def cpsBottom : Term := .abs (.abs omegaTerm)

theorem selfApply_no_beta : ¬ ∃ t, Beta selfApply t := by
  rintro ⟨t, h⟩
  change Beta (.abs (.app (.var 0) (.var 0))) t at h
  cases h with
  | abs h =>
    cases h with
    | appLeft h => cases h
    | appRight h => cases h

theorem omega_beta_self : Beta omegaTerm omegaTerm := by
  simpa [omegaTerm, selfApply, substAt, liftBy] using
    (Beta.contract (.app (.var 0) (.var 0)) selfApply)

theorem omega_beta_eq {t : Term} (h : Beta omegaTerm t) : t = omegaTerm := by
  change Beta (.app selfApply selfApply) t at h
  cases h with
  | contract body value => rfl
  | appLeft h => exact False.elim (selfApply_no_beta ⟨_, h⟩)
  | appRight h => exact False.elim (selfApply_no_beta ⟨_, h⟩)

theorem omega_reaches_eq {t : Term} (h : Reaches omegaTerm t) : t = omegaTerm := by
  have hstar : ∀ {a b : Term}, Reaches a b → a = omegaTerm → b = omegaTerm := by
    intro a b r
    induction r with
    | refl => exact fun ha => ha
    | step hs _ ih =>
      intro ha
      cases ha
      exact ih (omega_beta_eq hs)
  exact hstar h rfl

theorem omega_no_normal : ¬ ∃ N, Reaches omegaTerm N ∧ ¬ ∃ u, Beta N u := by
  rintro ⟨N, hr, hnormal⟩
  have heq := omega_reaches_eq hr
  subst N
  exact hnormal ⟨omegaTerm, omega_beta_self⟩

theorem omega_closed : Scoped 0 omegaTerm := by simp [omegaTerm, selfApply, Scoped]

theorem cpsBottom_run (n : Nat) (K : Term) :
    Reaches (.app (.app cpsBottom (church n)) K) omegaTerm := by
  have h1 := substAt_scoped omegaTerm 1 (church n) (scoped_mono omega_closed (Nat.zero_le 1))
  have h0 := substAt_scoped omegaTerm 0 K omega_closed
  have hb1 : Beta (.app cpsBottom (church n)) (.abs omegaTerm) := by
    simpa [cpsBottom, substAt, h1] using (Beta.contract (.abs omegaTerm) (church n))
  have hb2 : Beta (.app (.abs omegaTerm) K) omegaTerm := by
    simpa [h0] using (Beta.contract omegaTerm K)
  exact .step (.appLeft hb1) (.step hb2 (.refl _))

theorem cpsBottom_represents : CPSRepresents cpsBottom (fun _ => Part.none) := by
  constructor
  · change Scoped 2 omegaTerm
    exact scoped_mono omega_closed (Nat.zero_le 2)
  · intro n K
    constructor
    · intro m h
      simp at h
    · intro _
      exact noNormal_backward (cpsBottom_run n K) omega_no_normal

/-- Even an outer constant cannot erase an undefined inner CPS computation. -/
theorem cpsConstant_after_bottom (k : Nat) :
    CPSRepresents (cpsCompose (cpsConstant k) cpsBottom) (fun _ => Part.none) := by
  have h := cpsCompose_represents (cpsConstant_represents k) cpsBottom_represents
  have heq : (fun _ : Nat => (Part.none : Part Nat).bind (Nat.Partrec.Code.eval (Nat.Partrec.Code.const k))) =
      (fun _ : Nat => (Part.none : Part Nat)) := by
    funext n
    exact Part.bind_none _
  rw [heq] at h
  exact h

theorem cpsConstant_after_bottom_no_numerical (k n : Nat) :
    numericalValue (cpsUnary (cpsCompose (cpsConstant k) cpsBottom)) n = Part.none := by
  exact (cpsUnary_represents (cpsConstant_after_bottom k)).2 n

/-- A concrete partial-recursive code whose minimization test is always one. -/
def bottomCode : Nat.Partrec.Code := .rfind' (Nat.Partrec.Code.const 1)

theorem bottomCode_eval (x : Nat) : Nat.Partrec.Code.eval bottomCode x = Part.none := by
  have hsearch (a m : Nat) :
      Nat.rfind (fun n => (fun v => v = 0) <$>
        Nat.Partrec.Code.eval (Nat.Partrec.Code.const 1) (Nat.pair a (n + m))) = Part.none := by
    apply Part.eq_none_iff.2
    intro n hn
    have hs := Nat.rfind_spec hn
    simp [Nat.Partrec.Code.eval_const, Part.map_eq_map] at hs
  change (Nat.rfind (fun n => (fun v => v = 0) <$>
    Nat.Partrec.Code.eval (Nat.Partrec.Code.const 1) (Nat.pair x.unpair.1 (n + x.unpair.2)))).map
      (· + x.unpair.2) = Part.none
  rw [hsearch]
  simp

theorem cpsBottom_code : CPSRepresents cpsBottom (Nat.Partrec.Code.eval bottomCode) := by
  have heq : Nat.Partrec.Code.eval bottomCode = (fun _ => Part.none) := by
    funext n
    exact bottomCode_eval n
  rw [heq]
  exact cpsBottom_represents

/-- Extend the supported lambda fragment with one verified undefined code. -/
def compileWithBottom (c : Nat.Partrec.Code) : Option Term :=
  if Encodable.encode c = Encodable.encode bottomCode then some (cpsUnary cpsBottom)
  else compileSuccessorFragment c

theorem compileWithBottom_bottom : compileWithBottom bottomCode = some (cpsUnary cpsBottom) := by
  simp [compileWithBottom]

theorem compileWithBottom_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileWithBottom c = some t) : Represents t (Nat.Partrec.Code.eval c) := by
  by_cases hc : Encodable.encode c = Encodable.encode bottomCode
  · have heq : c = bottomCode := Encodable.encode_injective hc
    subst c
    have ht : cpsUnary cpsBottom = t := by simpa [compileWithBottom] using h
    subst t
    exact cpsUnary_represents cpsBottom_code
  · exact compileSuccessorFragment_sound c t (by simpa [compileWithBottom, hc] using h)

theorem primrec_compileWithBottom : Primrec compileWithBottom :=
  Primrec.ite (Primrec.eq.comp Primrec.encode (Primrec.const (Encodable.encode bottomCode)))
    (Primrec.const (some (cpsUnary cpsBottom))) primrec_compileSuccessorFragment

#print axioms omega_no_normal
#print axioms cpsBottom_represents
#print axioms cpsConstant_after_bottom_no_numerical
#print axioms bottomCode_eval
#print axioms compileWithBottom_sound
#print axioms primrec_compileWithBottom

end LambdaTuring
