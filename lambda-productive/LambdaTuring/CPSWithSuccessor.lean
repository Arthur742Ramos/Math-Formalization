/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSComposition
public meta import LambdaTuring.CPSComposition
public import LambdaTuring.ChurchSuccessor
public meta import LambdaTuring.ChurchSuccessor

@[expose] public section

namespace LambdaTuring

/-- A constructive CPS compiler for constants, identity, successor, and
    arbitrary finite compositions of supported codes. -/
def compileCPSSuccessor : Nat.Partrec.Code → Option Term
  | .succ => some cpsSuccessor
  | .comp f g =>
    match decodeConst (.comp f g) with
    | some n => some (cpsConstant n)
    | none => do
      let F ← compileCPSSuccessor f
      let G ← compileCPSSuccessor g
      pure (cpsCompose F G)
  | c => compileCPSBase c

theorem compileCPSSuccessor_const (n : Nat) :
    compileCPSSuccessor (Nat.Partrec.Code.const n) = some (cpsConstant n) := by
  cases n with
  | zero => simpa [Nat.Partrec.Code.const, compileCPSSuccessor] using compileCPSBase_const 0
  | succ n =>
    have hc : decodeConst (.comp .succ (Nat.Partrec.Code.const n)) = some (n + 1) := by
      simpa [Nat.Partrec.Code.const] using decodeConst_const (n + 1)
    simp only [Nat.Partrec.Code.const, compileCPSSuccessor, hc]

theorem compileCPSSuccessor_id : compileCPSSuccessor Nat.Partrec.Code.id = some cpsIdentity := by
  simp [Nat.Partrec.Code.id, compileCPSSuccessor, compileCPSBase]

theorem compileCPSSuccessor_succ : compileCPSSuccessor .succ = some cpsSuccessor := rfl

theorem compileCPSSuccessor_comp (f g : Nat.Partrec.Code) (F G : Term)
    (hc : decodeConst (.comp f g) = none)
    (hf : compileCPSSuccessor f = some F) (hg : compileCPSSuccessor g = some G) :
    compileCPSSuccessor (.comp f g) = some (cpsCompose F G) := by
  simp [compileCPSSuccessor, hc, hf, hg]

theorem compileCPSSuccessor_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileCPSSuccessor c = some t) : CPSRepresents t (Nat.Partrec.Code.eval c) := by
  induction c generalizing t with
  | comp f g ihf ihg =>
    cases hc : decodeConst (.comp f g) with
    | some n =>
      have ht : cpsConstant n = t := by simpa [compileCPSSuccessor, hc] using h
      subst t
      have heq := decodeConst_sound (.comp f g) n hc
      rw [heq]
      exact cpsConstant_represents n
    | none =>
      cases hf : compileCPSSuccessor f with
      | none => simp [compileCPSSuccessor, hc, hf] at h
      | some F =>
        cases hg : compileCPSSuccessor g with
        | none => simp [compileCPSSuccessor, hc, hf, hg] at h
        | some G =>
          have ht : cpsCompose F G = t := by simpa [compileCPSSuccessor, hc, hf, hg] using h
          subst t
          have heval : Nat.Partrec.Code.eval (.comp f g) =
              (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
            funext n
            exact Part.bind_eq_bind _ _
          rw [heval]
          exact cpsCompose_represents (ihf F hf) (ihg G hg)
  | zero => exact compileCPSBase_sound _ _ h
  | succ =>
    have ht : cpsSuccessor = t := by simpa [compileCPSSuccessor] using h
    subst t
    exact cpsSuccessor_represents
  | left => exact compileCPSBase_sound _ _ h
  | right => exact compileCPSBase_sound _ _ h
  | pair f g ihf ihg => exact compileCPSBase_sound _ _ h
  | prec f g ihf ihg => exact compileCPSBase_sound _ _ h
  | rfind' f ih => exact compileCPSBase_sound _ _ h

inductive CPSSuccessorSupported : Nat.Partrec.Code → Prop where
  | constant (n : Nat) : CPSSuccessorSupported (Nat.Partrec.Code.const n)
  | identity : CPSSuccessorSupported Nat.Partrec.Code.id
  | successor : CPSSuccessorSupported .succ
  | composition {f g : Nat.Partrec.Code} :
      CPSSuccessorSupported f → CPSSuccessorSupported g → CPSSuccessorSupported (.comp f g)

theorem compileCPSSuccessor_complete {c : Nat.Partrec.Code} (h : CPSSuccessorSupported c) :
    ∃ t, compileCPSSuccessor c = some t := by
  induction h with
  | constant n => exact ⟨cpsConstant n, compileCPSSuccessor_const n⟩
  | identity => exact ⟨cpsIdentity, compileCPSSuccessor_id⟩
  | successor => exact ⟨cpsSuccessor, compileCPSSuccessor_succ⟩
  | @composition f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    cases hc : decodeConst (.comp f g) with
    | some n => exact ⟨cpsConstant n, by simp [compileCPSSuccessor, hc]⟩
    | none => exact ⟨cpsCompose F G, compileCPSSuccessor_comp f g F G hc hf hg⟩

def compileSuccessorFragment (c : Nat.Partrec.Code) : Option Term :=
  (compileCPSSuccessor c).map cpsUnary

theorem compileSuccessorFragment_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileSuccessorFragment c = some t) : Represents t (Nat.Partrec.Code.eval c) := by
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact cpsUnary_represents (compileCPSSuccessor_sound c C hC)

theorem compileSuccessorFragment_complete {c : Nat.Partrec.Code} (h : CPSSuccessorSupported c) :
    ∃ t, compileSuccessorFragment c = some t := by
  obtain ⟨C, hC⟩ := compileCPSSuccessor_complete h
  exact ⟨cpsUnary C, by simp [compileSuccessorFragment, hC]⟩

def compileCPSSuccessorFold (c : Nat.Partrec.Code) : Option Term :=
  Nat.Partrec.Code.recOn c (compileCPSBase .zero) (some cpsSuccessor)
    (compileCPSBase .left) (compileCPSBase .right)
    (fun f g _ _ => compileCPSBase (.pair f g))
    (fun f g F G => match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => F.bind fun F' => G.map (cpsCompose F'))
    (fun f g _ _ => compileCPSBase (.prec f g))
    (fun f _ => compileCPSBase (.rfind' f))

theorem compileCPSSuccessorFold_eq (c : Nat.Partrec.Code) : compileCPSSuccessorFold c = compileCPSSuccessor c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair f g ihf ihg => rfl
  | prec f g ihf ihg => rfl
  | rfind' f ih => rfl
  | comp f g ihf ihg =>
    change (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSSuccessorFold f).bind fun F => (compileCPSSuccessorFold g).map (cpsCompose F)) =
      (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSSuccessor f).bind fun F =>
          (compileCPSSuccessor g).bind fun G => some (cpsCompose F G))
    rw [ihf, ihg]
    cases decodeConst (.comp f g) <;> cases compileCPSSuccessor f <;>
      cases compileCPSSuccessor g <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_compileCPSSuccessorFold : Primrec compileCPSSuccessorFold := by
  let A := Nat.Partrec.Code
  let P := A × A × Option Term × Option Term
  let S := A × P
  have hf : Primrec (fun s : S => s.2.1) := Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun s : S => s.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun s : S => s.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr : Primrec (fun s : S => s.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hpr : Primrec₂ (fun (_ : A) (p : P) => compileCPSBase (.pair p.1 p.2.1)) :=
    primrec_compileCPSBase.comp (Nat.Partrec.Code.primrec₂_pair.comp hf hg)
  have hpc : Primrec₂ (fun (_ : A) (p : P) => compileCPSBase (.prec p.1 p.2.1)) :=
    primrec_compileCPSBase.comp (Nat.Partrec.Code.primrec₂_prec.comp hf hg)
  have hco : Primrec₂ (fun (_ : A) (p : P) => match decodeConst (.comp p.1 p.2.1) with
      | some n => some (cpsConstant n)
      | none => p.2.2.1.bind fun F => p.2.2.2.map (cpsCompose F)) := by
    have hd : Primrec (fun s : S => decodeConst (.comp s.2.1 s.2.2.1)) :=
      primrec_decodeConst.comp (Nat.Partrec.Code.primrec₂_comp.comp hf hg)
    have hn : Primrec (fun s : S => s.2.2.2.1.bind fun F => s.2.2.2.2.map (cpsCompose F)) := by
      apply Primrec.option_bind hl
      have hright : Primrec (fun x : S × Term => x.1.2.2.2.2) := hr.comp Primrec.fst
      have hcombine : Primrec₂ (fun (x : S × Term) (G : Term) => cpsCompose x.2 G) :=
        primrec_cpsCompose.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
      exact (Primrec.option_map hright hcombine).to₂
    have hs : Primrec₂ (fun (_ : S) (n : Nat) => some (cpsConstant n)) :=
      Primrec.option_some.comp (primrec_cpsConstant.comp Primrec.snd)
    apply (Primrec.option_casesOn hd hn hs).of_eq
    intro s
    cases h : decodeConst (.comp s.2.1 s.2.2.1) <;> simp [h]
  have hrf : Primrec₂ (fun (_ : A) (p : A × Option Term) => compileCPSBase (.rfind' p.1)) :=
    primrec_compileCPSBase.comp (Nat.Partrec.Code.primrec_rfind'.comp (Primrec.fst.comp Primrec.snd))
  have h := Nat.Partrec.Code.primrec_recOn'
    (c := id) (z := fun _ : A => compileCPSBase .zero)
    (s := fun _ : A => some cpsSuccessor) (l := fun _ : A => compileCPSBase .left)
    (r := fun _ : A => compileCPSBase .right)
    (pr := fun _ p => compileCPSBase (.pair p.1 p.2.1))
    (co := fun _ p => match decodeConst (.comp p.1 p.2.1) with
      | some n => some (cpsConstant n)
      | none => p.2.2.1.bind fun F => p.2.2.2.map (cpsCompose F))
    (pc := fun _ p => compileCPSBase (.prec p.1 p.2.1))
    (rf := fun _ p => compileCPSBase (.rfind' p.1))
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr hco hpc hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_compileCPSSuccessor : Primrec compileCPSSuccessor :=
  primrec_compileCPSSuccessorFold.of_eq compileCPSSuccessorFold_eq


theorem primrec_compileSuccessorFragment : Primrec compileSuccessorFragment :=
  (Primrec.option_map₁ primrec_cpsUnary).comp primrec_compileCPSSuccessor

#print axioms primrec_compileSuccessorFragment
#print axioms compileSuccessorFragment_sound
#print axioms compileSuccessorFragment_complete

end LambdaTuring
