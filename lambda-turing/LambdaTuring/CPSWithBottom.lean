/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSBottom
public meta import LambdaTuring.CPSBottom
public import LambdaTuring.CPSComposition
public meta import LambdaTuring.CPSComposition

@[expose] public section

namespace LambdaTuring

/-- CPS compiler for constants, identity, successor, the verified undefined
    code, and finite compositions of those source codes. -/
def compileCPSWithBottom : Nat.Partrec.Code → Option Term
  | .succ => some cpsSuccessor
  | .comp f g =>
    match decodeConst (.comp f g) with
    | some n => some (cpsConstant n)
    | none => do
      let F ← compileCPSWithBottom f
      let G ← compileCPSWithBottom g
      pure (cpsCompose F G)
  | .rfind' f =>
    if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom
    else compileCPSBase (.rfind' f)
  | c => compileCPSBase c

theorem compileCPSWithBottom_const (n : Nat) :
    compileCPSWithBottom (Nat.Partrec.Code.const n) = some (cpsConstant n) := by
  cases n with
  | zero => simpa [Nat.Partrec.Code.const, compileCPSWithBottom] using compileCPSBase_const 0
  | succ n =>
    have hc : decodeConst (.comp .succ (Nat.Partrec.Code.const n)) = some (n + 1) := by
      simpa [Nat.Partrec.Code.const] using decodeConst_const (n + 1)
    simp only [Nat.Partrec.Code.const, compileCPSWithBottom, hc]

theorem compileCPSWithBottom_id : compileCPSWithBottom Nat.Partrec.Code.id = some cpsIdentity := by
  simp [Nat.Partrec.Code.id, compileCPSWithBottom, compileCPSBase]

theorem compileCPSWithBottom_succ : compileCPSWithBottom .succ = some cpsSuccessor := rfl

theorem compileCPSWithBottom_bottom : compileCPSWithBottom bottomCode = some cpsBottom := by
  simp [bottomCode, compileCPSWithBottom]

theorem compileCPSWithBottom_comp (f g : Nat.Partrec.Code) (F G : Term)
    (hc : decodeConst (.comp f g) = none)
    (hf : compileCPSWithBottom f = some F) (hg : compileCPSWithBottom g = some G) :
    compileCPSWithBottom (.comp f g) = some (cpsCompose F G) := by
  simp [compileCPSWithBottom, hc, hf, hg]

theorem compileCPSWithBottom_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileCPSWithBottom c = some t) : CPSRepresents t (Nat.Partrec.Code.eval c) := by
  induction c generalizing t with
  | comp f g ihf ihg =>
    cases hc : decodeConst (.comp f g) with
    | some n =>
      have ht : cpsConstant n = t := by simpa [compileCPSWithBottom, hc] using h
      subst t
      have heq := decodeConst_sound (.comp f g) n hc
      rw [heq]
      exact cpsConstant_represents n
    | none =>
      cases hf : compileCPSWithBottom f with
      | none => simp [compileCPSWithBottom, hc, hf] at h
      | some F =>
        cases hg : compileCPSWithBottom g with
        | none => simp [compileCPSWithBottom, hc, hf, hg] at h
        | some G =>
          have ht : cpsCompose F G = t := by simpa [compileCPSWithBottom, hc, hf, hg] using h
          subst t
          have heval : Nat.Partrec.Code.eval (.comp f g) =
              (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
            funext n
            exact Part.bind_eq_bind _ _
          rw [heval]
          exact cpsCompose_represents (ihf F hf) (ihg G hg)
  | rfind' f ih =>
    by_cases hc : Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode
    · have heq : Nat.Partrec.Code.rfind' f = bottomCode := Encodable.encode_injective hc
      have ht : cpsBottom = t := by simpa [compileCPSWithBottom, hc] using h
      subst t
      rw [heq]
      exact cpsBottom_code
    · exact compileCPSBase_sound _ _ (by simpa [compileCPSWithBottom, hc] using h)
  | zero => exact compileCPSBase_sound _ _ h
  | succ =>
    have ht : cpsSuccessor = t := by simpa [compileCPSWithBottom] using h
    subst t
    exact cpsSuccessor_represents
  | left => exact compileCPSBase_sound _ _ h
  | right => exact compileCPSBase_sound _ _ h
  | pair f g ihf ihg => exact compileCPSBase_sound _ _ h
  | prec f g ihf ihg => exact compileCPSBase_sound _ _ h

inductive CPSBottomSupported : Nat.Partrec.Code → Prop where
  | constant (n : Nat) : CPSBottomSupported (Nat.Partrec.Code.const n)
  | identity : CPSBottomSupported Nat.Partrec.Code.id
  | successor : CPSBottomSupported .succ
  | bottom : CPSBottomSupported bottomCode
  | composition {f g : Nat.Partrec.Code} :
      CPSBottomSupported f → CPSBottomSupported g → CPSBottomSupported (.comp f g)

theorem compileCPSWithBottom_complete {c : Nat.Partrec.Code} (h : CPSBottomSupported c) :
    ∃ t, compileCPSWithBottom c = some t := by
  induction h with
  | constant n => exact ⟨cpsConstant n, compileCPSWithBottom_const n⟩
  | identity => exact ⟨cpsIdentity, compileCPSWithBottom_id⟩
  | successor => exact ⟨cpsSuccessor, compileCPSWithBottom_succ⟩
  | bottom => exact ⟨cpsBottom, compileCPSWithBottom_bottom⟩
  | @composition f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    cases hc : decodeConst (.comp f g) with
    | some n => exact ⟨cpsConstant n, by simp [compileCPSWithBottom, hc]⟩
    | none => exact ⟨cpsCompose F G, compileCPSWithBottom_comp f g F G hc hf hg⟩

def compileBottomClosure (c : Nat.Partrec.Code) : Option Term :=
  (compileCPSWithBottom c).map cpsUnary

theorem compileBottomClosure_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileBottomClosure c = some t) : Represents t (Nat.Partrec.Code.eval c) := by
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact cpsUnary_represents (compileCPSWithBottom_sound c C hC)

theorem compileBottomClosure_complete {c : Nat.Partrec.Code} (h : CPSBottomSupported c) :
    ∃ t, compileBottomClosure c = some t := by
  obtain ⟨C, hC⟩ := compileCPSWithBottom_complete h
  exact ⟨cpsUnary C, by simp [compileBottomClosure, hC]⟩

/-- The compiler really composes an outer constant after the undefined code;
    strictness prevents the constant from erasing the undefined computation. -/
theorem compileBottomClosure_const_after_bottom (k : Nat) :
    compileBottomClosure (.comp (Nat.Partrec.Code.const k) bottomCode) =
      some (cpsUnary (cpsCompose (cpsConstant k) cpsBottom)) := by
  have hc : decodeConst (.comp (Nat.Partrec.Code.const k) bottomCode) = none := by
    cases k <;> rfl
  simp [compileBottomClosure,
    compileCPSWithBottom_comp _ _ _ _ hc (compileCPSWithBottom_const k) compileCPSWithBottom_bottom]

theorem compiled_const_after_bottom_no_result (k n : Nat) :
    numericalValue (cpsUnary (cpsCompose (cpsConstant k) cpsBottom)) n = Part.none :=
  cpsConstant_after_bottom_no_numerical k n

def compileCPSBottomFold (c : Nat.Partrec.Code) : Option Term :=
  Nat.Partrec.Code.recOn c (compileCPSBase .zero) (some cpsSuccessor)
    (compileCPSBase .left) (compileCPSBase .right)
    (fun f g _ _ => compileCPSBase (.pair f g))
    (fun f g F G => match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => F.bind fun F' => G.map (cpsCompose F'))
    (fun f g _ _ => compileCPSBase (.prec f g))
    (fun f _ => if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom else compileCPSBase (.rfind' f))

theorem compileCPSBottomFold_eq (c : Nat.Partrec.Code) : compileCPSBottomFold c = compileCPSWithBottom c := by
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
      | none => (compileCPSBottomFold f).bind fun F => (compileCPSBottomFold g).map (cpsCompose F)) =
      (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSWithBottom f).bind fun F =>
          (compileCPSWithBottom g).bind fun G => some (cpsCompose F G))
    rw [ihf, ihg]
    cases decodeConst (.comp f g) <;> cases compileCPSWithBottom f <;>
      cases compileCPSWithBottom g <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_compileCPSBottomFold : Primrec compileCPSBottomFold := by
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
  have hrf : Primrec₂ (fun (_ : A) (p : A × Option Term) =>
      if Encodable.encode (Nat.Partrec.Code.rfind' p.1) = Encodable.encode bottomCode then some cpsBottom
      else compileCPSBase (.rfind' p.1)) := by
    have hc : Primrec (fun x : A × (A × Option Term) => Nat.Partrec.Code.rfind' x.2.1) :=
      Nat.Partrec.Code.primrec_rfind'.comp (Primrec.fst.comp Primrec.snd)
    exact Primrec.ite (Primrec.eq.comp (Primrec.encode.comp hc) (Primrec.const (Encodable.encode bottomCode)))
      (Primrec.const (some cpsBottom)) (primrec_compileCPSBase.comp hc)
  have h := Nat.Partrec.Code.primrec_recOn'
    (c := id) (z := fun _ : A => compileCPSBase .zero)
    (s := fun _ : A => some cpsSuccessor) (l := fun _ : A => compileCPSBase .left)
    (r := fun _ : A => compileCPSBase .right)
    (pr := fun _ p => compileCPSBase (.pair p.1 p.2.1))
    (co := fun _ p => match decodeConst (.comp p.1 p.2.1) with
      | some n => some (cpsConstant n)
      | none => p.2.2.1.bind fun F => p.2.2.2.map (cpsCompose F))
    (pc := fun _ p => compileCPSBase (.prec p.1 p.2.1))
    (rf := fun _ p => if Encodable.encode (Nat.Partrec.Code.rfind' p.1) = Encodable.encode bottomCode then some cpsBottom else compileCPSBase (.rfind' p.1))
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr hco hpc hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_compileCPSWithBottom : Primrec compileCPSWithBottom :=
  primrec_compileCPSBottomFold.of_eq compileCPSBottomFold_eq



theorem primrec_compileBottomClosure : Primrec compileBottomClosure :=
  (Primrec.option_map₁ primrec_cpsUnary).comp primrec_compileCPSWithBottom

#print axioms primrec_compileBottomClosure
#print axioms compileBottomClosure_sound
#print axioms compileBottomClosure_complete
#print axioms compiled_const_after_bottom_no_result

end LambdaTuring
