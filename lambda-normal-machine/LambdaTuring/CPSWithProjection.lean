/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSPair
public meta import LambdaTuring.CPSPair
public import LambdaTuring.CPSWithBottom
public meta import LambdaTuring.CPSWithBottom
public import LambdaTuring.CPSProjection
public meta import LambdaTuring.CPSProjection

@[expose] public section

namespace LambdaTuring

/-- Compile the supported source-code fragment, including strict numeric pairing and both numeric projections. -/
def compileCPSWithProjection : Nat.Partrec.Code → Option Term
  | .succ => some cpsSuccessor
  | .left => some (cpsLiftTotal churchNumericLeft)
  | .right => some (cpsLiftTotal churchNumericRight)
  | .pair f g =>
    if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
    else do
      let F ← compileCPSWithProjection f
      let G ← compileCPSWithProjection g
      pure (cpsPair F G)
  | .comp f g =>
    match decodeConst (.comp f g) with
    | some n => some (cpsConstant n)
    | none => do
      let F ← compileCPSWithProjection f
      let G ← compileCPSWithProjection g
      pure (cpsCompose F G)
  | .rfind' f =>
    if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom
    else compileCPSBase (.rfind' f)
  | c => compileCPSBase c

theorem compileCPSWithProjection_const (n : Nat) :
    compileCPSWithProjection (Nat.Partrec.Code.const n) = some (cpsConstant n) := by
  cases n with
  | zero => simpa [Nat.Partrec.Code.const, compileCPSWithProjection] using compileCPSBase_const 0
  | succ n =>
    have hc : decodeConst (.comp .succ (Nat.Partrec.Code.const n)) = some (n + 1) := by
      simpa [Nat.Partrec.Code.const] using decodeConst_const (n + 1)
    simp only [Nat.Partrec.Code.const, compileCPSWithProjection, hc]

theorem compileCPSWithProjection_id : compileCPSWithProjection Nat.Partrec.Code.id = some cpsIdentity := by
  simp [Nat.Partrec.Code.id, compileCPSWithProjection]

theorem compileCPSWithProjection_succ : compileCPSWithProjection .succ = some cpsSuccessor := rfl

theorem compileCPSWithProjection_bottom : compileCPSWithProjection bottomCode = some cpsBottom := by
  simp [bottomCode, compileCPSWithProjection]

theorem compileCPSWithProjection_comp (f g : Nat.Partrec.Code) (F G : Term)
    (hc : decodeConst (.comp f g) = none)
    (hf : compileCPSWithProjection f = some F) (hg : compileCPSWithProjection g = some G) :
    compileCPSWithProjection (.comp f g) = some (cpsCompose F G) := by
  simp [compileCPSWithProjection, hc, hf, hg]

theorem compileCPSWithProjection_pair (f g : Nat.Partrec.Code) (F G : Term)
    (hi : Encodable.encode (Nat.Partrec.Code.pair f g) ≠ Encodable.encode Nat.Partrec.Code.id)
    (hf : compileCPSWithProjection f = some F) (hg : compileCPSWithProjection g = some G) :
    compileCPSWithProjection (.pair f g) = some (cpsPair F G) := by
  simp [compileCPSWithProjection, hi, hf, hg]

theorem compileCPSWithProjection_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileCPSWithProjection c = some t) : CPSRepresents t (Nat.Partrec.Code.eval c) := by
  induction c generalizing t with
  | pair f g ihf ihg =>
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · have heq : Nat.Partrec.Code.pair f g = Nat.Partrec.Code.id := Encodable.encode_injective hi
      have ht : cpsIdentity = t := by simpa [compileCPSWithProjection, hi] using h
      subst t
      rw [heq]
      exact cpsIdentity_represents
    · cases hf : compileCPSWithProjection f with
      | none => simp [compileCPSWithProjection, hi, hf] at h
      | some F =>
        cases hg : compileCPSWithProjection g with
        | none => simp [compileCPSWithProjection, hi, hf, hg] at h
        | some G =>
          have ht : cpsPair F G = t := by simpa [compileCPSWithProjection, hi, hf, hg] using h
          subst t
          rw [codePair_eval]
          exact cpsPair_represents (ihf F hf) (ihg G hg)
  | comp f g ihf ihg =>
    cases hc : decodeConst (.comp f g) with
    | some n =>
      have ht : cpsConstant n = t := by simpa [compileCPSWithProjection, hc] using h
      subst t
      have heq := decodeConst_sound (.comp f g) n hc
      rw [heq]
      exact cpsConstant_represents n
    | none =>
      cases hf : compileCPSWithProjection f with
      | none => simp [compileCPSWithProjection, hc, hf] at h
      | some F =>
        cases hg : compileCPSWithProjection g with
        | none => simp [compileCPSWithProjection, hc, hf, hg] at h
        | some G =>
          have ht : cpsCompose F G = t := by simpa [compileCPSWithProjection, hc, hf, hg] using h
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
      have ht : cpsBottom = t := by simpa [compileCPSWithProjection, hc] using h
      subst t
      rw [heq]
      exact cpsBottom_code
    · exact compileCPSBase_sound _ _ (by simpa [compileCPSWithProjection, hc] using h)
  | zero => exact compileCPSBase_sound _ _ h
  | succ =>
    have ht : cpsSuccessor = t := by simpa [compileCPSWithProjection] using h
    subst t
    exact cpsSuccessor_represents
  | left =>
    have ht : cpsLiftTotal churchNumericLeft = t := by simpa [compileCPSWithProjection] using h
    subst t
    exact cpsNumericLeft_represents
  | right =>
    have ht : cpsLiftTotal churchNumericRight = t := by simpa [compileCPSWithProjection] using h
    subst t
    exact cpsNumericRight_represents
  | prec f g ihf ihg => exact compileCPSBase_sound _ _ h

inductive CPSProjectionSupported : Nat.Partrec.Code → Prop where
  | constant (n : Nat) : CPSProjectionSupported (Nat.Partrec.Code.const n)
  | identity : CPSProjectionSupported Nat.Partrec.Code.id
  | successor : CPSProjectionSupported .succ
  | left : CPSProjectionSupported .left
  | right : CPSProjectionSupported .right
  | bottom : CPSProjectionSupported bottomCode
  | composition {f g : Nat.Partrec.Code} : CPSProjectionSupported f → CPSProjectionSupported g → CPSProjectionSupported (.comp f g)
  | pairing {f g : Nat.Partrec.Code} : CPSProjectionSupported f → CPSProjectionSupported g → CPSProjectionSupported (.pair f g)

theorem compileCPSWithProjection_complete {c : Nat.Partrec.Code} (h : CPSProjectionSupported c) :
    ∃ t, compileCPSWithProjection c = some t := by
  induction h with
  | constant n => exact ⟨cpsConstant n, compileCPSWithProjection_const n⟩
  | identity => exact ⟨cpsIdentity, compileCPSWithProjection_id⟩
  | successor => exact ⟨cpsSuccessor, compileCPSWithProjection_succ⟩
  | left => exact ⟨cpsLiftTotal churchNumericLeft, rfl⟩
  | right => exact ⟨cpsLiftTotal churchNumericRight, rfl⟩
  | bottom => exact ⟨cpsBottom, compileCPSWithProjection_bottom⟩
  | @composition f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    cases hc : decodeConst (.comp f g) with
    | some n => exact ⟨cpsConstant n, by simp [compileCPSWithProjection, hc]⟩
    | none => exact ⟨cpsCompose F G, compileCPSWithProjection_comp f g F G hc hf hg⟩
  | @pairing f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · exact ⟨cpsIdentity, by simp [compileCPSWithProjection, hi]⟩
    · exact ⟨cpsPair F G, compileCPSWithProjection_pair f g F G hi hf hg⟩

def compileProjectionClosure (c : Nat.Partrec.Code) : Option Term := (compileCPSWithProjection c).map cpsUnary

theorem compileProjectionClosure_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileProjectionClosure c = some t) : Represents t (Nat.Partrec.Code.eval c) := by
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact cpsUnary_represents (compileCPSWithProjection_sound c C hC)

theorem compileProjectionClosure_complete {c : Nat.Partrec.Code} (h : CPSProjectionSupported c) :
    ∃ t, compileProjectionClosure c = some t := by
  obtain ⟨C, hC⟩ := compileCPSWithProjection_complete h
  exact ⟨cpsUnary C, by simp [compileProjectionClosure, hC]⟩

theorem projection_pair_bottom_const_ne_id (k : Nat) :
    Encodable.encode (Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k)) ≠
      Encodable.encode Nat.Partrec.Code.id := by
  intro h
  have heq : Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k) = Nat.Partrec.Code.id :=
    Encodable.encode_injective h
  change Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k) =
    Nat.Partrec.Code.pair .left .right at heq
  injection heq with hleft hright
  cases hleft

theorem compileProjectionClosure_bottom_left (k : Nat) :
    compileProjectionClosure (.pair bottomCode (Nat.Partrec.Code.const k)) =
      some (cpsUnary (cpsPair cpsBottom (cpsConstant k))) := by
  simp [compileProjectionClosure,
    compileCPSWithProjection_pair _ _ _ _ (projection_pair_bottom_const_ne_id k) compileCPSWithProjection_bottom (compileCPSWithProjection_const k)]

theorem projection_compiled_pair_bottom_left_no_result (k n : Nat) :
    numericalValue (cpsUnary (cpsPair cpsBottom (cpsConstant k))) n = Part.none := by
  have h := (cpsUnary_represents (cpsPair_represents cpsBottom_code (cpsConstant_represents k))).2 n
  have hn : numericalPairBind (Nat.Partrec.Code.eval bottomCode)
      (Nat.Partrec.Code.eval (Nat.Partrec.Code.const k)) n = Part.none := by
    change (Nat.Partrec.Code.eval bottomCode n).bind _ = Part.none
    rw [bottomCode_eval, Part.bind_none]
  rw [h, hn]

def compileCPSProjectionFold (c : Nat.Partrec.Code) : Option Term :=
  Nat.Partrec.Code.recOn c (compileCPSBase .zero) (some cpsSuccessor)
    (some (cpsLiftTotal churchNumericLeft)) (some (cpsLiftTotal churchNumericRight))
    (fun f g F G => if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else F.bind fun F' => G.map (cpsPair F'))
    (fun f g F G => match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => F.bind fun F' => G.map (cpsCompose F'))
    (fun f g _ _ => compileCPSBase (.prec f g))
    (fun f _ => if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom else compileCPSBase (.rfind' f))

theorem compileCPSProjectionFold_eq (c : Nat.Partrec.Code) : compileCPSProjectionFold c = compileCPSWithProjection c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair f g ihf ihg =>
    change (if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else (compileCPSProjectionFold f).bind fun F => (compileCPSProjectionFold g).map (cpsPair F)) =
      (if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else (compileCPSWithProjection f).bind fun F => (compileCPSWithProjection g).bind fun G => some (cpsPair F G))
    rw [ihf, ihg]
    by_cases h : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · simp [h]
    · simp only [h, ite_false]
      cases compileCPSWithProjection f <;> cases compileCPSWithProjection g <;> rfl
  | prec f g ihf ihg => rfl
  | rfind' f ih => rfl
  | comp f g ihf ihg =>
    change (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSProjectionFold f).bind fun F => (compileCPSProjectionFold g).map (cpsCompose F)) =
      (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSWithProjection f).bind fun F =>
          (compileCPSWithProjection g).bind fun G => some (cpsCompose F G))
    rw [ihf, ihg]
    cases decodeConst (.comp f g) <;> cases compileCPSWithProjection f <;>
      cases compileCPSWithProjection g <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_compileCPSProjectionFold : Primrec compileCPSProjectionFold := by
  let A := Nat.Partrec.Code
  let P := A × A × Option Term × Option Term
  let S := A × P
  have hf : Primrec (fun s : S => s.2.1) := Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun s : S => s.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun s : S => s.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr : Primrec (fun s : S => s.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hpr : Primrec₂ (fun (_ : A) (p : P) =>
      if Encodable.encode (Nat.Partrec.Code.pair p.1 p.2.1) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else p.2.2.1.bind fun F => p.2.2.2.map (cpsPair F)) := by
    have hn : Primrec (fun s : S => s.2.2.2.1.bind fun F => s.2.2.2.2.map (cpsPair F)) := by
      apply Primrec.option_bind hl
      have hright : Primrec (fun x : S × Term => x.1.2.2.2.2) := hr.comp Primrec.fst
      have hcombine : Primrec₂ (fun (x : S × Term) (G : Term) => cpsPair x.2 G) :=
        primrec_cpsPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
      exact (Primrec.option_map hright hcombine).to₂
    exact Primrec.ite
      (Primrec.eq.comp (Primrec.encode.comp (Nat.Partrec.Code.primrec₂_pair.comp hf hg))
        (Primrec.const (Encodable.encode Nat.Partrec.Code.id)))
      (Primrec.const (some cpsIdentity)) hn
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
    (s := fun _ : A => some cpsSuccessor) (l := fun _ : A => some (cpsLiftTotal churchNumericLeft))
    (r := fun _ : A => some (cpsLiftTotal churchNumericRight))
    (pr := fun _ p => if Encodable.encode (Nat.Partrec.Code.pair p.1 p.2.1) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else p.2.2.1.bind fun F => p.2.2.2.map (cpsPair F))
    (co := fun _ p => match decodeConst (.comp p.1 p.2.1) with
      | some n => some (cpsConstant n)
      | none => p.2.2.1.bind fun F => p.2.2.2.map (cpsCompose F))
    (pc := fun _ p => compileCPSBase (.prec p.1 p.2.1))
    (rf := fun _ p => if Encodable.encode (Nat.Partrec.Code.rfind' p.1) = Encodable.encode bottomCode then some cpsBottom else compileCPSBase (.rfind' p.1))
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr hco hpc hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_compileCPSWithProjection : Primrec compileCPSWithProjection :=
  primrec_compileCPSProjectionFold.of_eq compileCPSProjectionFold_eq




theorem primrec_compileProjectionClosure : Primrec compileProjectionClosure :=
  (Primrec.option_map₁ primrec_cpsUnary).comp primrec_compileCPSWithProjection

#print axioms primrec_compileProjectionClosure
#print axioms compileProjectionClosure_sound
#print axioms compileProjectionClosure_complete
#print axioms projection_compiled_pair_bottom_left_no_result

end LambdaTuring
