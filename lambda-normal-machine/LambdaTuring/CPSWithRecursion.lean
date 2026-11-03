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
public import LambdaTuring.CPSRecursion
public meta import LambdaTuring.CPSRecursion

@[expose] public section

namespace LambdaTuring

/-- Compile the supported source-code fragment, including strict numeric pairing, projections and primitive recursion. -/
def compileCPSWithRecursion : Nat.Partrec.Code → Option Term
  | .succ => some cpsSuccessor
  | .left => some (cpsLiftTotal churchNumericLeft)
  | .right => some (cpsLiftTotal churchNumericRight)
  | .pair f g =>
    if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
    else do
      let F ← compileCPSWithRecursion f
      let G ← compileCPSWithRecursion g
      pure (cpsPair F G)
  | .comp f g =>
    match decodeConst (.comp f g) with
    | some n => some (cpsConstant n)
    | none => do
      let F ← compileCPSWithRecursion f
      let G ← compileCPSWithRecursion g
      pure (cpsCompose F G)
  | .prec f g => do
    let F ← compileCPSWithRecursion f
    let G ← compileCPSWithRecursion g
    pure (cpsRecursion F G)
  | .rfind' f =>
    if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom
    else compileCPSBase (.rfind' f)
  | c => compileCPSBase c

theorem compileCPSWithRecursion_const (n : Nat) :
    compileCPSWithRecursion (Nat.Partrec.Code.const n) = some (cpsConstant n) := by
  cases n with
  | zero => simpa [Nat.Partrec.Code.const, compileCPSWithRecursion] using compileCPSBase_const 0
  | succ n =>
    have hc : decodeConst (.comp .succ (Nat.Partrec.Code.const n)) = some (n + 1) := by
      simpa [Nat.Partrec.Code.const] using decodeConst_const (n + 1)
    simp only [Nat.Partrec.Code.const, compileCPSWithRecursion, hc]

theorem compileCPSWithRecursion_id : compileCPSWithRecursion Nat.Partrec.Code.id = some cpsIdentity := by
  simp [Nat.Partrec.Code.id, compileCPSWithRecursion]

theorem compileCPSWithRecursion_succ : compileCPSWithRecursion .succ = some cpsSuccessor := rfl

theorem compileCPSWithRecursion_bottom : compileCPSWithRecursion bottomCode = some cpsBottom := by
  simp [bottomCode, compileCPSWithRecursion]

theorem compileCPSWithRecursion_comp (f g : Nat.Partrec.Code) (F G : Term)
    (hc : decodeConst (.comp f g) = none)
    (hf : compileCPSWithRecursion f = some F) (hg : compileCPSWithRecursion g = some G) :
    compileCPSWithRecursion (.comp f g) = some (cpsCompose F G) := by
  simp [compileCPSWithRecursion, hc, hf, hg]

theorem compileCPSWithRecursion_pair (f g : Nat.Partrec.Code) (F G : Term)
    (hi : Encodable.encode (Nat.Partrec.Code.pair f g) ≠ Encodable.encode Nat.Partrec.Code.id)
    (hf : compileCPSWithRecursion f = some F) (hg : compileCPSWithRecursion g = some G) :
    compileCPSWithRecursion (.pair f g) = some (cpsPair F G) := by
  simp [compileCPSWithRecursion, hi, hf, hg]

theorem compileCPSWithRecursion_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileCPSWithRecursion c = some t) : CPSRepresents t (Nat.Partrec.Code.eval c) := by
  induction c generalizing t with
  | pair f g ihf ihg =>
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · have heq : Nat.Partrec.Code.pair f g = Nat.Partrec.Code.id := Encodable.encode_injective hi
      have ht : cpsIdentity = t := by simpa [compileCPSWithRecursion, hi] using h
      subst t
      rw [heq]
      exact cpsIdentity_represents
    · cases hf : compileCPSWithRecursion f with
      | none => simp [compileCPSWithRecursion, hi, hf] at h
      | some F =>
        cases hg : compileCPSWithRecursion g with
        | none => simp [compileCPSWithRecursion, hi, hf, hg] at h
        | some G =>
          have ht : cpsPair F G = t := by simpa [compileCPSWithRecursion, hi, hf, hg] using h
          subst t
          rw [codePair_eval]
          exact cpsPair_represents (ihf F hf) (ihg G hg)
  | comp f g ihf ihg =>
    cases hc : decodeConst (.comp f g) with
    | some n =>
      have ht : cpsConstant n = t := by simpa [compileCPSWithRecursion, hc] using h
      subst t
      have heq := decodeConst_sound (.comp f g) n hc
      rw [heq]
      exact cpsConstant_represents n
    | none =>
      cases hf : compileCPSWithRecursion f with
      | none => simp [compileCPSWithRecursion, hc, hf] at h
      | some F =>
        cases hg : compileCPSWithRecursion g with
        | none => simp [compileCPSWithRecursion, hc, hf, hg] at h
        | some G =>
          have ht : cpsCompose F G = t := by simpa [compileCPSWithRecursion, hc, hf, hg] using h
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
      have ht : cpsBottom = t := by simpa [compileCPSWithRecursion, hc] using h
      subst t
      rw [heq]
      exact cpsBottom_code
    · exact compileCPSBase_sound _ _ (by simpa [compileCPSWithRecursion, hc] using h)
  | zero => exact compileCPSBase_sound _ _ h
  | succ =>
    have ht : cpsSuccessor = t := by simpa [compileCPSWithRecursion] using h
    subst t
    exact cpsSuccessor_represents
  | left =>
    have ht : cpsLiftTotal churchNumericLeft = t := by simpa [compileCPSWithRecursion] using h
    subst t
    exact cpsNumericLeft_represents
  | right =>
    have ht : cpsLiftTotal churchNumericRight = t := by simpa [compileCPSWithRecursion] using h
    subst t
    exact cpsNumericRight_represents
  | prec f g ihf ihg =>
    cases hf : compileCPSWithRecursion f with
    | none => simp [compileCPSWithRecursion, hf] at h
    | some F =>
      cases hg : compileCPSWithRecursion g with
      | none => simp [compileCPSWithRecursion, hf, hg] at h
      | some G =>
        have ht : cpsRecursion F G = t := by simpa [compileCPSWithRecursion, hf, hg] using h
        subst t
        exact cpsRecursion_code (ihf F hf) (ihg G hg)

inductive CPSRecursionSupported : Nat.Partrec.Code → Prop where
  | constant (n : Nat) : CPSRecursionSupported (Nat.Partrec.Code.const n)
  | identity : CPSRecursionSupported Nat.Partrec.Code.id
  | successor : CPSRecursionSupported .succ
  | left : CPSRecursionSupported .left
  | right : CPSRecursionSupported .right
  | bottom : CPSRecursionSupported bottomCode
  | composition {f g : Nat.Partrec.Code} : CPSRecursionSupported f → CPSRecursionSupported g → CPSRecursionSupported (.comp f g)
  | pairing {f g : Nat.Partrec.Code} : CPSRecursionSupported f → CPSRecursionSupported g → CPSRecursionSupported (.pair f g)
  | recursion {f g : Nat.Partrec.Code} : CPSRecursionSupported f → CPSRecursionSupported g → CPSRecursionSupported (.prec f g)

theorem compileCPSWithRecursion_complete {c : Nat.Partrec.Code} (h : CPSRecursionSupported c) :
    ∃ t, compileCPSWithRecursion c = some t := by
  induction h with
  | constant n => exact ⟨cpsConstant n, compileCPSWithRecursion_const n⟩
  | identity => exact ⟨cpsIdentity, compileCPSWithRecursion_id⟩
  | successor => exact ⟨cpsSuccessor, compileCPSWithRecursion_succ⟩
  | left => exact ⟨cpsLiftTotal churchNumericLeft, rfl⟩
  | right => exact ⟨cpsLiftTotal churchNumericRight, rfl⟩
  | bottom => exact ⟨cpsBottom, compileCPSWithRecursion_bottom⟩
  | @composition f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    cases hc : decodeConst (.comp f g) with
    | some n => exact ⟨cpsConstant n, by simp [compileCPSWithRecursion, hc]⟩
    | none => exact ⟨cpsCompose F G, compileCPSWithRecursion_comp f g F G hc hf hg⟩
  | @pairing f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · exact ⟨cpsIdentity, by simp [compileCPSWithRecursion, hi]⟩
    · exact ⟨cpsPair F G, compileCPSWithRecursion_pair f g F G hi hf hg⟩
  | @recursion f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    exact ⟨cpsRecursion F G, by simp [compileCPSWithRecursion, hf, hg]⟩

def compileRecursionClosure (c : Nat.Partrec.Code) : Option Term := (compileCPSWithRecursion c).map cpsUnary

theorem compileRecursionClosure_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileRecursionClosure c = some t) : Represents t (Nat.Partrec.Code.eval c) := by
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact cpsUnary_represents (compileCPSWithRecursion_sound c C hC)

theorem compileRecursionClosure_complete {c : Nat.Partrec.Code} (h : CPSRecursionSupported c) :
    ∃ t, compileRecursionClosure c = some t := by
  obtain ⟨C, hC⟩ := compileCPSWithRecursion_complete h
  exact ⟨cpsUnary C, by simp [compileRecursionClosure, hC]⟩

theorem recursion_pair_bottom_const_ne_id (k : Nat) :
    Encodable.encode (Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k)) ≠
      Encodable.encode Nat.Partrec.Code.id := by
  intro h
  have heq : Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k) = Nat.Partrec.Code.id :=
    Encodable.encode_injective h
  change Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k) =
    Nat.Partrec.Code.pair .left .right at heq
  injection heq with hleft hright
  cases hleft

theorem compileRecursionClosure_bottom_left (k : Nat) :
    compileRecursionClosure (.pair bottomCode (Nat.Partrec.Code.const k)) =
      some (cpsUnary (cpsPair cpsBottom (cpsConstant k))) := by
  simp [compileRecursionClosure,
    compileCPSWithRecursion_pair _ _ _ _ (recursion_pair_bottom_const_ne_id k) compileCPSWithRecursion_bottom (compileCPSWithRecursion_const k)]

theorem recursion_compiled_pair_bottom_left_no_result (k n : Nat) :
    numericalValue (cpsUnary (cpsPair cpsBottom (cpsConstant k))) n = Part.none := by
  have h := (cpsUnary_represents (cpsPair_represents cpsBottom_code (cpsConstant_represents k))).2 n
  have hn : numericalPairBind (Nat.Partrec.Code.eval bottomCode)
      (Nat.Partrec.Code.eval (Nat.Partrec.Code.const k)) n = Part.none := by
    change (Nat.Partrec.Code.eval bottomCode n).bind _ = Part.none
    rw [bottomCode_eval, Part.bind_none]
  rw [h, hn]

def compileCPSRecursionFold (c : Nat.Partrec.Code) : Option Term :=
  Nat.Partrec.Code.recOn c (compileCPSBase .zero) (some cpsSuccessor)
    (some (cpsLiftTotal churchNumericLeft)) (some (cpsLiftTotal churchNumericRight))
    (fun f g F G => if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else F.bind fun F' => G.map (cpsPair F'))
    (fun f g F G => match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => F.bind fun F' => G.map (cpsCompose F'))
    (fun _ _ F G => F.bind fun F' => G.map (cpsRecursion F'))
    (fun f _ => if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom else compileCPSBase (.rfind' f))

theorem compileCPSRecursionFold_eq (c : Nat.Partrec.Code) : compileCPSRecursionFold c = compileCPSWithRecursion c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair f g ihf ihg =>
    change (if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else (compileCPSRecursionFold f).bind fun F => (compileCPSRecursionFold g).map (cpsPair F)) =
      (if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else (compileCPSWithRecursion f).bind fun F => (compileCPSWithRecursion g).bind fun G => some (cpsPair F G))
    rw [ihf, ihg]
    by_cases h : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · simp [h]
    · simp only [h, ite_false]
      cases compileCPSWithRecursion f <;> cases compileCPSWithRecursion g <;> rfl
  | prec f g ihf ihg =>
    change ((compileCPSRecursionFold f).bind fun F => (compileCPSRecursionFold g).map (cpsRecursion F)) =
      ((compileCPSWithRecursion f).bind fun F => (compileCPSWithRecursion g).bind fun G => some (cpsRecursion F G))
    rw [ihf, ihg]
    cases compileCPSWithRecursion f <;> cases compileCPSWithRecursion g <;> rfl
  | rfind' f ih => rfl
  | comp f g ihf ihg =>
    change (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSRecursionFold f).bind fun F => (compileCPSRecursionFold g).map (cpsCompose F)) =
      (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSWithRecursion f).bind fun F =>
          (compileCPSWithRecursion g).bind fun G => some (cpsCompose F G))
    rw [ihf, ihg]
    cases decodeConst (.comp f g) <;> cases compileCPSWithRecursion f <;>
      cases compileCPSWithRecursion g <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_compileCPSRecursionFold : Primrec compileCPSRecursionFold := by
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
  have hpc : Primrec₂ (fun (_ : A) (p : P) =>
      p.2.2.1.bind fun F => p.2.2.2.map (cpsRecursion F)) := by
    apply Primrec.option_bind hl
    have hright : Primrec (fun x : S × Term => x.1.2.2.2.2) := hr.comp Primrec.fst
    have hcombine : Primrec₂ (fun (x : S × Term) (G : Term) => cpsRecursion x.2 G) :=
      primrec_cpsRecursion.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact (Primrec.option_map hright hcombine).to₂
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
    (pc := fun _ p => p.2.2.1.bind fun F => p.2.2.2.map (cpsRecursion F))
    (rf := fun _ p => if Encodable.encode (Nat.Partrec.Code.rfind' p.1) = Encodable.encode bottomCode then some cpsBottom else compileCPSBase (.rfind' p.1))
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr hco hpc hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_compileCPSWithRecursion : Primrec compileCPSWithRecursion :=
  primrec_compileCPSRecursionFold.of_eq compileCPSRecursionFold_eq




theorem primrec_compileRecursionClosure : Primrec compileRecursionClosure :=
  (Primrec.option_map₁ primrec_cpsUnary).comp primrec_compileCPSWithRecursion

#print axioms primrec_compileRecursionClosure
#print axioms compileRecursionClosure_sound
#print axioms compileRecursionClosure_complete
#print axioms recursion_compiled_pair_bottom_left_no_result

end LambdaTuring
