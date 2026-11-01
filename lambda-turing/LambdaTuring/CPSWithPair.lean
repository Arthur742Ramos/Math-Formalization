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

@[expose] public section

namespace LambdaTuring

/-- Compile the supported source-code fragment, including strict numeric pairing. -/
def compileCPSWithPair : Nat.Partrec.Code → Option Term
  | .succ => some cpsSuccessor
  | .pair f g =>
    if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
    else do
      let F ← compileCPSWithPair f
      let G ← compileCPSWithPair g
      pure (cpsPair F G)
  | .comp f g =>
    match decodeConst (.comp f g) with
    | some n => some (cpsConstant n)
    | none => do
      let F ← compileCPSWithPair f
      let G ← compileCPSWithPair g
      pure (cpsCompose F G)
  | .rfind' f =>
    if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom
    else compileCPSBase (.rfind' f)
  | c => compileCPSBase c

theorem compileCPSWithPair_const (n : Nat) :
    compileCPSWithPair (Nat.Partrec.Code.const n) = some (cpsConstant n) := by
  cases n with
  | zero => simpa [Nat.Partrec.Code.const, compileCPSWithPair] using compileCPSBase_const 0
  | succ n =>
    have hc : decodeConst (.comp .succ (Nat.Partrec.Code.const n)) = some (n + 1) := by
      simpa [Nat.Partrec.Code.const] using decodeConst_const (n + 1)
    simp only [Nat.Partrec.Code.const, compileCPSWithPair, hc]

theorem compileCPSWithPair_id : compileCPSWithPair Nat.Partrec.Code.id = some cpsIdentity := by
  simp [Nat.Partrec.Code.id, compileCPSWithPair]

theorem compileCPSWithPair_succ : compileCPSWithPair .succ = some cpsSuccessor := rfl

theorem compileCPSWithPair_bottom : compileCPSWithPair bottomCode = some cpsBottom := by
  simp [bottomCode, compileCPSWithPair]

theorem compileCPSWithPair_comp (f g : Nat.Partrec.Code) (F G : Term)
    (hc : decodeConst (.comp f g) = none)
    (hf : compileCPSWithPair f = some F) (hg : compileCPSWithPair g = some G) :
    compileCPSWithPair (.comp f g) = some (cpsCompose F G) := by
  simp [compileCPSWithPair, hc, hf, hg]

theorem compileCPSWithPair_pair (f g : Nat.Partrec.Code) (F G : Term)
    (hi : Encodable.encode (Nat.Partrec.Code.pair f g) ≠ Encodable.encode Nat.Partrec.Code.id)
    (hf : compileCPSWithPair f = some F) (hg : compileCPSWithPair g = some G) :
    compileCPSWithPair (.pair f g) = some (cpsPair F G) := by
  simp [compileCPSWithPair, hi, hf, hg]

theorem compileCPSWithPair_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileCPSWithPair c = some t) : CPSRepresents t (Nat.Partrec.Code.eval c) := by
  induction c generalizing t with
  | pair f g ihf ihg =>
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · have heq : Nat.Partrec.Code.pair f g = Nat.Partrec.Code.id := Encodable.encode_injective hi
      have ht : cpsIdentity = t := by simpa [compileCPSWithPair, hi] using h
      subst t
      rw [heq]
      exact cpsIdentity_represents
    · cases hf : compileCPSWithPair f with
      | none => simp [compileCPSWithPair, hi, hf] at h
      | some F =>
        cases hg : compileCPSWithPair g with
        | none => simp [compileCPSWithPair, hi, hf, hg] at h
        | some G =>
          have ht : cpsPair F G = t := by simpa [compileCPSWithPair, hi, hf, hg] using h
          subst t
          rw [codePair_eval]
          exact cpsPair_represents (ihf F hf) (ihg G hg)
  | comp f g ihf ihg =>
    cases hc : decodeConst (.comp f g) with
    | some n =>
      have ht : cpsConstant n = t := by simpa [compileCPSWithPair, hc] using h
      subst t
      have heq := decodeConst_sound (.comp f g) n hc
      rw [heq]
      exact cpsConstant_represents n
    | none =>
      cases hf : compileCPSWithPair f with
      | none => simp [compileCPSWithPair, hc, hf] at h
      | some F =>
        cases hg : compileCPSWithPair g with
        | none => simp [compileCPSWithPair, hc, hf, hg] at h
        | some G =>
          have ht : cpsCompose F G = t := by simpa [compileCPSWithPair, hc, hf, hg] using h
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
      have ht : cpsBottom = t := by simpa [compileCPSWithPair, hc] using h
      subst t
      rw [heq]
      exact cpsBottom_code
    · exact compileCPSBase_sound _ _ (by simpa [compileCPSWithPair, hc] using h)
  | zero => exact compileCPSBase_sound _ _ h
  | succ =>
    have ht : cpsSuccessor = t := by simpa [compileCPSWithPair] using h
    subst t
    exact cpsSuccessor_represents
  | left => exact compileCPSBase_sound _ _ h
  | right => exact compileCPSBase_sound _ _ h
  | prec f g ihf ihg => exact compileCPSBase_sound _ _ h

inductive CPSPairSupported : Nat.Partrec.Code → Prop where
  | constant (n : Nat) : CPSPairSupported (Nat.Partrec.Code.const n)
  | identity : CPSPairSupported Nat.Partrec.Code.id
  | successor : CPSPairSupported .succ
  | bottom : CPSPairSupported bottomCode
  | composition {f g : Nat.Partrec.Code} : CPSPairSupported f → CPSPairSupported g → CPSPairSupported (.comp f g)
  | pairing {f g : Nat.Partrec.Code} : CPSPairSupported f → CPSPairSupported g → CPSPairSupported (.pair f g)

theorem compileCPSWithPair_complete {c : Nat.Partrec.Code} (h : CPSPairSupported c) :
    ∃ t, compileCPSWithPair c = some t := by
  induction h with
  | constant n => exact ⟨cpsConstant n, compileCPSWithPair_const n⟩
  | identity => exact ⟨cpsIdentity, compileCPSWithPair_id⟩
  | successor => exact ⟨cpsSuccessor, compileCPSWithPair_succ⟩
  | bottom => exact ⟨cpsBottom, compileCPSWithPair_bottom⟩
  | @composition f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    cases hc : decodeConst (.comp f g) with
    | some n => exact ⟨cpsConstant n, by simp [compileCPSWithPair, hc]⟩
    | none => exact ⟨cpsCompose F G, compileCPSWithPair_comp f g F G hc hf hg⟩
  | @pairing f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    by_cases hi : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · exact ⟨cpsIdentity, by simp [compileCPSWithPair, hi]⟩
    · exact ⟨cpsPair F G, compileCPSWithPair_pair f g F G hi hf hg⟩

def compilePairClosure (c : Nat.Partrec.Code) : Option Term := (compileCPSWithPair c).map cpsUnary

theorem compilePairClosure_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compilePairClosure c = some t) : Represents t (Nat.Partrec.Code.eval c) := by
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact cpsUnary_represents (compileCPSWithPair_sound c C hC)

theorem compilePairClosure_complete {c : Nat.Partrec.Code} (h : CPSPairSupported c) :
    ∃ t, compilePairClosure c = some t := by
  obtain ⟨C, hC⟩ := compileCPSWithPair_complete h
  exact ⟨cpsUnary C, by simp [compilePairClosure, hC]⟩

theorem pair_bottom_const_ne_id (k : Nat) :
    Encodable.encode (Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k)) ≠
      Encodable.encode Nat.Partrec.Code.id := by
  intro h
  have heq : Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k) = Nat.Partrec.Code.id :=
    Encodable.encode_injective h
  change Nat.Partrec.Code.pair bottomCode (Nat.Partrec.Code.const k) =
    Nat.Partrec.Code.pair .left .right at heq
  injection heq with hleft hright
  cases hleft

theorem compilePairClosure_bottom_left (k : Nat) :
    compilePairClosure (.pair bottomCode (Nat.Partrec.Code.const k)) =
      some (cpsUnary (cpsPair cpsBottom (cpsConstant k))) := by
  simp [compilePairClosure,
    compileCPSWithPair_pair _ _ _ _ (pair_bottom_const_ne_id k) compileCPSWithPair_bottom (compileCPSWithPair_const k)]

theorem compiled_pair_bottom_left_no_result (k n : Nat) :
    numericalValue (cpsUnary (cpsPair cpsBottom (cpsConstant k))) n = Part.none := by
  have h := (cpsUnary_represents (cpsPair_represents cpsBottom_code (cpsConstant_represents k))).2 n
  have hn : numericalPairBind (Nat.Partrec.Code.eval bottomCode)
      (Nat.Partrec.Code.eval (Nat.Partrec.Code.const k)) n = Part.none := by
    change (Nat.Partrec.Code.eval bottomCode n).bind _ = Part.none
    rw [bottomCode_eval, Part.bind_none]
  rw [h, hn]

def compileCPSPairFold (c : Nat.Partrec.Code) : Option Term :=
  Nat.Partrec.Code.recOn c (compileCPSBase .zero) (some cpsSuccessor)
    (compileCPSBase .left) (compileCPSBase .right)
    (fun f g F G => if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else F.bind fun F' => G.map (cpsPair F'))
    (fun f g F G => match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => F.bind fun F' => G.map (cpsCompose F'))
    (fun f g _ _ => compileCPSBase (.prec f g))
    (fun f _ => if Encodable.encode (Nat.Partrec.Code.rfind' f) = Encodable.encode bottomCode then some cpsBottom else compileCPSBase (.rfind' f))

theorem compileCPSPairFold_eq (c : Nat.Partrec.Code) : compileCPSPairFold c = compileCPSWithPair c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair f g ihf ihg =>
    change (if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else (compileCPSPairFold f).bind fun F => (compileCPSPairFold g).map (cpsPair F)) =
      (if Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id then some cpsIdentity
      else (compileCPSWithPair f).bind fun F => (compileCPSWithPair g).bind fun G => some (cpsPair F G))
    rw [ihf, ihg]
    by_cases h : Encodable.encode (Nat.Partrec.Code.pair f g) = Encodable.encode Nat.Partrec.Code.id
    · simp [h]
    · simp only [h, ite_false]
      cases compileCPSWithPair f <;> cases compileCPSWithPair g <;> rfl
  | prec f g ihf ihg => rfl
  | rfind' f ih => rfl
  | comp f g ihf ihg =>
    change (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSPairFold f).bind fun F => (compileCPSPairFold g).map (cpsCompose F)) =
      (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSWithPair f).bind fun F =>
          (compileCPSWithPair g).bind fun G => some (cpsCompose F G))
    rw [ihf, ihg]
    cases decodeConst (.comp f g) <;> cases compileCPSWithPair f <;>
      cases compileCPSWithPair g <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_compileCPSPairFold : Primrec compileCPSPairFold := by
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
    (s := fun _ : A => some cpsSuccessor) (l := fun _ : A => compileCPSBase .left)
    (r := fun _ : A => compileCPSBase .right)
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

theorem primrec_compileCPSWithPair : Primrec compileCPSWithPair :=
  primrec_compileCPSPairFold.of_eq compileCPSPairFold_eq




theorem primrec_compilePairClosure : Primrec compilePairClosure :=
  (Primrec.option_map₁ primrec_cpsUnary).comp primrec_compileCPSWithPair

#print axioms primrec_compilePairClosure
#print axioms compilePairClosure_sound
#print axioms compilePairClosure_complete
#print axioms compiled_pair_bottom_left_no_result

end LambdaTuring
