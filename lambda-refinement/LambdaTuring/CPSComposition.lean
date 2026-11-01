/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPS
public meta import LambdaTuring.CPS

@[expose] public section

/- The CPS composition construction and strictness argument follow the related
   Isabelle Lambda_CPS_Composition theory and its credited Norrish method. -/

namespace LambdaTuring

theorem substAt_liftFrom (t : Term) (depth : Nat) (value : Term) :
    substAt depth value (liftFrom depth t) = t := by
  induction t generalizing depth with
  | var i =>
    by_cases hi : i < depth
    · simp [liftFrom, substAt, hi, Nat.ne_of_lt hi, Nat.not_lt_of_ge (Nat.le_of_lt hi)]
    · have hle : depth ≤ i := Nat.le_of_not_gt hi
      have hne : i + 1 ≠ depth := by omega
      have hlt : depth < i + 1 := by omega
      simp [liftFrom, substAt, hi, hne, hlt]
  | abs t ih =>
    change Term.abs (substAt (depth + 1) value (liftFrom (depth + 1) t)) = Term.abs t
    rw [ih (depth + 1)]
  | app f x ihf ihx =>
    change Term.app (substAt depth value (liftFrom depth f))
      (substAt depth value (liftFrom depth x)) = Term.app f x
    rw [ihf depth, ihx depth]

theorem noNormal_backward {a b : Term} (hab : Reaches a b)
    (hn : ¬ ∃ N, Reaches b N ∧ ¬ ∃ u, Beta N u) :
    ¬ ∃ N, Reaches a N ∧ ¬ ∃ u, Beta N u := by
  rintro ⟨N, haN, normal⟩
  obtain ⟨u, hbu, hNu⟩ := beta_confluent hab haN
  have eq : N = u := normal_reaches_eq normal hNu
  apply hn
  exact ⟨N, by simpa [← eq] using hbu, normal⟩

def cpsCompose (F G : Term) : Term :=
  .abs (.abs (.app (.app G (.var 1)) (.abs (.app (.app F (.var 0)) (.var 1)))))

def cpsComposeCont (F K : Term) : Term :=
  .abs (.app (.app F (.var 0)) (liftFrom 0 K))

theorem cpsCompose_closed {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) :
    Scoped 0 (cpsCompose F G) := by
  have hf3 := scoped_mono hf (Nat.zero_le 3)
  have hg2 := scoped_mono hg (Nat.zero_le 2)
  simpa [cpsCompose, Scoped] using And.intro (And.intro hg2 (by decide : 1 < 2))
    (And.intro (And.intro hf3 (by decide : 0 < 3)) (by decide : 1 < 3))

theorem cpsCompose_run {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) (n : Nat) (K : Term) :
    Reaches (.app (.app (cpsCompose F G) (church n)) K)
      (.app (.app G (church n)) (cpsComposeCont F K)) := by
  have hg1 := substAt_scoped G 1 (church n) (scoped_mono hg (Nat.zero_le 1))
  have hf2 := substAt_scoped F 2 (church n) (scoped_mono hf (Nat.zero_le 2))
  have hcn : liftBy 1 (church n) = church n := by
    simpa [liftBy] using liftFrom_scoped (church n) 0 0 (church_closed n) (le_refl _)
  have hb1 : Beta (.app (cpsCompose F G) (church n))
      (.abs (.app (.app G (church n)) (.abs (.app (.app F (.var 0)) (.var 1))))) := by
    simpa [cpsCompose, substAt, hg1, hf2, hcn] using
      (Beta.contract (.abs (.app (.app G (.var 1)) (.abs (.app (.app F (.var 0)) (.var 1))))) (church n))
  have hg0 := substAt_scoped G 0 K hg
  have hf1 := substAt_scoped F 1 K (scoped_mono hf (Nat.zero_le 1))
  have hc0 := substAt_scoped (church n) 0 K (church_closed n)
  have hb2 : Beta (.app (.abs (.app (.app G (church n)) (.abs (.app (.app F (.var 0)) (.var 1))))) K)
      (.app (.app G (church n)) (cpsComposeCont F K)) := by
    simpa [cpsComposeCont, substAt, liftBy, hg0, hf1, hc0] using
      (Beta.contract (.app (.app G (church n)) (.abs (.app (.app F (.var 0)) (.var 1)))) K)
  exact .step (.appLeft hb1) (.step hb2 (.refl _))

theorem cpsComposeCont_run {F : Term} (hf : Scoped 0 F) (K : Term) (n : Nat) :
    Reaches (.app (cpsComposeCont F K) (church n)) (.app (.app F (church n)) K) := by
  have hF := substAt_scoped F 0 (church n) hf
  have hK := substAt_liftFrom K 0 (church n)
  have hb : Beta (.app (cpsComposeCont F K) (church n)) (.app (.app F (church n)) K) := by
    simpa [cpsComposeCont, substAt, liftBy, hF, hK] using
      (Beta.contract (.app (.app F (.var 0)) (liftFrom 0 K)) (church n))
  exact .step hb (.refl _)

/-- Strict CPS composition preserves both numerical values and undefinedness. -/
theorem cpsCompose_represents {F G : Term} {f g : Nat →. Nat}
    (hf : CPSRepresents F f) (hg : CPSRepresents G g) :
    CPSRepresents (cpsCompose F G) (fun n => (g n).bind f) := by
  constructor
  · exact cpsCompose_closed hf.1 hg.1
  · intro n K
    have hprefix : Reaches (.app (.app (cpsCompose F G) (church n)) K)
        (.app (.app G (church n)) (cpsComposeCont F K)) := cpsCompose_run hf.1 hg.1 n K
    have second : ∀ a, a ∈ g n →
        Reaches (.app (.app (cpsCompose F G) (church n)) K) (.app (.app F (church a)) K) := by
      intro a ha
      exact reaches_trans hprefix
        (reaches_trans ((hg.2 n (cpsComposeCont F K)).1 a ha) (cpsComposeCont_run hf.1 K a))
    constructor
    · intro m hm
      obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.1 hm
      exact reaches_trans (second a ha) ((hf.2 a K).1 m hm)
    · intro hnone
      change (g n).bind f = Part.none at hnone
      by_cases hd : (g n).Dom
      · obtain ⟨a, ha⟩ := Part.dom_iff_mem.1 hd
        have hfnone : f a = Part.none := by
          apply Part.eq_none_iff.2
          intro m hm
          have hmem : m ∈ (g n).bind f := Part.mem_bind_iff.2 ⟨a, ha, hm⟩
          rw [hnone] at hmem
          simp at hmem
        exact noNormal_backward (second a ha) ((hf.2 a K).2 hfnone)
      · have hgnone : g n = Part.none := by
          apply Part.eq_none_iff.2
          intro m hm
          exact hd (Part.dom_iff_mem.2 ⟨m, hm⟩)
        exact noNormal_backward hprefix ((hg.2 n (cpsComposeCont F K)).2 hgnone)

/-- Compile the composition closure of canonical constants and identity.
    Failure identifies an unsupported syntax tree, not an undefined value. -/
def compileCPSComposition : Nat.Partrec.Code → Option Term
  | .comp f g =>
    match decodeConst (.comp f g) with
    | some n => some (cpsConstant n)
    | none => do
      let F ← compileCPSComposition f
      let G ← compileCPSComposition g
      pure (cpsCompose F G)
  | c => compileCPSBase c

theorem compileCPSComposition_const (n : Nat) :
    compileCPSComposition (Nat.Partrec.Code.const n) = some (cpsConstant n) := by
  cases n with
  | zero => simpa [Nat.Partrec.Code.const, compileCPSComposition] using compileCPSBase_const 0
  | succ n =>
    have hc : decodeConst (.comp .succ (Nat.Partrec.Code.const n)) = some (n + 1) := by
      simpa [Nat.Partrec.Code.const] using decodeConst_const (n + 1)
    simp only [Nat.Partrec.Code.const, compileCPSComposition, hc]

theorem compileCPSComposition_id :
    compileCPSComposition Nat.Partrec.Code.id = some cpsIdentity := by
  simp [Nat.Partrec.Code.id, compileCPSComposition, compileCPSBase]

theorem compileCPSComposition_comp (f g : Nat.Partrec.Code) (F G : Term)
    (hc : decodeConst (.comp f g) = none)
    (hf : compileCPSComposition f = some F) (hg : compileCPSComposition g = some G) :
    compileCPSComposition (.comp f g) = some (cpsCompose F G) := by
  simp [compileCPSComposition, hc, hf, hg]

theorem compileCPSComposition_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileCPSComposition c = some t) : CPSRepresents t (Nat.Partrec.Code.eval c) := by
  induction c generalizing t with
  | comp f g ihf ihg =>
    cases hc : decodeConst (.comp f g) with
    | some n =>
      have ht : cpsConstant n = t := by simpa [compileCPSComposition, hc] using h
      subst t
      have heq := decodeConst_sound (.comp f g) n hc
      rw [heq]
      exact cpsConstant_represents n
    | none =>
      cases hf : compileCPSComposition f with
      | none => simp [compileCPSComposition, hc, hf] at h
      | some F =>
        cases hg : compileCPSComposition g with
        | none => simp [compileCPSComposition, hc, hf, hg] at h
        | some G =>
          have ht : cpsCompose F G = t := by simpa [compileCPSComposition, hc, hf, hg] using h
          subst t
          have heval : Nat.Partrec.Code.eval (.comp f g) =
              (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
            funext n
            exact Part.bind_eq_bind _ _
          rw [heval]
          exact cpsCompose_represents (ihf F hf) (ihg G hg)
  | zero => exact compileCPSBase_sound _ _ h
  | succ => exact compileCPSBase_sound _ _ h
  | left => exact compileCPSBase_sound _ _ h
  | right => exact compileCPSBase_sound _ _ h
  | pair f g ihf ihg => exact compileCPSBase_sound _ _ h
  | prec f g ihf ihg => exact compileCPSBase_sound _ _ h
  | rfind' f ih => exact compileCPSBase_sound _ _ h

/-- The supported fragment is closed under arbitrary finite composition. -/
inductive CPSCompositionSupported : Nat.Partrec.Code → Prop where
  | constant (n : Nat) : CPSCompositionSupported (Nat.Partrec.Code.const n)
  | identity : CPSCompositionSupported Nat.Partrec.Code.id
  | composition {f g : Nat.Partrec.Code} :
      CPSCompositionSupported f → CPSCompositionSupported g → CPSCompositionSupported (.comp f g)

theorem compileCPSComposition_complete {c : Nat.Partrec.Code} (h : CPSCompositionSupported c) :
    ∃ t, compileCPSComposition c = some t := by
  induction h with
  | constant n => exact ⟨cpsConstant n, compileCPSComposition_const n⟩
  | identity => exact ⟨cpsIdentity, compileCPSComposition_id⟩
  | @composition f g _ _ ihf ihg =>
    obtain ⟨F, hf⟩ := ihf
    obtain ⟨G, hg⟩ := ihg
    cases hc : decodeConst (.comp f g) with
    | some n => exact ⟨cpsConstant n, by simp [compileCPSComposition, hc]⟩
    | none => exact ⟨cpsCompose F G, compileCPSComposition_comp f g F G hc hf hg⟩

/-- Close a compiled CPS program with the identity continuation. -/
def compileComposition (c : Nat.Partrec.Code) : Option Term :=
  (compileCPSComposition c).map cpsUnary

theorem compileComposition_sound (c : Nat.Partrec.Code) (t : Term)
    (h : compileComposition c = some t) : Represents t (Nat.Partrec.Code.eval c) := by
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact cpsUnary_represents (compileCPSComposition_sound c C hC)

theorem compileComposition_complete {c : Nat.Partrec.Code} (h : CPSCompositionSupported c) :
    ∃ t, compileComposition c = some t := by
  obtain ⟨C, hC⟩ := compileCPSComposition_complete h
  exact ⟨cpsUnary C, by simp [compileComposition, hC]⟩

theorem primrec_cpsCompose : Primrec₂ cpsCompose := by
  let P := Term × Term
  have hF : Primrec (fun p : P => p.1) := Primrec.fst
  have hG : Primrec (fun p : P => p.2) := Primrec.snd
  have hinner : Primrec (fun p : P => Term.abs (.app (.app p.1 (.var 0)) (.var 1))) :=
    primrec_abs.comp (primrec_app.comp (primrec_app.comp hF (Primrec.const (Term.var 0)))
      (Primrec.const (Term.var 1)))
  exact primrec_abs.comp (primrec_abs.comp (primrec_app.comp
    (primrec_app.comp hG (Primrec.const (Term.var 1))) hinner))

def compileCPSFold (c : Nat.Partrec.Code) : Option Term :=
  Nat.Partrec.Code.recOn c (compileCPSBase .zero) (compileCPSBase .succ)
    (compileCPSBase .left) (compileCPSBase .right)
    (fun f g _ _ => compileCPSBase (.pair f g))
    (fun f g F G => match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => F.bind fun F' => G.map (cpsCompose F'))
    (fun f g _ _ => compileCPSBase (.prec f g))
    (fun f _ => compileCPSBase (.rfind' f))

theorem compileCPSFold_eq (c : Nat.Partrec.Code) : compileCPSFold c = compileCPSComposition c := by
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
      | none => (compileCPSFold f).bind fun F => (compileCPSFold g).map (cpsCompose F)) =
      (match decodeConst (.comp f g) with
      | some n => some (cpsConstant n)
      | none => (compileCPSComposition f).bind fun F =>
          (compileCPSComposition g).bind fun G => some (cpsCompose F G))
    rw [ihf, ihg]
    cases decodeConst (.comp f g) <;> cases compileCPSComposition f <;>
      cases compileCPSComposition g <;> rfl

set_option maxHeartbeats 1000000 in
theorem primrec_compileCPSFold : Primrec compileCPSFold := by
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
    (s := fun _ : A => compileCPSBase .succ) (l := fun _ : A => compileCPSBase .left)
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

theorem primrec_compileCPSComposition : Primrec compileCPSComposition :=
  primrec_compileCPSFold.of_eq compileCPSFold_eq

theorem primrec_cpsUnary : Primrec cpsUnary :=
  primrec_abs.comp (primrec_app.comp (primrec_app.comp Primrec.id (Primrec.const (Term.var 0)))
    (Primrec.const identityTerm))

theorem primrec_compileComposition : Primrec compileComposition :=
  (Primrec.option_map₁ primrec_cpsUnary).comp primrec_compileCPSComposition

#print axioms substAt_liftFrom
#print axioms noNormal_backward
#print axioms cpsCompose_run
#print axioms cpsComposeCont_run
#print axioms cpsCompose_represents
#print axioms compileCPSComposition_sound
#print axioms compileComposition_sound
#print axioms compileComposition_complete
#print axioms primrec_compileComposition

end LambdaTuring
