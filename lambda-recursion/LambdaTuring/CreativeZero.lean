/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
import LambdaTuring.EffectiveLambdaRecursion

namespace LambdaTuring

/-- Program zero if a coded recognizer accepts the given syntax; otherwise no
numerical result. Invalid recognizer encodings use a fixed fallback. -/
def recognizerZeroProgram (p : Nat × Term) : Term :=
  let c := (Encodable.decode p.1 : Option Nat.Partrec.Code).getD .zero
  compileLambdaTotal (.comp (.const 0) (.comp c (.const (executableTermEncode p.2))))

theorem recognizerZeroProgram_primrec : Primrec recognizerZeroProgram := by
  let P := Nat × Term
  have hc : Primrec (fun p : P =>
      (Encodable.decode p.1 : Option Nat.Partrec.Code).getD .zero) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const _)).comp Primrec.fst
  have he : Primrec (fun p : P => executableTermEncode p.2) :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).comp Primrec.snd
  have hconst : Primrec (fun p : P => Nat.Partrec.Code.const (executableTermEncode p.2)) :=
    Nat.Partrec.Code.primrec_const.comp he
  have hinner : Primrec (fun p : P => Nat.Partrec.Code.comp
      ((Encodable.decode p.1 : Option Nat.Partrec.Code).getD .zero)
      (Nat.Partrec.Code.const (executableTermEncode p.2))) :=
    Nat.Partrec.Code.primrec₂_comp.comp hc hconst
  exact primrec_compileLambdaTotal.comp (Nat.Partrec.Code.primrec₂_comp.comp
    (Primrec.const (Nat.Partrec.Code.const 0)) hinner)

/-- A uniform closed diagonal has numerical output zero exactly when its
argument recognizer accepts it. -/
theorem closed_zero_diagonal :
    ∃ diagonal : Nat.Partrec.Code → Term, Primrec diagonal ∧
      ∀ c, Scoped 0 (diagonal c) ∧
        (NumericalResult (diagonal c) 0 0 ↔ codeAcceptsTerm c (diagonal c)) := by
  obtain ⟨q, hq, hfixed⟩ :=
    lambda_recursion_with_parameters recognizerZeroProgram recognizerZeroProgram_primrec.to_comp
  let diagonal : Nat.Partrec.Code → Term := fun c => q (Encodable.encode c)
  refine ⟨diagonal, hq.comp Primrec.encode, ?_⟩
  intro c
  let t := diagonal c
  refine ⟨(hfixed (Encodable.encode c)).1, ?_⟩
  have hv : numericalValue t 0 =
      (Nat.Partrec.Code.eval c (executableTermEncode t)).bind (fun _ => Part.some 0) := by
    rw [(hfixed (Encodable.encode c)).2 0]
    simp only [recognizerZeroProgram, Encodable.encodek, Option.getD_some]
    change numericalValue (compileLambdaTotal (.comp (.const 0)
      (.comp c (.const (executableTermEncode t))))) 0 = _
    rw [(compileLambdaTotal_sound _).2 0]
    change ((Nat.Partrec.Code.eval (.const (executableTermEncode t)) 0).bind
      (fun x => Nat.Partrec.Code.eval c x)).bind
        (fun x => Nat.Partrec.Code.eval (.const 0) x) = _
    rw [Nat.Partrec.Code.eval_const, Part.bind_some]
    simp only [Nat.Partrec.Code.eval_const]
  rw [← mem_numericalValue_iff, hv, codeAcceptsTerm]
  constructor
  · intro h
    obtain ⟨v, hv, _⟩ := Part.mem_bind_iff.1 h
    exact (Part.dom_iff_mem).2 ⟨v, hv⟩
  · intro h
    obtain ⟨v, hv⟩ := (Part.dom_iff_mem).1 h
    exact Part.mem_bind_iff.2 ⟨v, hv, by simp⟩

/-- The complement of the closed zero-result language is productive, even
against recognizer subsets required to avoid it only on closed syntax. -/
theorem closed_zero_productive_complement :
    ∃ productive : Nat.Partrec.Code → Term, Primrec productive ∧
      ∀ c, (∀ t, Scoped 0 t → codeAcceptsTerm c t → ¬ closedNumeralAtZero 0 t) →
        Scoped 0 (productive c) ∧ ¬ closedNumeralAtZero 0 (productive c) ∧
          ¬ codeAcceptsTerm c (productive c) := by
  obtain ⟨diagonal, hd, hdiag⟩ := closed_zero_diagonal
  refine ⟨diagonal, hd, ?_⟩
  intro c hc
  have hs := (hdiag c).1
  have he : ¬ codeAcceptsTerm c (diagonal c) := by
    intro ha
    exact hc _ hs ha ⟨hs, (hdiag c).2.mpr ha⟩
  exact ⟨hs, fun h => he ((hdiag c).2.mp h.2), he⟩

/-- Encode a recursive-program halting question as a closed program whose
only possible numerical result is zero. -/
def codeHaltingToClosedZero (p : Nat.Partrec.Code × Nat) : Term :=
  compileLambdaTotal (.comp (.const 0) (.comp p.1 (.const p.2)))

theorem codeHaltingToClosedZero_primrec : Primrec codeHaltingToClosedZero := by
  have hinner : Primrec (fun p : Nat.Partrec.Code × Nat =>
      Nat.Partrec.Code.comp p.1 (.const p.2)) :=
    Nat.Partrec.Code.primrec₂_comp.comp Primrec.fst
      (Nat.Partrec.Code.primrec_const.comp Primrec.snd)
  exact primrec_compileLambdaTotal.comp (Nat.Partrec.Code.primrec₂_comp.comp
    (Primrec.const (Nat.Partrec.Code.const 0)) hinner)

theorem codeHaltingToClosedZero_correct (c : Nat.Partrec.Code) (n : Nat) :
    Scoped 0 (codeHaltingToClosedZero (c, n)) ∧
      (closedNumeralAtZero 0 (codeHaltingToClosedZero (c, n)) ↔
        (Nat.Partrec.Code.eval c n).Dom) := by
  let t := codeHaltingToClosedZero (c, n)
  have hs : Scoped 0 t := (compileLambdaTotal_sound _).1
  have hv : numericalValue t 0 =
      (Nat.Partrec.Code.eval c n).bind (fun _ => Part.some 0) := by
    change numericalValue (compileLambdaTotal (.comp (.const 0) (.comp c (.const n)))) 0 = _
    rw [(compileLambdaTotal_sound _).2 0]
    change ((Nat.Partrec.Code.eval (.const n) 0).bind
      (fun x => Nat.Partrec.Code.eval c x)).bind
        (fun x => Nat.Partrec.Code.eval (.const 0) x) = _
    rw [Nat.Partrec.Code.eval_const, Part.bind_some]
    simp only [Nat.Partrec.Code.eval_const]
  refine ⟨hs, ?_⟩
  constructor
  · rintro ⟨_, hr⟩
    have hm : 0 ∈ (Nat.Partrec.Code.eval c n).bind (fun _ => Part.some 0) := by
      rw [← hv]
      exact (mem_numericalValue_iff _ _ _).2 hr
    obtain ⟨v, hv, _⟩ := Part.mem_bind_iff.1 hm
    exact (Part.dom_iff_mem).2 ⟨v, hv⟩
  · intro hd
    obtain ⟨v, hv'⟩ := (Part.dom_iff_mem).1 hd
    refine ⟨hs, (mem_numericalValue_iff _ _ _).1 ?_⟩
    rw [hv]
    exact Part.mem_bind_iff.2 ⟨v, hv', by simp⟩

/-- On every numeral input, the compiled program has exactly the result
zero when the encoded computation is defined, and no other numerical result. -/
theorem codeHaltingToClosedZero_result (c : Nat.Partrec.Code) (n x m : Nat) :
    NumericalResult (codeHaltingToClosedZero (c, n)) x m ↔
      m = 0 ∧ (Nat.Partrec.Code.eval c n).Dom := by
  have hv : numericalValue (codeHaltingToClosedZero (c, n)) x =
      (Nat.Partrec.Code.eval c n).bind (fun _ => Part.some 0) := by
    change numericalValue (compileLambdaTotal (.comp (.const 0) (.comp c (.const n)))) x = _
    rw [(compileLambdaTotal_sound _).2 x]
    change ((Nat.Partrec.Code.eval (.const n) x).bind
      (fun y => Nat.Partrec.Code.eval c y)).bind
        (fun y => Nat.Partrec.Code.eval (.const 0) y) = _
    rw [Nat.Partrec.Code.eval_const, Part.bind_some]
    simp only [Nat.Partrec.Code.eval_const]
  rw [← mem_numericalValue_iff, hv, Part.mem_bind_iff]
  constructor
  · rintro ⟨v, hv, hm⟩
    exact ⟨by simpa using hm, (Part.dom_iff_mem).2 ⟨v, hv⟩⟩
  · rintro ⟨rfl, hd⟩
    obtain ⟨v, hv⟩ := (Part.dom_iff_mem).1 hd
    exact ⟨v, hv, by simp⟩

/-- Every r.e. predicate computably reduces to the concrete closed
zero-result language. The code for the fixed predicate is chosen by existence. -/
theorem closed_zero_manyOne_complete {α : Type} [Primcodable α]
    (p : α → Prop) (hp : REPred p) : ManyOneReducible p (closedNumeralAtZero 0) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hdom (a : α) : (Nat.Partrec.Code.eval c (Encodable.encode a)).Dom ↔ p a := by
    rw [hc]
    simp [Encodable.encodek, Part.assert]
  refine ⟨fun a => codeHaltingToClosedZero (c, Encodable.encode a), ?_, ?_⟩
  · exact codeHaltingToClosedZero_primrec.to_comp.comp
      ((Computable.const c).pair Computable.encode)
  · intro a
    exact (hdom a).symm.trans (codeHaltingToClosedZero_correct c (Encodable.encode a)).2.symm

#print axioms closed_zero_diagonal
#print axioms closed_zero_productive_complement
#print axioms codeHaltingToClosedZero_correct
#print axioms codeHaltingToClosedZero_result
#print axioms closed_zero_manyOne_complete
end LambdaTuring
