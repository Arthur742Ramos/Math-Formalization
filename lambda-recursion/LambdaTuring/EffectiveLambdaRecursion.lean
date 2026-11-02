/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

Working increment: recursion and self-reference for closed lambda syntax.
-/
module
public import LambdaTuring.TotalityBounded
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LambdaTuring

/-- Specializing a recursive program and compiling it to a closed lambda term
is primitive recursive in both the program and its parameter. -/
def specializeToLambda (p : Nat.Partrec.Code × Nat) : Term :=
  compileLambdaTotal (Nat.Partrec.Code.curry p.1 p.2)

theorem specializeToLambda_primrec : Primrec specializeToLambda :=
  primrec_compileLambdaTotal.comp Nat.Partrec.Code.primrec₂_curry

theorem specializeToLambda_closed (c : Nat.Partrec.Code) (a : Nat) :
    Scoped 0 (specializeToLambda (c, a)) := (compileLambdaTotal_sound _).1

theorem specializeToLambda_value (c : Nat.Partrec.Code) (a n : Nat) :
    numericalValue (specializeToLambda (c, a)) n = Nat.Partrec.Code.eval c (Nat.pair a n) := by
  rw [specializeToLambda, (compileLambdaTotal_sound _).2 n, Nat.Partrec.Code.eval_curry]

/-- A computable transformation of syntax has a uniform family of closed
extensional fixed points. The family is primitive recursive after choosing one
recursive code for the transformation. -/
theorem lambda_recursion_with_parameters (G : Nat × Term → Term) (hG : Computable G) :
    ∃ q : Nat → Term, Primrec q ∧ ∀ a, Scoped 0 (q a) ∧
      ∀ n, numericalValue (q a) n = numericalValue (G (a, q a)) n := by
  let P := Nat.Partrec.Code × Nat
  have hc : Computable (fun p : P => p.1) := Computable.fst
  have hu : Computable (fun p : P => Nat.unpair p.2) := Computable.unpair.comp Computable.snd
  have ha : Computable (fun p : P => (Nat.unpair p.2).1) := Computable.fst.comp hu
  have hn : Computable (fun p : P => (Nat.unpair p.2).2) := Computable.snd.comp hu
  have hq : Computable (fun p : P => specializeToLambda (p.1, (Nat.unpair p.2).1)) :=
    specializeToLambda_primrec.to_comp.comp (hc.pair ha)
  have hterm : Computable (fun p : P => G ((Nat.unpair p.2).1,
      specializeToLambda (p.1, (Nat.unpair p.2).1))) := hG.comp (ha.pair hq)
  have hfun : Partrec₂ (fun c n => numericalValue
      (G ((Nat.unpair n).1, specializeToLambda (c, (Nat.unpair n).1))) (Nat.unpair n).2) :=
    (uniformNumericalValue_partrec.comp (hterm.pair hn)).to₂
  obtain ⟨c, hcfix⟩ := Nat.Partrec.Code.fixed_point₂ hfun
  let q : Nat → Term := fun a => specializeToLambda (c, a)
  have hq' : Primrec q := specializeToLambda_primrec.comp ((Primrec.const c).pair Primrec.id)
  refine ⟨q, hq', ?_⟩
  intro a
  refine ⟨specializeToLambda_closed c a, ?_⟩
  intro n
  rw [specializeToLambda_value]
  have h := congrFun hcfix (Nat.pair a n)
  simpa [Nat.unpair_pair, q] using h

/-- Closed lambda programs can uniformly return any computable function of
their parameter and their own canonical syntax code. -/
theorem lambda_computable_self_code (g : Nat × Nat → Nat) (hg : Computable g) :
    ∃ q : Nat → Term, Primrec q ∧ ∀ a, Scoped 0 (q a) ∧
      ∀ n, NumericalResult (q a) n (g (a, executableTermEncode (q a))) := by
  let G : Nat × Term → Term := fun p =>
    compileLambdaTotal (Nat.Partrec.Code.const (g (p.1, executableTermEncode p.2)))
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have hG : Computable G :=
    (primrec_compileLambdaTotal.comp Nat.Partrec.Code.primrec_const).to_comp.comp
      (hg.comp (Computable.fst.pair (henc.comp Computable.snd)))
  obtain ⟨q, hq, hfixed⟩ := lambda_recursion_with_parameters G hG
  refine ⟨q, hq, ?_⟩
  intro a
  refine ⟨(hfixed a).1, ?_⟩
  intro n
  apply (mem_numericalValue_iff _ _ _).1
  rw [(hfixed a).2 n]
  change g (a, executableTermEncode (q a)) ∈
    numericalValue (compileLambdaTotal (Nat.Partrec.Code.const
      (g (a, executableTermEncode (q a))))) n
  rw [(compileLambdaTotal_sound _).2 n, Nat.Partrec.Code.eval_const]
  simp

/-- A numerical self-code program returns the code of its own closed syntax
on every numeral input. This is observational self-reference, not a claim of
literal source reproduction. -/
theorem closed_numerical_self_code :
    ∃ t : Term, Scoped 0 t ∧ ∀ n, NumericalResult t n (executableTermEncode t) := by
  obtain ⟨q, _, hq⟩ := lambda_computable_self_code (fun p : Nat × Nat => p.2) Computable.snd
  exact ⟨q 0, (hq 0).1, by simpa using (hq 0).2⟩

/-- No total computable Boolean test separates closed terms returning zero
on input zero from those returning one on input zero. -/
theorem no_computable_zero_one_separator (d : Term → Bool) (hd : Computable d)
    (hzero : ∀ t, Scoped 0 t → NumericalResult t 0 0 → d t = true)
    (hone : ∀ t, Scoped 0 t → NumericalResult t 0 1 → d t = false) : False := by
  let G : Nat × Term → Term := fun p => bif d p.2 then
    compileLambdaTotal (Nat.Partrec.Code.const 1) else
    compileLambdaTotal (Nat.Partrec.Code.const 0)
  have hG : Computable G := Computable.cond (hd.comp Computable.snd)
    (Computable.const _) (Computable.const _)
  obtain ⟨q, _, hq⟩ := lambda_recursion_with_parameters G hG
  let t := q 0
  have hs : Scoped 0 t := (hq 0).1
  have hfix : ∀ n, numericalValue t n = numericalValue (G (0, t)) n := (hq 0).2
  cases h : d t with
  | false =>
    have hv : numericalValue t 0 = Part.some 0 := by
      rw [hfix]
      simp [G, h, (compileLambdaTotal_sound _).2, Nat.Partrec.Code.eval_const]
    have hr : NumericalResult t 0 0 := (mem_numericalValue_iff _ _ _).1 (by rw [hv]; simp)
    have he := hzero t hs hr
    rw [h] at he
    contradiction
  | true =>
    have hv : numericalValue t 0 = Part.some 1 := by
      rw [hfix]
      simp [G, h, (compileLambdaTotal_sound _).2, Nat.Partrec.Code.eval_const]
    have hr : NumericalResult t 0 1 := (mem_numericalValue_iff _ _ _).1 (by rw [hv]; simp)
    have he := hone t hs hr
    rw [h] at he
    contradiction

/-- The concrete closed-term language that returns numeral `m` on numeral
input zero. -/
def closedNumeralAtZero (m : Nat) (t : Term) : Prop :=
  Scoped 0 t ∧ NumericalResult t 0 m

def numeralAtZeroStage (m : Nat) (p : Term × Nat) : Option Unit :=
  if (breadthObservations p.2 p.1 0).head? = some m then some () else none

theorem numeralAtZeroStage_primrec (m : Nat) : Primrec (numeralAtZeroStage m) := by
  have hobs : Primrec (fun p : Term × Nat => (breadthObservations p.2 p.1 0).head?) :=
    primrec_uniformBreadthObservation.comp (Primrec.fst.pair (Primrec.const 0)) Primrec.snd
  exact Primrec.ite (Primrec.eq.comp hobs (Primrec.const _)) (Primrec.const _) (Primrec.const _)

noncomputable def numeralAtZeroSearch (m : Nat) (t : Term) : Part Unit :=
  Nat.rfindOpt fun k => numeralAtZeroStage m (t, k)

theorem numeralAtZeroSearch_partrec (m : Nat) : Partrec (numeralAtZeroSearch m) :=
  Partrec.rfindOpt (numeralAtZeroStage_primrec m).to_comp

theorem numeralAtZeroSearch_dom (m : Nat) (t : Term) :
    (numeralAtZeroSearch m t).Dom ↔ NumericalResult t 0 m := by
  rw [numeralAtZeroSearch, Nat.rfindOpt_dom]
  constructor
  · rintro ⟨k, x, hx⟩
    have hhead : (breadthObservations k t 0).head? = some m := by
      by_contra h
      simp [numeralAtZeroStage, h] at hx
    exact (numeral_iff_breadth t 0 m).2 ⟨k, List.mem_of_mem_head? (by simpa using hhead)⟩
  · intro hm
    have hm' : m ∈ breadthSearch t 0 := (mem_breadthSearch_iff t 0 m).2 hm
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hm'
    have hhead : (breadthObservations k t 0).head? = some m := by simpa using hk
    exact ⟨k, (), by simp [numeralAtZeroStage, hhead]⟩

/-- Each exact numeral-result language is recursively enumerable. -/
theorem closedNumeralAtZero_re (m : Nat) : REPred (closedNumeralAtZero m) := by
  let closed : Term → Bool := fun t => decide (requiredDepth t ≤ 0)
  have hclosed : Computable closed :=
    (Primrec.nat_le.comp primrec_requiredDepth (Primrec.const 0)).decide.to_comp
  have hguard : Partrec (fun t : Term =>
      bif closed t then numeralAtZeroSearch m t else Part.none) :=
    Partrec.cond hclosed (numeralAtZeroSearch_partrec m) Partrec.none
  apply hguard.dom_re.of_eq
  intro t
  by_cases hs : Scoped 0 t
  · have hz : requiredDepth t = 0 := Nat.le_zero.mp ((scoped_iff_requiredDepth_le t 0).1 hs)
    simp [closed, hz, hs, closedNumeralAtZero, numeralAtZeroSearch_dom]
  · have hz : requiredDepth t ≠ 0 := fun h =>
      hs ((scoped_iff_requiredDepth_le t 0).2 (by omega))
    simp [closed, hz, hs, closedNumeralAtZero]

theorem closedZeroOne_disjoint (t : Term) :
    ¬ (closedNumeralAtZero 0 t ∧ closedNumeralAtZero 1 t) := by
  rintro ⟨⟨_, hzero⟩, ⟨_, hone⟩⟩
  have h := numeral_result_unique hzero hone
  omega

/-- Two disjoint recursively enumerable concrete closed-lambda languages are
not separable by a total computable Boolean predicate. -/
theorem closedZeroOne_recursively_inseparable :
    REPred (closedNumeralAtZero 0) ∧ REPred (closedNumeralAtZero 1) ∧
    (∀ t, ¬ (closedNumeralAtZero 0 t ∧ closedNumeralAtZero 1 t)) ∧
    ¬ ∃ d : Term → Bool, Computable d ∧
      (∀ t, closedNumeralAtZero 0 t → d t = true) ∧
      (∀ t, closedNumeralAtZero 1 t → d t = false) := by
  refine ⟨closedNumeralAtZero_re 0, closedNumeralAtZero_re 1, closedZeroOne_disjoint, ?_⟩
  rintro ⟨d, hd, hzero, hone⟩
  exact no_computable_zero_one_separator d hd
    (fun t hs h => hzero t ⟨hs, h⟩) (fun t hs h => hone t ⟨hs, h⟩)

/-- A recursive-code recognizer accepts the canonical encoding of a term. -/
def codeAcceptsTerm (c : Nat.Partrec.Code) (t : Term) : Prop :=
  (Nat.Partrec.Code.eval c (executableTermEncode t)).Dom

/-- Every recursive code describes a recursively enumerable predicate on
the actual term encoding. -/
theorem codeAcceptsTerm_re (c : Nat.Partrec.Code) : REPred (codeAcceptsTerm c) := by
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  exact (Nat.Partrec.Code.eval_part.comp (Computable.const c) henc).dom_re

/-- Every recursively enumerable predicate on terms has a code using the same
canonical syntax encoding. The code is selected by existence. -/
theorem rePredicate_has_code (P : Term → Prop) (hP : REPred P) :
    ∃ c, ∀ t, codeAcceptsTerm c t ↔ P t := by
  have hp := hP
  change Nat.Partrec (fun n => Part.bind (Part.ofOption (Encodable.decode (α := Term) n))
    fun t => (Part.assert (P t) (fun _ => Part.some ())).map Encodable.encode) at hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨c, ?_⟩
  intro t
  have he : Nat.Partrec.Code.eval c (Encodable.encode t) =
      (Part.assert (P t) (fun _ => Part.some ())).map Encodable.encode := by
    have h := congrFun hc (Encodable.encode t)
    simpa only [Encodable.encodek, Part.coe_some, Part.bind_some] using h
  rw [codeAcceptsTerm, executableTermEncode_eq, he]
  by_cases h : P t
  · simp [Part.assert_pos h, h]
  · simp [Part.assert_neg h, h]

theorem codeAcceptsTerm_iff_stage (c : Nat.Partrec.Code) (t : Term) :
    codeAcceptsTerm c t ↔
      ∃ k, (Nat.Partrec.Code.evaln k c (executableTermEncode t)).isSome = true := by
  constructor
  · intro hd
    obtain ⟨v, hv⟩ := (Part.dom_iff_mem).1 hd
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨k, ?_⟩
    cases h : Nat.Partrec.Code.evaln k c (executableTermEncode t) with
    | none => simp [h] at hk
    | some v => rfl
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k c (executableTermEncode t) with
    | none => simp [h] at hk
    | some v =>
      exact (Part.dom_iff_mem).2 ⟨v, Nat.Partrec.Code.evaln_sound (by rw [h]; simp)⟩

/-- A bounded diagonal observation favors the left recognizer if both have
accepted by the same stage. Disjointness is only used later in the proof. -/
def opposingStage (p : (Nat × Term) × Nat) : Option Nat :=
  let ef := (Encodable.decode p.1.1 : Option (Nat.Partrec.Code × Nat.Partrec.Code)).getD (.zero, .zero)
  let code := executableTermEncode p.1.2
  let left := (Nat.Partrec.Code.evaln p.2 ef.1 code).isSome
  let right := (Nat.Partrec.Code.evaln p.2 ef.2 code).isSome
  bif left then some 1 else bif right then some 0 else none

theorem opposingStage_primrec : Primrec opposingStage := by
  let P := (Nat × Term) × Nat
  have ha : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun p : P => p.2) := Primrec.snd
  have hef : Primrec (fun p : P =>
      (Encodable.decode p.1.1 : Option (Nat.Partrec.Code × Nat.Partrec.Code)).getD (.zero, .zero)) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const _)).comp ha
  have hcode : Primrec (fun p : P => executableTermEncode p.1.2) :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).comp ht
  have hl : Primrec (fun p : P =>
      (Nat.Partrec.Code.evaln p.2
        ((Encodable.decode p.1.1 : Option (Nat.Partrec.Code × Nat.Partrec.Code)).getD (.zero, .zero)).1
        (executableTermEncode p.1.2)).isSome) :=
    Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      ((hk.pair (Primrec.fst.comp hef)).pair hcode))
  have hr : Primrec (fun p : P =>
      (Nat.Partrec.Code.evaln p.2
        ((Encodable.decode p.1.1 : Option (Nat.Partrec.Code × Nat.Partrec.Code)).getD (.zero, .zero)).2
        (executableTermEncode p.1.2)).isSome) :=
    Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      ((hk.pair (Primrec.snd.comp hef)).pair hcode))
  exact Primrec.cond hl (Primrec.const (some 1))
    (Primrec.cond hr (Primrec.const (some 0)) (Primrec.const none))

noncomputable def opposingSearch (a : Nat) (t : Term) : Part Nat :=
  Nat.rfindOpt fun k => opposingStage ((a, t), k)

theorem opposingSearch_partrec :
    Partrec (fun p : Nat × Term => opposingSearch p.1 p.2) :=
  Partrec.rfindOpt opposingStage_primrec.to_comp

theorem codeAcceptsTerm_no_stage (c : Nat.Partrec.Code) (t : Term)
    (h : ¬ codeAcceptsTerm c t) (k : Nat) :
    Nat.Partrec.Code.evaln k c (executableTermEncode t) = none := by
  cases he : Nat.Partrec.Code.evaln k c (executableTermEncode t) with
  | none => rfl
  | some v =>
    have hv : v ∈ Nat.Partrec.Code.eval c (executableTermEncode t) :=
      Nat.Partrec.Code.evaln_sound (by rw [he]; simp)
    exact False.elim (h ((Part.dom_iff_mem).2 ⟨v, hv⟩))

theorem opposingSearch_left (e f : Nat.Partrec.Code) (t : Term)
    (he : codeAcceptsTerm e t) (hf : ¬ codeAcceptsTerm f t) :
    opposingSearch (Encodable.encode (e, f)) t = Part.some 1 := by
  obtain ⟨k, hk⟩ := (codeAcceptsTerm_iff_stage e t).1 he
  have hd : (opposingSearch (Encodable.encode (e, f)) t).Dom := by
    apply Nat.rfindOpt_dom.2
    exact ⟨k, 1, by simp [opposingStage, hk]⟩
  obtain ⟨v, hv⟩ := (Part.dom_iff_mem).1 hd
  obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hv
  have hn := codeAcceptsTerm_no_stage f t hf s
  have hv1 : v = 1 := by
    cases hc : (Nat.Partrec.Code.evaln s e (executableTermEncode t)).isSome <;>
      simp [opposingStage, hc, hn] at hs
    exact hs.symm
  subst v
  exact Part.eq_some_iff.2 hv

theorem opposingSearch_right (e f : Nat.Partrec.Code) (t : Term)
    (he : ¬ codeAcceptsTerm e t) (hf : codeAcceptsTerm f t) :
    opposingSearch (Encodable.encode (e, f)) t = Part.some 0 := by
  obtain ⟨k, hk⟩ := (codeAcceptsTerm_iff_stage f t).1 hf
  have hn := codeAcceptsTerm_no_stage e t he k
  have hd : (opposingSearch (Encodable.encode (e, f)) t).Dom := by
    apply Nat.rfindOpt_dom.2
    exact ⟨k, 0, by simp [opposingStage, hn, hk]⟩
  obtain ⟨v, hv⟩ := (Part.dom_iff_mem).1 hd
  obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hv
  have hn' := codeAcceptsTerm_no_stage e t he s
  have hv0 : v = 0 := by
    cases hc : (Nat.Partrec.Code.evaln s f (executableTermEncode t)).isSome <;>
      simp [opposingStage, hc, hn'] at hs
    exact hs.symm
  subst v
  exact Part.eq_some_iff.2 hv

/-- A primitive-recursive productive map for the two concrete numeral
languages: from any pair of recognizer codes whose closed-term supersets are
disjoint, it produces a closed term outside both supersets. -/
theorem closedZeroOne_effectively_inseparable :
    ∃ productive : Nat.Partrec.Code × Nat.Partrec.Code → Term, Primrec productive ∧
      ∀ e f,
        (∀ t, closedNumeralAtZero 0 t → codeAcceptsTerm e t) →
        (∀ t, closedNumeralAtZero 1 t → codeAcceptsTerm f t) →
        (∀ t, Scoped 0 t → ¬ (codeAcceptsTerm e t ∧ codeAcceptsTerm f t)) →
        Scoped 0 (productive (e, f)) ∧
          ¬ codeAcceptsTerm e (productive (e, f)) ∧
          ¬ codeAcceptsTerm f (productive (e, f)) := by
  have hp : Partrec (fun p : (Nat × Term) × Nat => opposingSearch p.1.1 p.1.2) :=
    opposingSearch_partrec.comp Computable.fst
  change Nat.Partrec (fun n => Part.bind
      (Part.ofOption (Encodable.decode (α := (Nat × Term) × Nat) n)) fun p =>
      (opposingSearch p.1.1 p.1.2).map Encodable.encode) at hp
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hu' (a : Nat) (t : Term) (n : Nat) :
      Nat.Partrec.Code.eval u (Nat.pair (Nat.pair a (executableTermEncode t)) n) =
        opposingSearch a t := by
    have h := congrFun hu (Encodable.encode ((a, t), n))
    simpa [Encodable.encode_prod_val, executableTermEncode_eq, Part.map_id'] using h
  let G : Nat × Term → Term := fun p =>
    specializeToLambda (u, Nat.pair p.1 (executableTermEncode p.2))
  have henc : Primrec executableTermEncode :=
    Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)
  have harg : Primrec (fun p : Nat × Term => Nat.pair p.1 (executableTermEncode p.2)) :=
    Primrec₂.natPair.comp Primrec.fst (henc.comp Primrec.snd)
  have hG : Computable G :=
    (specializeToLambda_primrec.comp ((Primrec.const u).pair harg)).to_comp
  obtain ⟨q, hq, hfixed⟩ := lambda_recursion_with_parameters G hG
  let productive : Nat.Partrec.Code × Nat.Partrec.Code → Term := fun p => q (Encodable.encode p)
  have hprod : Primrec productive := hq.comp Primrec.encode
  refine ⟨productive, hprod, ?_⟩
  intro e f hzero hone hdis
  let a := Encodable.encode (e, f)
  let t := productive (e, f)
  have hs : Scoped 0 t := (hfixed a).1
  have hrun (n : Nat) : numericalValue t n = opposingSearch a t := by
    rw [(hfixed a).2 n]
    change numericalValue (specializeToLambda (u, Nat.pair a (executableTermEncode t))) n = _
    rw [specializeToLambda_value, hu']
  refine ⟨hs, ?_, ?_⟩
  · intro he
    have hf : ¬ codeAcceptsTerm f t := fun hf => hdis t hs ⟨he, hf⟩
    have hv : numericalValue t 0 = Part.some 1 := by
      rw [hrun, opposingSearch_left e f t he hf]
    have hr : NumericalResult t 0 1 := (mem_numericalValue_iff _ _ _).1 (by rw [hv]; simp)
    exact hf (hone t ⟨hs, hr⟩)
  · intro hf
    have he : ¬ codeAcceptsTerm e t := fun he => hdis t hs ⟨he, hf⟩
    have hv : numericalValue t 0 = Part.some 0 := by
      rw [hrun, opposingSearch_right e f t he hf]
    have hr : NumericalResult t 0 0 := (mem_numericalValue_iff _ _ _).1 (by rw [hv]; simp)
    exact he (hzero t ⟨hs, hr⟩)

#print axioms lambda_recursion_with_parameters
#print axioms lambda_computable_self_code
#print axioms no_computable_zero_one_separator
#print axioms closedZeroOne_recursively_inseparable
#print axioms closedZeroOne_effectively_inseparable
#print axioms rePredicate_has_code
end LambdaTuring
