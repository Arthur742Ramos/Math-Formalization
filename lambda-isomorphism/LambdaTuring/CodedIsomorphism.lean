/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.FiniteOrbit
public meta import LambdaTuring.FiniteOrbit

@[expose] public section
namespace LambdaTuring

/-- Decode syntax with a fixed open-term fallback. Membership below also checks
canonical re-encoding, so invalid or noncanonical codes cannot be accepted. -/
def decodedSyntax (n : Nat) : Term :=
  (executableTermDecode n).getD (.var 0)

def codedClosedZero (n : Nat) : Prop :=
  n = executableTermEncode (decodedSyntax n) ∧ closedNumeralAtZero 0 (decodedSyntax n)

theorem decodedSyntax_primrec : Primrec decodedSyntax := by
  have h : Primrec (fun n : Nat => (Encodable.decode n : Option Term).getD (.var 0)) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const _)
  exact h.of_eq (fun n => by simp [decodedSyntax, executableTermDecode_eq])

theorem codedClosedZero_encode (t : Term) :
    codedClosedZero (executableTermEncode t) ↔ closedNumeralAtZero 0 t := by
  simp [codedClosedZero, decodedSyntax, executableTermDecode_encode]

theorem codedClosedZero_exact (n : Nat) :
    codedClosedZero n ↔ ∃ t, executableTermEncode t = n ∧ closedNumeralAtZero 0 t := by
  constructor
  · rintro ⟨he, hz⟩
    exact ⟨decodedSyntax n, he.symm, hz⟩
  · rintro ⟨t, rfl, hz⟩
    exact (codedClosedZero_encode t).2 hz

theorem codedClosedZero_re : REPred codedClosedZero := by
  have hterm : Computable decodedSyntax := decodedSyntax_primrec.to_comp
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have hvalid : Computable (fun n : Nat => decide (n = executableTermEncode (decodedSyntax n))) :=
    (Primrec.eq : PrimrecRel (fun x y : Nat => x = y)).decide.to_comp.comp
      Computable.id (henc.comp hterm)
  have hclosed : Partrec (fun n : Nat =>
      Part.assert (closedNumeralAtZero 0 (decodedSyntax n)) fun _ => Part.some ()) :=
    (closedNumeralAtZero_re 0).comp hterm
  have hp := Partrec.cond hvalid hclosed Partrec.none
  apply hp.dom_re.of_eq
  intro n
  change (bif decide (n = executableTermEncode (decodedSyntax n)) then
    Part.assert (closedNumeralAtZero 0 (decodedSyntax n)) (fun _ => Part.some ())
    else Part.none).Dom ↔ codedClosedZero n
  by_cases he : n = executableTermEncode (decodedSyntax n)
  · have hb : decide (n = executableTermEncode (decodedSyntax n)) = true := decide_eq_true he
    simp only [hb, Bool.cond_true]
    change (∃ _ : closedNumeralAtZero 0 (decodedSyntax n), True) ↔ codedClosedZero n
    exact ⟨fun ⟨hz, _⟩ => ⟨he, hz⟩, fun h => ⟨h.2, trivial⟩⟩
  · have hb : decide (n = executableTermEncode (decodedSyntax n)) = false := decide_eq_false he
    simp only [hb, Bool.cond_false]
    change False ↔ codedClosedZero n
    exact ⟨False.elim, fun h => he h.1⟩

/-- Canonical code of a recursive program together with its numerical input. -/
def decodedCodeInput (n : Nat) : Nat.Partrec.Code × Nat :=
  (Encodable.decode n : Option (Nat.Partrec.Code × Nat)).getD (.zero, 0)

def codedHalting (n : Nat) : Prop :=
  n = Encodable.encode (decodedCodeInput n) ∧
    (Nat.Partrec.Code.eval (decodedCodeInput n).1 (decodedCodeInput n).2).Dom

theorem decodedCodeInput_primrec : Primrec decodedCodeInput :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const _)

theorem codedHalting_encode (p : Nat.Partrec.Code × Nat) :
    codedHalting (Encodable.encode p) ↔ (Nat.Partrec.Code.eval p.1 p.2).Dom := by
  have hd : decodedCodeInput (Encodable.encode p) = p := by
    unfold decodedCodeInput
    rw [Encodable.encodek]
    rfl
  change (Encodable.encode p = Encodable.encode (decodedCodeInput (Encodable.encode p)) ∧ _) ↔ _
  rw [hd]
  exact ⟨And.right, fun h => ⟨rfl, h⟩⟩

theorem codedHalting_re : REPred codedHalting := by
  have hd : Computable decodedCodeInput := decodedCodeInput_primrec.to_comp
  have hvalid : Computable (fun n : Nat => decide (n = Encodable.encode (decodedCodeInput n))) :=
    (Primrec.eq : PrimrecRel (fun x y : Nat => x = y)).decide.to_comp.comp
      Computable.id (Computable.encode.comp hd)
  have heval : Partrec (fun n : Nat => Nat.Partrec.Code.eval
      (decodedCodeInput n).1 (decodedCodeInput n).2) :=
    Nat.Partrec.Code.eval_part.comp (Computable.fst.comp hd) (Computable.snd.comp hd)
  have hp := Partrec.cond hvalid heval Partrec.none
  apply hp.dom_re.of_eq
  intro n
  by_cases he : n = Encodable.encode (decodedCodeInput n)
  · have hb : decide (n = Encodable.encode (decodedCodeInput n)) = true := decide_eq_true he
    simp only [hb, Bool.cond_true]
    exact ⟨fun h => ⟨he, h⟩, And.right⟩
  · have hb : decide (n = Encodable.encode (decodedCodeInput n)) = false := decide_eq_false he
    simp only [hb, Bool.cond_false]
    change False ↔ codedHalting n
    exact ⟨False.elim, fun h => he h.1⟩

theorem codedHalting_exact (n : Nat) :
    codedHalting n ↔ ∃ p : Nat.Partrec.Code × Nat,
      Encodable.encode p = n ∧ (Nat.Partrec.Code.eval p.1 p.2).Dom := by
  constructor
  · rintro ⟨he, hh⟩
    exact ⟨decodedCodeInput n, he.symm, hh⟩
  · rintro ⟨p, rfl, hh⟩
    exact (codedHalting_encode p).2 hh

/-- Invalid syntax codes are outside the concrete lambda language. -/
theorem codedClosedZero_invalid (n : Nat) (h : executableTermDecode n = none) :
    ¬ codedClosedZero n := by
  intro hz
  have hd := executableTermDecode_encode (decodedSyntax n)
  rw [← hz.1, h] at hd
  contradiction

/-- Invalid code-input encodings are outside the canonical halting language. -/
theorem codedHalting_invalid (n : Nat)
    (h : (Encodable.decode n : Option (Nat.Partrec.Code × Nat)) = none) :
    ¬ codedHalting n := by
  intro hh
  have hd := Encodable.encodek (decodedCodeInput n)
  rw [← hh.1, h] at hd
  contradiction

/-- Every r.e. numerical predicate has an injective primitive-recursive
reduction to the canonical code-input halting language. The recursive program
for the fixed predicate is selected by existence. -/
theorem codedHalting_oneOne_complete (p : Nat → Prop) (hp : REPred p) :
    ∃ f : Nat → Nat, Primrec f ∧ Function.Injective f ∧
      ∀ n, p n ↔ codedHalting (f n) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hdom (n : Nat) : (Nat.Partrec.Code.eval c (Encodable.encode n)).Dom ↔ p n := by
    rw [hc]
    simp [Part.assert]
  let f : Nat → Nat := fun n => Encodable.encode (c, Encodable.encode n)
  have hf : Primrec f := Primrec.encode.comp ((Primrec.const c).pair Primrec.encode)
  have hi : Function.Injective f := by
    intro a b hab
    have hpair : (c, Encodable.encode a) = (c, Encodable.encode b) :=
      Encodable.encode_injective hab
    exact Encodable.encode_injective (congrArg Prod.snd hpair)
  exact ⟨f, hf, hi, fun n => (hdom n).symm.trans
    (codedHalting_encode (c, Encodable.encode n)).symm⟩

/-- The canonical lambda zero-result language receives every r.e. numerical
language by an injective primitive-recursive map of natural-number codes. -/
theorem codedClosedZero_oneOne_complete (p : Nat → Prop) (hp : REPred p) :
    ∃ f : Nat → Nat, Primrec f ∧ Function.Injective f ∧
      ∀ n, p n ↔ codedClosedZero (f n) := by
  obtain ⟨g, hg, hgi, hgr⟩ := closed_zero_oneOne_complete p hp
  let f : Nat → Nat := fun n => executableTermEncode (g n)
  have henc : Primrec executableTermEncode :=
    Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)
  have hi : Function.Injective f := by
    intro a b hab
    apply hgi
    apply Encodable.encode_injective
    change executableTermEncode (g a) = executableTermEncode (g b) at hab
    simpa only [executableTermEncode_eq] using hab
  exact ⟨f, henc.comp hg, hi, fun n => (hgr n).trans (codedClosedZero_encode (g n)).symm⟩

/-- The canonical recursive-code halting language and the canonical codes of
closed lambda programs returning zero are computably isomorphic. -/
theorem codedHalting_closedZero_isomorphism :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧
      ∀ n, codedHalting n ↔ codedClosedZero (e n) := by
  obtain ⟨f, hf, hfi, hfr⟩ := codedClosedZero_oneOne_complete codedHalting codedHalting_re
  obtain ⟨g, hg, hgi, hgr⟩ := codedHalting_oneOne_complete codedClosedZero codedClosedZero_re
  exact computable_permutation_of_oneOneEquiv codedHalting codedClosedZero
    ⟨⟨f, hf.to_comp, hfi, hfr⟩, ⟨g, hg.to_comp, hgi, hgr⟩⟩

/-- On every actual encoded code-input pair, the isomorphism transports its
halting question to the closed lambda zero-result language. -/
theorem codeInput_closedZero_permutation :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧
      ∀ c n, codedClosedZero (e (Encodable.encode (c, n))) ↔
        (Nat.Partrec.Code.eval c n).Dom := by
  obtain ⟨e, he, hei, h⟩ := codedHalting_closedZero_isomorphism
  refine ⟨e, he, hei, ?_⟩
  intro c n
  exact (h (Encodable.encode (c, n))).symm.trans (codedHalting_encode (c, n))



/-- A Boolean set has members beyond every numerical bound. -/
def UnboundedTrue (test : Nat → Bool) : Prop :=
  ∀ a, ∃ n, a ≤ n ∧ test n = true

/-- The least member of a Boolean set at or beyond a specified bound. -/
noncomputable def firstTrueAfter (test : Nat → Bool) (h : UnboundedTrue test) (a : Nat) : Nat :=
  Nat.find (h a)

theorem firstTrueAfter_spec (test : Nat → Bool) (h : UnboundedTrue test) (a : Nat) :
    a ≤ firstTrueAfter test h a ∧ test (firstTrueAfter test h a) = true :=
  Nat.find_spec (h a)

theorem firstTrueAfter_le (test : Nat → Bool) (h : UnboundedTrue test) (a n : Nat)
    (han : a ≤ n) (hn : test n = true) : firstTrueAfter test h a ≤ n :=
  Nat.find_min' (h a) ⟨han, hn⟩

def afterBoolean (test : Nat → Bool) (a n : Nat) : Bool :=
  decide (a ≤ n) && test n

theorem afterBoolean_computable (test : Nat → Bool) (ht : Computable test) :
    Computable₂ (afterBoolean test) := by
  have hle : Computable (fun p : Nat × Nat => decide (p.1 ≤ p.2)) := Primrec.nat_le.decide.to_comp
  have h := Primrec.and.to_comp.comp hle (ht.comp Computable.snd)
  exact h.to₂

theorem firstTrueAfter_computable (test : Nat → Bool) (h : UnboundedTrue test)
    (ht : Computable test) : Computable (firstTrueAfter test h) := by
  have hbool := afterBoolean_computable test ht
  have hpart := Partrec.rfind hbool.partrec.to₂
  apply hpart.of_eq_tot
  intro a
  apply Nat.mem_rfind.mpr
  constructor
  · simp only [PFun.coe_val, Part.mem_some_iff]
    simp [afterBoolean, (firstTrueAfter_spec test h a).1, (firstTrueAfter_spec test h a).2]
  · intro n hn
    simp only [PFun.coe_val, Part.mem_some_iff]
    have hnot : ¬ (a ≤ n ∧ test n = true) := Nat.find_min (h a) hn
    cases hv : test n <;> by_cases ha : a ≤ n <;>
      simp_all [afterBoolean]

/-- Increasing enumeration of all members of an unbounded Boolean set. -/
noncomputable def enumerateTrue (test : Nat → Bool) (h : UnboundedTrue test) : Nat → Nat
  | 0 => firstTrueAfter test h 0
  | n + 1 => firstTrueAfter test h (enumerateTrue test h n + 1)

theorem enumerateTrue_spec (test : Nat → Bool) (h : UnboundedTrue test) :
    ∀ n, test (enumerateTrue test h n) = true := by
  intro n
  cases n with
  | zero => exact (firstTrueAfter_spec test h 0).2
  | succ n => exact (firstTrueAfter_spec test h (enumerateTrue test h n + 1)).2

theorem enumerateTrue_strict (test : Nat → Bool) (h : UnboundedTrue test) :
    StrictMono (enumerateTrue test h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := (firstTrueAfter_spec test h (enumerateTrue test h n + 1)).1
  change enumerateTrue test h n < firstTrueAfter test h (enumerateTrue test h n + 1)
  omega

theorem enumerateTrue_computable (test : Nat → Bool) (h : UnboundedTrue test)
    (ht : Computable test) : Computable (enumerateTrue test h) := by
  let X := Nat × (Nat × Nat)
  have hnext : Computable (fun p : X => firstTrueAfter test h (p.2.2 + 1)) :=
    (firstTrueAfter_computable test h ht).comp (Computable.succ.comp (Computable.snd.comp Computable.snd))
  have hc := Computable.nat_rec (α := Nat) (σ := Nat) Computable.id
    (Computable.const (firstTrueAfter test h 0)) hnext.to₂
  have heq (n : Nat) : Nat.rec (firstTrueAfter test h 0)
      (fun _ x => firstTrueAfter test h (x + 1)) n = enumerateTrue test h n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [enumerateTrue, ih]
  exact hc.of_eq heq

/-- Every true code occurs in the increasing enumeration. -/
theorem enumerateTrue_surjective (test : Nat → Bool) (h : UnboundedTrue test)
    (n : Nat) (hn : test n = true) : ∃ k, enumerateTrue test h k = n := by
  have hi := enumerateTrue_strict test h
  let pred : Nat → Prop := fun k => n ≤ enumerateTrue test h k
  have hex : ∃ k, pred k := ⟨n, hi.id_le n⟩
  let k := Nat.find hex
  have hk : n ≤ enumerateTrue test h k := Nat.find_spec hex
  cases hk0 : k with
  | zero =>
    have hupper := firstTrueAfter_le test h 0 n (Nat.zero_le n) hn
    have hkn : n ≤ enumerateTrue test h 0 := by simpa [hk0] using hk
    refine ⟨0, ?_⟩
    change firstTrueAfter test h 0 = n
    change n ≤ firstTrueAfter test h 0 at hkn
    omega
  | succ j =>
    have hjlt : j < Nat.find hex := by change j < k; omega
    have hnot : ¬ pred j := Nat.find_min hex hjlt
    have hprev : enumerateTrue test h j < n := by dsimp [pred] at hnot; omega
    have hupper := firstTrueAfter_le test h (enumerateTrue test h j + 1) n (by omega) hn
    have hkn : n ≤ enumerateTrue test h (j + 1) := by simpa [hk0] using hk
    refine ⟨j + 1, ?_⟩
    change n ≤ firstTrueAfter test h (enumerateTrue test h j + 1) at hkn
    change firstTrueAfter test h (enumerateTrue test h j + 1) = n
    omega

noncomputable def enumerationMismatch (test : Nat → Bool) (h : UnboundedTrue test) (n k : Nat) : Bool :=
  !(decide (enumerateTrue test h k = n))

/-- A bounded inverse candidate. It is specified only for valid codes. -/
noncomputable def trueRank (test : Nat → Bool) (h : UnboundedTrue test) (n : Nat) : Nat :=
  boundedBadSearch (enumerationMismatch test h) n n

theorem trueRank_computable (test : Nat → Bool) (h : UnboundedTrue test)
    (ht : Computable test) : Computable (trueRank test h) := by
  have he := enumerateTrue_computable test h ht
  have heq : Computable (fun p : Nat × Nat => decide (enumerateTrue test h p.2 = p.1)) :=
    (Primrec.eq : PrimrecRel (fun a b : Nat => a = b)).decide.to_comp.comp
      (he.comp Computable.snd) Computable.fst
  have hb : Computable₂ (enumerationMismatch test h) := by
    have hh := Primrec.not.to_comp.comp heq
    exact hh.to₂
  have hr := boundedBadSearch_computable (enumerationMismatch test h) hb
  exact hr.comp (Computable.id.pair Computable.id)

theorem trueRank_valid (test : Nat → Bool) (h : UnboundedTrue test)
    (n : Nat) (hn : test n = true) : enumerateTrue test h (trueRank test h n) = n := by
  obtain ⟨k, hk⟩ := enumerateTrue_surjective test h n hn
  have hkn : k ≤ n := by
    have hh := (enumerateTrue_strict test h).id_le k
    simpa [hk] using hh
  have hs := (boundedBadSearch_spec (enumerationMismatch test h) n n).2
  have hbad : enumerationMismatch test h n (trueRank test h n) = false := by
    rcases hs with hf | hall
    · exact hf
    · have contra := hall k hkn
      simp [enumerationMismatch, hk] at contra
  simpa [enumerationMismatch] using hbad

theorem trueRank_enumerate (test : Nat → Bool) (h : UnboundedTrue test) (k : Nat) :
    trueRank test h (enumerateTrue test h k) = k := by
  apply (enumerateTrue_strict test h).injective
  exact trueRank_valid test h _ (enumerateTrue_spec test h k)

/-- Total syntax decoding used only together with canonical-code validation. -/
def closedCodeDecode (n : Nat) : Term :=
  (executableTermDecode n).getD (.var 0)

/-- Decide whether `n` is the canonical encoding of a closed lambda term. -/
def closedCodeTest (n : Nat) : Bool :=
  decide (executableTermEncode (closedCodeDecode n) = n) &&
    decide (requiredDepth (closedCodeDecode n) ≤ 0)

theorem closedCodeDecode_primrec : Primrec closedCodeDecode := by
  have h : Primrec (fun n : Nat => (Encodable.decode n : Option Term).getD (.var 0)) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const _)
  exact h.of_eq (fun n => by simp [closedCodeDecode, executableTermDecode_eq])

theorem closedCodeTest_primrec : Primrec closedCodeTest := by
  have henc : Primrec executableTermEncode :=
    Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)
  have hcanon : Primrec (fun n : Nat => decide (executableTermEncode (closedCodeDecode n) = n)) :=
    (Primrec.eq.comp (henc.comp closedCodeDecode_primrec) Primrec.id).decide
  have hclosed : Primrec (fun n : Nat => decide (requiredDepth (closedCodeDecode n) ≤ 0)) :=
    (Primrec.nat_le.comp (primrec_requiredDepth.comp closedCodeDecode_primrec) (Primrec.const 0)).decide
  exact Primrec.and.comp hcanon hclosed

theorem closedCodeTest_encode (t : Term) :
    closedCodeTest (Encodable.encode t) = true ↔ Scoped 0 t := by
  have hd : closedCodeDecode (Encodable.encode t) = t := by
    unfold closedCodeDecode
    rw [executableTermDecode_eq, Encodable.encodek]
    rfl
  simp only [closedCodeTest, hd, executableTermEncode_eq, decide_true, Bool.true_and, decide_eq_true_eq]
  exact (scoped_iff_requiredDepth_le t 0).symm

theorem closedCodeTest_exact (n : Nat) :
    closedCodeTest n = true ↔ ∃ t : Term, Encodable.encode t = n ∧ Scoped 0 t := by
  constructor
  · intro h
    have h' : executableTermEncode (closedCodeDecode n) = n ∧
        requiredDepth (closedCodeDecode n) ≤ 0 := by
      simpa only [closedCodeTest, Bool.and_eq_true, decide_eq_true_eq] using h
    exact ⟨closedCodeDecode n, by simpa only [executableTermEncode_eq] using h'.1,
      (scoped_iff_requiredDepth_le _ 0).2 h'.2⟩
  · rintro ⟨t, rfl, ht⟩
    exact (closedCodeTest_encode t).2 ht

theorem closedCodeTest_unbounded : UnboundedTrue closedCodeTest := by
  intro a
  let seed : Nat → Nat := fun n => Encodable.encode (church n)
  have hseed : Function.Injective seed := by
    intro m n h
    apply church_injective
    apply Encodable.encode_injective
    exact h
  obtain ⟨k, _, hk⟩ := injective_outside_prefix seed hseed (List.range a)
  have ha : a ≤ seed k := by
    have hn : ¬ seed k < a := by simpa only [List.mem_range] using hk
    omega
  exact ⟨seed k, ha, (closedCodeTest_exact (seed k)).2 ⟨church k, rfl, church_closed k⟩⟩

/-- The increasing enumeration and bounded rank of actual closed-term codes. -/
noncomputable def closedCodeEnum : Nat → Nat :=
  enumerateTrue closedCodeTest closedCodeTest_unbounded

noncomputable def closedCodeRank : Nat → Nat :=
  trueRank closedCodeTest closedCodeTest_unbounded

theorem closedCodeEnum_computable : Computable closedCodeEnum :=
  enumerateTrue_computable closedCodeTest closedCodeTest_unbounded closedCodeTest_primrec.to_comp

theorem closedCodeRank_computable : Computable closedCodeRank :=
  trueRank_computable closedCodeTest closedCodeTest_unbounded closedCodeTest_primrec.to_comp

theorem closedCodeEnum_closed (k : Nat) :
    ∃ t : Term, Encodable.encode t = closedCodeEnum k ∧ Scoped 0 t :=
  (closedCodeTest_exact _).1 (enumerateTrue_spec closedCodeTest closedCodeTest_unbounded k)

theorem closedCodeEnum_rank (n : Nat) (hn : closedCodeTest n = true) :
    closedCodeEnum (closedCodeRank n) = n :=
  trueRank_valid closedCodeTest closedCodeTest_unbounded n hn

theorem closedCodeRank_enum (k : Nat) : closedCodeRank (closedCodeEnum k) = k :=
  trueRank_enumerate closedCodeTest closedCodeTest_unbounded k


theorem closedCodeDecode_encode (t : Term) :
    closedCodeDecode (Encodable.encode t) = t := by
  unfold closedCodeDecode
  rw [executableTermDecode_eq, Encodable.encodek]
  rfl

theorem closedCodeEnum_code (k : Nat) :
    Encodable.encode (closedCodeDecode (closedCodeEnum k)) = closedCodeEnum k := by
  obtain ⟨t, ht, _⟩ := closedCodeEnum_closed k
  rw [← ht, closedCodeDecode_encode]

theorem closedCodeEnum_decode_closed (k : Nat) : Scoped 0 (closedCodeDecode (closedCodeEnum k)) := by
  obtain ⟨t, ht, hc⟩ := closedCodeEnum_closed k
  simpa [← ht, closedCodeDecode_encode] using hc

/-- Zero-result observation indexed by the computable enumeration of all
closed terms. Every index denotes a closed term, including negative instances. -/
noncomputable def indexedClosedZero (n : Nat) : Prop :=
  closedNumeralAtZero 0 (closedCodeDecode (closedCodeEnum n))

theorem indexedClosedZero_re : REPred indexedClosedZero := by
  have hd : Computable (fun n => closedCodeDecode (closedCodeEnum n)) :=
    closedCodeDecode_primrec.to_comp.comp closedCodeEnum_computable
  exact (closedNumeralAtZero_re 0).comp hd

theorem indexedClosedZero_rank (t : Term) (ht : Scoped 0 t) :
    indexedClosedZero (closedCodeRank (Encodable.encode t)) ↔ closedNumeralAtZero 0 t := by
  have hv : closedCodeTest (Encodable.encode t) = true := (closedCodeTest_encode t).2 ht
  change closedNumeralAtZero 0 (closedCodeDecode (closedCodeEnum (closedCodeRank (Encodable.encode t)))) ↔ _
  rw [closedCodeEnum_rank _ hv, closedCodeDecode_encode]

/-- The indexed closed-term language remains one-one hard, using a compiler
whose outputs are closed for every input, not only positive inputs. -/
theorem indexedClosedZero_oneOne_complete (p : Nat → Prop) (hp : REPred p) :
    ∃ r : Nat → Nat, Computable r ∧ Function.Injective r ∧
      ∀ n, p n ↔ indexedClosedZero (r n) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hdom (n : Nat) : (Nat.Partrec.Code.eval c (Encodable.encode n)).Dom ↔ p n := by
    rw [hc]
    simp [Part.assert]
  let t : Nat → Term := fun n => oneOneHaltingToClosedZero (c, Encodable.encode n)
  have htc : Computable t := oneOneHaltingToClosedZero_primrec.to_comp.comp
    ((Computable.const c).pair Computable.encode)
  have hclosed (n : Nat) : Scoped 0 (t n) := (oneOneHaltingToClosedZero_correct (c, Encodable.encode n)).1
  let r : Nat → Nat := fun n => closedCodeRank (Encodable.encode (t n))
  have hrc : Computable r := closedCodeRank_computable.comp (Computable.encode.comp htc)
  have hri : Function.Injective r := by
    intro a b hab
    have ha : closedCodeTest (Encodable.encode (t a)) = true := (closedCodeTest_encode _).2 (hclosed a)
    have hb : closedCodeTest (Encodable.encode (t b)) = true := (closedCodeTest_encode _).2 (hclosed b)
    have he := congrArg closedCodeEnum hab
    change closedCodeEnum (closedCodeRank (Encodable.encode (t a))) =
      closedCodeEnum (closedCodeRank (Encodable.encode (t b))) at he
    rw [closedCodeEnum_rank _ ha, closedCodeEnum_rank _ hb] at he
    have ht : t a = t b := Encodable.encode_injective he
    have hpairs := oneOneHaltingToClosedZero_injective ht
    exact Encodable.encode_injective (congrArg Prod.snd hpairs)
  refine ⟨r, hrc, hri, ?_⟩
  intro n
  exact (hdom n).symm.trans ((oneOneHaltingToClosedZero_correct (c, Encodable.encode n)).2.symm.trans
    (indexedClosedZero_rank (t n) (hclosed n)).symm)

/-- Every recursive code-input pair corresponds bijectively to a closed
lambda term, with both maps computable and exact halting/zero correspondence.
The inverse identity is asserted for all closed terms. -/
theorem codeInput_closedTerm_bijection :
    ∃ F : Nat.Partrec.Code × Nat → Term, ∃ G : Term → Nat.Partrec.Code × Nat,
      Computable F ∧ Computable G ∧
      (∀ p, Scoped 0 (F p)) ∧
      (∀ p, G (F p) = p) ∧
      (∀ t, Scoped 0 t → F (G t) = t) ∧
      (∀ p, (Nat.Partrec.Code.eval p.1 p.2).Dom ↔ closedNumeralAtZero 0 (F p)) := by
  obtain ⟨f, hf, hfi, hfr⟩ := indexedClosedZero_oneOne_complete codedHalting codedHalting_re
  obtain ⟨g, hg, hgi, hgr⟩ := codedHalting_oneOne_complete indexedClosedZero indexedClosedZero_re
  obtain ⟨e, he, hei, hrel⟩ := computable_permutation_of_oneOneEquiv codedHalting indexedClosedZero
    ⟨⟨f, hf, hfi, hfr⟩, ⟨g, hg.to_comp, hgi, hgr⟩⟩
  let F : Nat.Partrec.Code × Nat → Term := fun p =>
    closedCodeDecode (closedCodeEnum (e (Encodable.encode p)))
  let G : Term → Nat.Partrec.Code × Nat := fun t =>
    Denumerable.ofNat _ (e.symm (closedCodeRank (Encodable.encode t)))
  have hF : Computable F := closedCodeDecode_primrec.to_comp.comp
    (closedCodeEnum_computable.comp (he.comp Computable.encode))
  have hG : Computable G := (Computable.ofNat (Nat.Partrec.Code × Nat)).comp
    (hei.comp (closedCodeRank_computable.comp Computable.encode))
  refine ⟨F, G, hF, hG, ?_, ?_, ?_, ?_⟩
  · intro p
    exact closedCodeEnum_decode_closed (e (Encodable.encode p))
  · intro p
    change Denumerable.ofNat _ (e.symm (closedCodeRank
      (Encodable.encode (closedCodeDecode (closedCodeEnum (e (Encodable.encode p))))))) = p
    rw [closedCodeEnum_code, closedCodeRank_enum, e.symm_apply_apply, Denumerable.ofNat_encode]
  · intro t ht
    have hvalid : closedCodeTest (Encodable.encode t) = true := (closedCodeTest_encode t).2 ht
    change closedCodeDecode (closedCodeEnum (e (Encodable.encode
      (Denumerable.ofNat (Nat.Partrec.Code × Nat) (e.symm (closedCodeRank (Encodable.encode t))))))) = t
    rw [Denumerable.encode_ofNat, e.apply_symm_apply, closedCodeEnum_rank _ hvalid, closedCodeDecode_encode]
  · intro p
    change (Nat.Partrec.Code.eval p.1 p.2).Dom ↔ indexedClosedZero (e (Encodable.encode p))
    exact (codedHalting_encode p).symm.trans (hrel (Encodable.encode p))

#print axioms closedCodeEnum_code
#print axioms indexedClosedZero_oneOne_complete
#print axioms codeInput_closedTerm_bijection

end LambdaTuring
