/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

Numerical graph inclusion and equivalence for closed untyped lambda terms.
-/
module
public import LambdaTuring.TotalityBounded
@[expose] public section
namespace LambdaTuring

/-- Both closed programs have exactly the same partial numerical function. -/
def ClosedNumericalEquiv (p : Term × Term) : Prop :=
  Scoped 0 p.1 ∧ Scoped 0 p.2 ∧ numericalValue p.1 = numericalValue p.2

/-- Every numerical result of the first closed program also belongs to the second. -/
def ClosedNumericalRefines (p : Term × Term) : Prop :=
  Scoped 0 p.1 ∧ Scoped 0 p.2 ∧
    ∀ n v, v ∈ numericalValue p.1 n → v ∈ numericalValue p.2 n

theorem closedNumericalEquiv_iff_mutual_refinement (p : Term × Term) :
    ClosedNumericalEquiv p ↔
      ClosedNumericalRefines p ∧ ClosedNumericalRefines (p.2, p.1) := by
  constructor
  · rintro ⟨hfirst, hsecond, he⟩
    constructor
    · refine ⟨hfirst, hsecond, ?_⟩
      intro n v hv
      simpa only [he] using hv
    · refine ⟨hsecond, hfirst, ?_⟩
      intro n v hv
      simpa only [← he] using hv
  · rintro ⟨hforward, hbackward⟩
    refine ⟨hforward.1, hforward.2.1, ?_⟩
    funext n
    apply Part.ext
    intro v
    exact ⟨hforward.2.2 n v, hbackward.2.2 n v⟩

/-- Compile a code to its strict zero-valued restriction and the constant-zero program. -/
def totalityEquivPair (c : Nat.Partrec.Code) : Term × Term :=
  (compileLambdaTotal (.comp .zero c), compileLambdaTotal .zero)

theorem totalityEquivPair_primrec : Primrec totalityEquivPair := by
  have hcomp : Primrec (fun c : Nat.Partrec.Code => Nat.Partrec.Code.comp .zero c) :=
    Nat.Partrec.Code.primrec₂_comp.comp (Primrec.const _) Primrec.id
  exact (primrec_compileLambdaTotal.comp hcomp).pair (Primrec.const _)

theorem part_bind_zero_iff (p : Part Nat) :
    p.Dom ↔ p.bind (fun _ => Part.some 0) = Part.some 0 := by
  constructor
  · intro hp
    apply Part.eq_some_iff.mpr
    exact Part.mem_bind_iff.mpr ⟨p.get hp, Part.get_mem hp, by simp⟩
  · intro hp
    have hm : 0 ∈ p.bind (fun _ => Part.some 0) := Part.eq_some_iff.mp hp
    obtain ⟨v, hv, _⟩ := Part.mem_bind_iff.mp hm
    exact hv.1

theorem totalityEquivPair_correct (c : Nat.Partrec.Code) :
    CodeTotal c ↔ ClosedNumericalEquiv (totalityEquivPair c) := by
  have hc (n : Nat) : Nat.Partrec.Code.eval (.comp .zero c) n =
      (Nat.Partrec.Code.eval c n).bind (fun _ => Part.some 0) := rfl
  have hz (n : Nat) : Nat.Partrec.Code.eval .zero n = Part.some 0 := rfl
  constructor
  · intro ht
    refine ⟨(compileLambdaTotal_sound _).1, (compileLambdaTotal_sound _).1, ?_⟩
    funext n
    change numericalValue (compileLambdaTotal (.comp .zero c)) n =
      numericalValue (compileLambdaTotal .zero) n
    rw [(compileLambdaTotal_sound _).2 n, (compileLambdaTotal_sound _).2 n, hc n, hz n]
    exact (part_bind_zero_iff _).mp (ht n)
  · intro he n
    have hn := congrFun he.2.2 n
    change numericalValue (compileLambdaTotal (.comp .zero c)) n =
      numericalValue (compileLambdaTotal .zero) n at hn
    rw [(compileLambdaTotal_sound _).2 n, (compileLambdaTotal_sound _).2 n, hc n, hz n] at hn
    exact (part_bind_zero_iff _).mpr hn

theorem codeTotal_manyOne_closedNumericalEquiv :
    ManyOneReducible CodeTotal ClosedNumericalEquiv :=
  ⟨totalityEquivPair, totalityEquivPair_primrec.to_comp, totalityEquivPair_correct⟩

/-- Reverse the zero-valued pair so that inclusion forces its partial side to be total. -/
def totalityRefinementPair (c : Nat.Partrec.Code) : Term × Term :=
  (compileLambdaTotal .zero, compileLambdaTotal (.comp .zero c))

/-- The varying side of both hardness reductions can produce only zero. -/
theorem totalityPair_varying_output_zero (c : Nat.Partrec.Code) (n v : Nat)
    (hv : v ∈ numericalValue (compileLambdaTotal (.comp .zero c)) n) : v = 0 := by
  rw [(compileLambdaTotal_sound (.comp .zero c)).2 n] at hv
  change v ∈ (Nat.Partrec.Code.eval c n).bind (fun _ => Part.some 0) at hv
  obtain ⟨_, _, hout⟩ := Part.mem_bind_iff.mp hv
  simpa using hout

/-- The fixed side of both reductions denotes the total constant-zero function. -/
theorem totalityPair_fixed_zero (n : Nat) :
    numericalValue (compileLambdaTotal .zero) n = Part.some 0 := by
  rw [(compileLambdaTotal_sound Nat.Partrec.Code.zero).2 n]
  rfl

theorem totalityRefinementPair_primrec : Primrec totalityRefinementPair := by
  have hcomp : Primrec (fun c : Nat.Partrec.Code => Nat.Partrec.Code.comp .zero c) :=
    Nat.Partrec.Code.primrec₂_comp.comp (Primrec.const _) Primrec.id
  exact (Primrec.const _).pair (primrec_compileLambdaTotal.comp hcomp)

theorem totalityRefinementPair_correct (c : Nat.Partrec.Code) :
    CodeTotal c ↔ ClosedNumericalRefines (totalityRefinementPair c) := by
  constructor
  · intro ht
    have he := (totalityEquivPair_correct c).mp ht
    refine ⟨he.2.1, he.1, ?_⟩
    intro n v hv
    change v ∈ numericalValue (compileLambdaTotal .zero) n at hv
    change v ∈ numericalValue (compileLambdaTotal (.comp .zero c)) n
    have he' : numericalValue (compileLambdaTotal (.comp .zero c)) =
        numericalValue (compileLambdaTotal .zero) := he.2.2
    rw [← he'] at hv
    exact hv
  · intro hr n
    have hz : 0 ∈ numericalValue (compileLambdaTotal .zero) n := by
      rw [(compileLambdaTotal_sound Nat.Partrec.Code.zero).2 n]
      change 0 ∈ Part.some 0
      simp
    have hm : 0 ∈ numericalValue (compileLambdaTotal (.comp .zero c)) n := hr.2.2 n 0 hz
    rw [(compileLambdaTotal_sound (.comp .zero c)).2 n] at hm
    change 0 ∈ (Nat.Partrec.Code.eval c n).bind (fun _ => Part.some 0) at hm
    obtain ⟨v, hv, _⟩ := Part.mem_bind_iff.mp hm
    exact hv.1

theorem codeTotal_manyOne_closedNumericalRefines :
    ManyOneReducible CodeTotal ClosedNumericalRefines :=
  ⟨totalityRefinementPair, totalityRefinementPair_primrec.to_comp,
    totalityRefinementPair_correct⟩

/-- Hardness of refinement even against one fixed constant-zero program. -/
theorem restrictedRefinementReduction :
    ∃ f : Nat.Partrec.Code → Term × Term, Primrec f ∧
      (∀ c, CodeTotal c ↔ ClosedNumericalRefines (f c)) ∧
      (∃ t, (∀ c, (f c).1 = t) ∧
        ∀ n, numericalValue t n = Part.some 0) ∧
      ∀ c n v, v ∈ numericalValue (f c).2 n → v = 0 := by
  refine ⟨totalityRefinementPair, totalityRefinementPair_primrec,
    totalityRefinementPair_correct, ?_, ?_⟩
  · exact ⟨compileLambdaTotal .zero, fun _ => rfl, totalityPair_fixed_zero⟩
  · exact totalityPair_varying_output_zero

/-- Hardness of equivalence with the fixed zero program in the second position. -/
theorem restrictedEquivalenceReduction :
    ∃ f : Nat.Partrec.Code → Term × Term, Primrec f ∧
      (∀ c, CodeTotal c ↔ ClosedNumericalEquiv (f c)) ∧
      (∃ t, (∀ c, (f c).2 = t) ∧
        ∀ n, numericalValue t n = Part.some 0) ∧
      ∀ c n v, v ∈ numericalValue (f c).1 n → v = 0 := by
  refine ⟨totalityEquivPair, totalityEquivPair_primrec,
    totalityEquivPair_correct, ?_, ?_⟩
  · exact ⟨compileLambdaTotal .zero, fun _ => rfl, totalityPair_fixed_zero⟩
  · exact totalityPair_varying_output_zero

theorem closedNumericalRefines_normalForm_manyOne
    (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    ManyOneReducible (fun a => ∀ n, ∃ k, R ((a,n),k) = true) ClosedNumericalRefines :=
  ((closedNumericalTotal_normalForm_manyOne R hR).trans
    closedNumericalTotal_manyOne_codeTotal).trans codeTotal_manyOne_closedNumericalRefines

/-- Every computable universal-existential normal form reduces to program equivalence. -/
theorem closedNumericalEquiv_normalForm_manyOne
    (R : (Nat × Nat) × Nat → Bool) (hR : Computable R) :
    ManyOneReducible (fun a => ∀ n, ∃ k, R ((a,n),k) = true) ClosedNumericalEquiv :=
  ((closedNumericalTotal_normalForm_manyOne R hR).trans
    closedNumericalTotal_manyOne_codeTotal).trans codeTotal_manyOne_closedNumericalEquiv

abbrev InclusionInput := (((Nat.Partrec.Code × Nat.Partrec.Code) × Nat) × Nat) × Nat

/-- The first evaluator has not yet returned, or the second has returned the same value. -/
def boundedInclusionWitness (p : InclusionInput) : Bool :=
  let a := Nat.Partrec.Code.evaln p.1.2 p.1.1.1.1 p.1.1.2
  let b := Nat.Partrec.Code.evaln p.2 p.1.1.1.2 p.1.1.2
  !a.isSome || decide (a = b)

theorem boundedInclusionWitness_primrec : Primrec boundedInclusionWitness := by
  have hpair : Primrec (fun p : InclusionInput => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun p : InclusionInput => p.1.1.1.1) := Primrec.fst.comp hpair
  have hd : Primrec (fun p : InclusionInput => p.1.1.1.2) := Primrec.snd.comp hpair
  have hn : Primrec (fun p : InclusionInput => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec (fun p : InclusionInput => p.1.2) := Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun p : InclusionInput => p.2) := Primrec.snd
  have ha : Primrec (fun p : InclusionInput =>
      Nat.Partrec.Code.evaln p.1.2 p.1.1.1.1 p.1.1.2) :=
    Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hc).pair hn)
  have hb : Primrec (fun p : InclusionInput =>
      Nat.Partrec.Code.evaln p.2 p.1.1.1.2 p.1.1.2) :=
    Nat.Partrec.Code.primrec_evaln.comp ((hj.pair hd).pair hn)
  exact Primrec.or.comp (Primrec.not.comp (Primrec.option_isSome.comp ha))
    (Primrec.eq.decide.comp ha hb)

/-- A directional finite-stage characterization of inclusion of partial graphs. -/
theorem boundedInclusion_iff (c d : Nat.Partrec.Code) (n : Nat) :
    (∀ v, v ∈ Nat.Partrec.Code.eval c n → v ∈ Nat.Partrec.Code.eval d n) ↔
      ∀ k, ∃ j, boundedInclusionWitness ((((c, d), n), k), j) = true := by
  constructor
  · intro h k
    cases hc : Nat.Partrec.Code.evaln k c n with
    | none =>
      exact ⟨0, by simp [boundedInclusionWitness, hc]⟩
    | some v =>
      have hv : v ∈ Nat.Partrec.Code.eval c n :=
        Nat.Partrec.Code.evaln_complete.mpr ⟨k, by simp [hc]⟩
      obtain ⟨j, hj⟩ := Nat.Partrec.Code.evaln_complete.mp (h v hv)
      have hsecond : Nat.Partrec.Code.evaln j d n = some v := by
        simpa only [Option.mem_def] using hj
      exact ⟨j, by simp [boundedInclusionWitness, hc, hsecond]⟩
  · intro h v hv
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    have hfirst : Nat.Partrec.Code.evaln k c n = some v := by
      simpa only [Option.mem_def] using hk
    obtain ⟨j, hj⟩ := h k
    have hsecond : Nat.Partrec.Code.evaln j d n = some v := by
      simp only [boundedInclusionWitness, hfirst, Option.isSome_some, Bool.not_true,
        Bool.false_or, decide_eq_true_eq] at hj
      exact hj.symm
    exact Nat.Partrec.Code.evaln_complete.mpr ⟨j, by simp [hsecond]⟩

/-- Equality of partial functions is mutual inclusion, with both directions bounded. -/
theorem codeEquiv_iff_bounded (c d : Nat.Partrec.Code) :
    Nat.Partrec.Code.eval c = Nat.Partrec.Code.eval d ↔
      (∀ n k, ∃ j, boundedInclusionWitness ((((c, d), n), k), j) = true) ∧
      (∀ n k, ∃ j, boundedInclusionWitness ((((d, c), n), k), j) = true) := by
  constructor
  · intro he
    constructor
    · intro n
      apply (boundedInclusion_iff c d n).mp
      intro v hv
      simpa only [he] using hv
    · intro n
      apply (boundedInclusion_iff d c n).mp
      intro v hv
      simpa only [← he] using hv
  · rintro ⟨hcd, hdc⟩
    funext n
    apply Part.ext
    intro v
    exact ⟨(boundedInclusion_iff c d n).mpr (hcd n) v,
      (boundedInclusion_iff d c n).mpr (hdc n) v⟩

/-- Inclusion between the graphs of two partial recursive codes. -/
def CodeRefines (p : Nat.Partrec.Code × Nat.Partrec.Code) : Prop :=
  ∀ n v, v ∈ Nat.Partrec.Code.eval p.1 n → v ∈ Nat.Partrec.Code.eval p.2 n

/-- Reject an open input by mapping it to a fixed non-inclusion. -/
def closedPairCodes (u : Nat.Partrec.Code) (p : Term × Term) :
    Nat.Partrec.Code × Nat.Partrec.Code :=
  if requiredDepth p.1 ≤ 0 ∧ requiredDepth p.2 ≤ 0 then
    (Nat.Partrec.Code.curry u (executableTermEncode p.1),
      Nat.Partrec.Code.curry u (executableTermEncode p.2))
  else (.zero, bottomCode)

theorem closedPairCodes_primrec (u : Nat.Partrec.Code) : Primrec (closedPairCodes u) := by
  have hleft : Primrec (fun p : Term × Term => requiredDepth p.1) :=
    primrec_requiredDepth.comp Primrec.fst
  have hright : Primrec (fun p : Term × Term => requiredDepth p.2) :=
    primrec_requiredDepth.comp Primrec.snd
  have hguard : PrimrecPred (fun p : Term × Term =>
      requiredDepth p.1 ≤ 0 ∧ requiredDepth p.2 ≤ 0) :=
    (Primrec.nat_le.comp hleft (Primrec.const 0)).and
      (Primrec.nat_le.comp hright (Primrec.const 0))
  have henc : Primrec executableTermEncode :=
    Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)
  have hcomp : Primrec (fun t : Term => Nat.Partrec.Code.curry u (executableTermEncode t)) :=
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) henc
  unfold closedPairCodes
  exact Primrec.ite hguard ((hcomp.comp Primrec.fst).pair (hcomp.comp Primrec.snd))
    (Primrec.const _)

theorem zero_not_refines_bottom : ¬ CodeRefines (.zero, bottomCode) := by
  intro h
  have hz : 0 ∈ Nat.Partrec.Code.eval .zero 0 := by
    change 0 ∈ Part.some 0
    simp
  have hb := h 0 0 hz
  change 0 ∈ Nat.Partrec.Code.eval bottomCode 0 at hb
  rw [bottomCode_eval] at hb
  exact hb.1

theorem closedPairCodes_correct (u : Nat.Partrec.Code) (hu : UniformLambdaCode u)
    (p : Term × Term) : ClosedNumericalRefines p ↔ CodeRefines (closedPairCodes u p) := by
  by_cases h : requiredDepth p.1 ≤ 0 ∧ requiredDepth p.2 ≤ 0
  · have hs₁ : Scoped 0 p.1 := (scoped_iff_requiredDepth_le p.1 0).mpr h.1
    have hs₂ : Scoped 0 p.2 := (scoped_iff_requiredDepth_le p.2 0).mpr h.2
    have he₁ : Nat.Partrec.Code.eval (Nat.Partrec.Code.curry u (executableTermEncode p.1)) =
        numericalValue p.1 := by
      funext n
      rw [Nat.Partrec.Code.eval_curry, hu]
    have he₂ : Nat.Partrec.Code.eval (Nat.Partrec.Code.curry u (executableTermEncode p.2)) =
        numericalValue p.2 := by
      funext n
      rw [Nat.Partrec.Code.eval_curry, hu]
    simp only [closedPairCodes, h]
    change (Scoped 0 p.1 ∧ Scoped 0 p.2 ∧ ∀ n v,
      v ∈ numericalValue p.1 n → v ∈ numericalValue p.2 n) ↔
        ∀ n v, v ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.curry u (executableTermEncode p.1)) n →
          v ∈ Nat.Partrec.Code.eval (Nat.Partrec.Code.curry u (executableTermEncode p.2)) n
    rw [he₁, he₂]
    simp [hs₁, hs₂]
  · simp only [closedPairCodes, h, ↓reduceIte]
    constructor
    · intro hp
      exfalso
      exact h ⟨(scoped_iff_requiredDepth_le p.1 0).mp hp.1,
        (scoped_iff_requiredDepth_le p.2 0).mp hp.2.1⟩
    · intro hp
      exact False.elim (zero_not_refines_bottom hp)

theorem closedNumericalRefines_has_bounded_form :
    ∃ f : Term × Term → Nat.Partrec.Code × Nat.Partrec.Code, Primrec f ∧ ∀ p,
      (ClosedNumericalRefines p ↔ ∀ n k, ∃ j,
        boundedInclusionWitness ((((f p), n), k), j) = true) := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  refine ⟨closedPairCodes u, closedPairCodes_primrec u, ?_⟩
  intro p
  rw [closedPairCodes_correct u hu]
  change (∀ n v, v ∈ Nat.Partrec.Code.eval (closedPairCodes u p).1 n →
    v ∈ Nat.Partrec.Code.eval (closedPairCodes u p).2 n) ↔ _
  exact forall_congr' fun n => boundedInclusion_iff _ _ n

abbrev DualCodePair := (Nat.Partrec.Code × Nat.Partrec.Code) ×
  (Nat.Partrec.Code × Nat.Partrec.Code)
abbrev BothInput := (DualCodePair × Nat) × Nat

/-- Decode a direction and a pair of bounded-evaluation inputs from one index. -/
def boundedBothWitness (p : BothInput) : Bool :=
  let direction := (Nat.unpair p.1.2).1
  let nk := Nat.unpair (Nat.unpair p.1.2).2
  if direction = 0 then
    boundedInclusionWitness (((p.1.1.1, nk.1), nk.2), p.2)
  else
    boundedInclusionWitness (((p.1.1.2, nk.1), nk.2), p.2)

theorem boundedBothWitness_primrec : Primrec boundedBothWitness := by
  have hc : Primrec (fun p : BothInput => p.1.1) := Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : BothInput => Nat.unpair p.1.2) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)
  have hnk : Primrec (fun p : BothInput => Nat.unpair (Nat.unpair p.1.2).2) :=
    Primrec.unpair.comp (Primrec.snd.comp hi)
  have hn : Primrec (fun p : BothInput => (Nat.unpair (Nat.unpair p.1.2).2).1) :=
    Primrec.fst.comp hnk
  have hk : Primrec (fun p : BothInput => (Nat.unpair (Nat.unpair p.1.2).2).2) :=
    Primrec.snd.comp hnk
  have hj : Primrec (fun p : BothInput => p.2) := Primrec.snd
  have hl := boundedInclusionWitness_primrec.comp
    ((((Primrec.fst.comp hc).pair hn).pair hk).pair hj)
  have hr := boundedInclusionWitness_primrec.comp
    ((((Primrec.snd.comp hc).pair hn).pair hk).pair hj)
  unfold boundedBothWitness
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hi) (Primrec.const 0)) hl hr

def closedDualCodes (u : Nat.Partrec.Code) (p : Term × Term) : DualCodePair :=
  (closedPairCodes u p, closedPairCodes u (p.2, p.1))

theorem closedDualCodes_primrec (u : Nat.Partrec.Code) : Primrec (closedDualCodes u) :=
  (closedPairCodes_primrec u).pair
    ((closedPairCodes_primrec u).comp (Primrec.snd.pair Primrec.fst))

def closedRepeatedCodes (u : Nat.Partrec.Code) (p : Term × Term) : DualCodePair :=
  (closedPairCodes u p, closedPairCodes u p)

theorem closedRepeatedCodes_primrec (u : Nat.Partrec.Code) : Primrec (closedRepeatedCodes u) :=
  (closedPairCodes_primrec u).pair (closedPairCodes_primrec u)

theorem closedNumericalRefines_has_normal_form :
    ∃ f : Term × Term → DualCodePair, Primrec f ∧ ∀ p,
      (ClosedNumericalRefines p ↔ ∀ i, ∃ j, boundedBothWitness ((f p, i), j) = true) := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  refine ⟨closedRepeatedCodes u, closedRepeatedCodes_primrec u, ?_⟩
  intro p
  rw [closedPairCodes_correct u hu]
  constructor
  · intro h i
    let nk := Nat.unpair (Nat.unpair i).2
    obtain ⟨j, hj⟩ := (boundedInclusion_iff _ _ nk.1).mp (h nk.1) nk.2
    refine ⟨j, ?_⟩
    dsimp [boundedBothWitness, closedRepeatedCodes]
    split <;> exact hj
  · intro h n v hv
    have hb : ∀ k, ∃ j, boundedInclusionWitness
        ((((closedPairCodes u p), n), k), j) = true := by
      intro k
      obtain ⟨j, hj⟩ := h (Nat.pair 0 (Nat.pair n k))
      exact ⟨j, by simpa [boundedBothWitness, closedRepeatedCodes] using hj⟩
    exact (boundedInclusion_iff _ _ n).mpr hb v hv

theorem closedNumericalEquiv_has_bounded_form :
    ∃ f : Term × Term → DualCodePair, Primrec f ∧ ∀ p,
      (ClosedNumericalEquiv p ↔ ∀ i, ∃ j, boundedBothWitness ((f p, i), j) = true) := by
  obtain ⟨u, hu⟩ := uniformLambdaCode_exists
  refine ⟨closedDualCodes u, closedDualCodes_primrec u, ?_⟩
  intro p
  rw [closedNumericalEquiv_iff_mutual_refinement,
    closedPairCodes_correct u hu, closedPairCodes_correct u hu]
  constructor
  · rintro ⟨hl, hr⟩ i
    let nk := Nat.unpair (Nat.unpair i).2
    by_cases hd : (Nat.unpair i).1 = 0
    · obtain ⟨j, hj⟩ := (boundedInclusion_iff _ _ nk.1).mp (hl nk.1) nk.2
      exact ⟨j, by simpa [boundedBothWitness, closedDualCodes, nk, hd] using hj⟩
    · obtain ⟨j, hj⟩ := (boundedInclusion_iff _ _ nk.1).mp (hr nk.1) nk.2
      exact ⟨j, by simpa [boundedBothWitness, closedDualCodes, nk, hd] using hj⟩
  · intro h
    constructor
    · intro n v hv
      have hb : ∀ k, ∃ j, boundedInclusionWitness
          ((((closedPairCodes u p), n), k), j) = true := by
        intro k
        obtain ⟨j, hj⟩ := h (Nat.pair 0 (Nat.pair n k))
        exact ⟨j, by simpa [boundedBothWitness, closedDualCodes] using hj⟩
      exact (boundedInclusion_iff _ _ n).mpr hb v hv
    · intro n v hv
      have hb : ∀ k, ∃ j, boundedInclusionWitness
          ((((closedPairCodes u (p.2, p.1)), n), k), j) = true := by
        intro k
        obtain ⟨j, hj⟩ := h (Nat.pair 1 (Nat.pair n k))
        exact ⟨j, by simpa [boundedBothWitness, closedDualCodes] using hj⟩
      exact (boundedInclusion_iff _ _ n).mpr hb v hv

/-- Classical Π₂ normal-form completeness for numerical graph inclusion. -/
theorem closedNumericalRefines_normalForm_complete :
    Primrec boundedBothWitness ∧
    (∃ f : Term × Term → DualCodePair, Primrec f ∧ ∀ p,
      (ClosedNumericalRefines p ↔ ∀ i, ∃ j, boundedBothWitness ((f p, i), j) = true)) ∧
    ∀ R : (Nat × Nat) × Nat → Bool, Computable R →
      ManyOneReducible (fun a => ∀ n, ∃ k, R ((a,n),k) = true) ClosedNumericalRefines :=
  ⟨boundedBothWitness_primrec, closedNumericalRefines_has_normal_form,
    closedNumericalRefines_normalForm_manyOne⟩

/-- Classical Π₂ normal-form completeness for numerical program equivalence. -/
theorem closedNumericalEquiv_normalForm_complete :
    Primrec boundedBothWitness ∧
    (∃ f : Term × Term → DualCodePair, Primrec f ∧ ∀ p,
      (ClosedNumericalEquiv p ↔ ∀ i, ∃ j, boundedBothWitness ((f p, i), j) = true)) ∧
    ∀ R : (Nat × Nat) × Nat → Bool, Computable R →
      ManyOneReducible (fun a => ∀ n, ∃ k, R ((a,n),k) = true) ClosedNumericalEquiv :=
  ⟨boundedBothWitness_primrec, closedNumericalEquiv_has_bounded_form,
    closedNumericalEquiv_normalForm_manyOne⟩

#print axioms closedNumericalRefines_normalForm_complete
#print axioms closedNumericalEquiv_normalForm_complete
#print axioms totalityPair_varying_output_zero
#print axioms totalityPair_fixed_zero

end LambdaTuring
