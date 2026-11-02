/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

Working increment: effective finite numerical graph realizations.
-/
module

public import LambdaTuring.TotalityBounded
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LambdaTuring

/-- `none` is an unconstrained input, rather than a claim of divergence. -/
abbrev FiniteObservation := List (Option Nat)

def finiteLookup (p : FiniteObservation × Nat) : Option Nat :=
  (p.1[p.2]?).getD none

def finiteValue (table : FiniteObservation) (n : Nat) : Part Nat :=
  (finiteLookup (table, n) : Part Nat)

theorem finiteLookup_primrec : Primrec finiteLookup := by
  exact Primrec.option_getD.comp
    (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const none)

theorem finiteValue_partrec :
    Partrec (fun p : FiniteObservation × Nat => finiteValue p.1 p.2) := by
  exact finiteLookup_primrec.to_comp.ofOption

theorem finiteValue_mem_iff (table : FiniteObservation) (n y : Nat) :
    y ∈ finiteValue table n ↔ table[n]? = some (some y) := by
  cases h : table[n]? with
  | none => simp [finiteValue, finiteLookup, h]
  | some v => cases v <;> simp [finiteValue, finiteLookup, h, eq_comm]

def ObservationIncluded (table : FiniteObservation) (f : Nat →. Nat) : Prop :=
  ∀ n y, table[n]? = some (some y) → y ∈ f n

theorem observationIncluded_iff (table : FiniteObservation) (f : Nat →. Nat) :
    ObservationIncluded table f ↔ ∀ n y, y ∈ finiteValue table n → y ∈ f n := by
  simp only [ObservationIncluded, finiteValue_mem_iff]

/-- The finite prefix of a partial numerical graph, used only in proofs.
Computing this particular snapshot from an arbitrary partial function is not
claimed. -/
noncomputable def graphPrefix (f : Nat →. Nat) (b : Nat) : FiniteObservation := by
  classical
  exact (List.range b).map fun n => if h : (f n).Dom then some ((f n).get h) else none

theorem graphPrefix_mem_iff (f : Nat →. Nat) (b n y : Nat) :
    y ∈ finiteValue (graphPrefix f b) n ↔ n < b ∧ y ∈ f n := by
  classical
  rw [finiteValue_mem_iff]
  by_cases hn : n < b
  · by_cases hd : (f n).Dom
    · have hm := Part.get_mem hd
      have heq : (f n).get hd = y ↔ y ∈ f n :=
        ⟨fun h => h ▸ hm, fun hy => Part.mem_unique hm hy⟩
      simpa [graphPrefix, hn, hd] using heq
    · have hv : y ∉ f n := fun hy => hd ((Part.dom_iff_mem).2 ⟨y, hy⟩)
      simp [graphPrefix, hn, hd, hv]
  · simp [graphPrefix, hn]

theorem boundedGraph_realized (f : Nat →. Nat) (b : Nat)
    (hb : ∀ n, b ≤ n → ¬ (f n).Dom) : finiteValue (graphPrefix f b) = f := by
  funext n
  apply Part.ext
  intro y
  rw [graphPrefix_mem_iff]
  constructor
  · exact And.right
  · intro hy
    have hn : n < b := by
      by_contra h
      exact hb n (Nat.le_of_not_gt h) ((Part.dom_iff_mem).2 ⟨y, hy⟩)
    exact ⟨hn, hy⟩

/-- An ordinary finite graph is consistent when each input has at most one
associated output. -/
def ConsistentFinitePairs (s : Finset (Nat × Nat)) : Prop :=
  ∀ n x y, (n, x) ∈ s → (n, y) ∈ s → x = y

noncomputable def finitePairsValue (s : Finset (Nat × Nat)) (n : Nat) : Part Nat :=
  Part.assert (∃ y, (n, y) ∈ s) fun h => Part.some (Classical.choose h)

theorem finitePairsValue_mem_iff (s : Finset (Nat × Nat)) (hs : ConsistentFinitePairs s)
    (n y : Nat) : y ∈ finitePairsValue s n ↔ (n, y) ∈ s := by
  constructor
  · intro hy
    obtain ⟨h, hv⟩ := Part.mem_assert_iff.1 hy
    have he : y = Classical.choose h := by simpa using hv
    rw [he]
    exact Classical.choose_spec h
  · intro hy
    let h : ∃ z, (n, z) ∈ s := ⟨y, hy⟩
    apply Part.mem_assert h
    have he := hs n y (Classical.choose h) hy (Classical.choose_spec h)
    simpa using he

/-- Every ordinary finite consistent set of input/output pairs is represented
exactly by one list table, including tables with gaps in their inputs. -/
theorem consistentFinitePairs_represented (s : Finset (Nat × Nat))
    (hs : ConsistentFinitePairs s) :
    ∃ table : FiniteObservation, ∀ n y,
      table[n]? = some (some y) ↔ (n, y) ∈ s := by
  let b := s.sup (fun p => p.1) + 1
  have hb : ∀ n, b ≤ n → ¬ (finitePairsValue s n).Dom := by
    intro n hn hd
    obtain ⟨y, hy⟩ := (Part.dom_iff_mem).1 hd
    have hp := (finitePairsValue_mem_iff s hs n y).1 hy
    have hsbound : n ≤ s.sup (fun p => p.1) :=
      Finset.le_sup (f := fun p : Nat × Nat => p.1) hp
    dsimp [b] at hn
    omega
  refine ⟨graphPrefix (finitePairsValue s) b, ?_⟩
  intro n y
  rw [← finiteValue_mem_iff, boundedGraph_realized _ b hb, finitePairsValue_mem_iff s hs]

def FiniteTableCode (u : Nat.Partrec.Code) : Prop :=
  ∀ table n, Nat.Partrec.Code.eval u (Nat.pair (Encodable.encode table) n) =
    finiteValue table n

theorem finiteTableCode_exists : ∃ u, FiniteTableCode u := by
  have hp := finiteValue_partrec
  change Nat.Partrec (fun n => Part.bind
      (Part.ofOption (Encodable.decode (α := FiniteObservation × Nat) n)) fun p =>
      (finiteValue p.1 p.2).map Encodable.encode) at hp
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨u, ?_⟩
  intro table n
  have h := congrFun hu (Encodable.encode (table, n))
  simpa [Encodable.encode_prod_val, Part.map_id'] using h

def finiteTableCompiler (u : Nat.Partrec.Code) (table : FiniteObservation) : Term :=
  compileLambdaTotal (Nat.Partrec.Code.curry u (Encodable.encode table))

theorem finiteTableCompiler_primrec (u : Nat.Partrec.Code) :
    Primrec (finiteTableCompiler u) := by
  exact primrec_compileLambdaTotal.comp
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode)

theorem finiteTableCompiler_correct (u : Nat.Partrec.Code) (hu : FiniteTableCode u)
    (table : FiniteObservation) :
    Scoped 0 (finiteTableCompiler u table) ∧
      ∀ n y, NumericalResult (finiteTableCompiler u table) n y ↔
        table[n]? = some (some y) := by
  constructor
  · exact (compileLambdaTotal_sound _).1
  · intro n y
    rw [← mem_numericalValue_iff]
    change y ∈ numericalValue (compileLambdaTotal (Nat.Partrec.Code.curry u
      (Encodable.encode table))) n ↔ _
    rw [(compileLambdaTotal_sound _).2 n, Nat.Partrec.Code.eval_curry, hu,
      finiteValue_mem_iff]

theorem finiteTable_closed_realization :
    ∃ f : FiniteObservation → Term, Primrec f ∧
      ∀ table, Scoped 0 (f table) ∧ ∀ n y,
        NumericalResult (f table) n y ↔ table[n]? = some (some y) := by
  obtain ⟨u, hu⟩ := finiteTableCode_exists
  exact ⟨finiteTableCompiler u, finiteTableCompiler_primrec u,
    finiteTableCompiler_correct u hu⟩

/-- A semidecider for the closed-program property enumerates exactly the
finite tables whose finite functions have the property. -/
theorem acceptedFiniteTables_re (C : Set (Nat →. Nat))
    (hC : REPred (fun t : Term => Scoped 0 t ∧ numericalValue t ∈ C)) :
    REPred (fun table : FiniteObservation => finiteValue table ∈ C) := by
  obtain ⟨compiler, hc, hspec⟩ := finiteTable_closed_realization
  have hcomp : REPred (fun table : FiniteObservation =>
      Scoped 0 (compiler table) ∧ numericalValue (compiler table) ∈ C) :=
    hC.comp hc.to_comp
  apply hcomp.of_eq
  intro table
  have hvalue : numericalValue (compiler table) = finiteValue table := by
    funext n
    apply Part.ext
    intro y
    rw [mem_numericalValue_iff, (hspec table).2 n y, finiteValue_mem_iff]
  rw [hvalue]
  simp [(hspec table).1]

/-- Inclusion of numerical graphs makes no claim about divergence. -/
def NumericalExtension (f g : Nat →. Nat) : Prop :=
  ∀ n y, y ∈ f n → y ∈ g n

/-- This consequence uses a finite-table characterization as a hypothesis;
establishing that characterization is the remaining Rice–Shapiro theorem. -/
theorem finiteWitness_extension (C : Set (Nat →. Nat))
    (E : FiniteObservation → Prop)
    (hC : ∀ f, Nat.Partrec f →
      (f ∈ C ↔ ∃ table, E table ∧ ObservationIncluded table f))
    {f g : Nat →. Nat} (hf : Nat.Partrec f) (hg : Nat.Partrec g)
    (hext : NumericalExtension f g) (hin : f ∈ C) : g ∈ C := by
  obtain ⟨table, htable, hbelow⟩ := (hC f hf).mp hin
  apply (hC g hg).mpr
  refine ⟨table, htable, ?_⟩
  intro n y hy
  exact hext n y (hbelow n y hy)

/-- Under the same characterization, acceptance of the empty numerical graph
forces acceptance of every partial computable numerical function. -/
theorem finiteWitness_empty_forces_all (C : Set (Nat →. Nat))
    (E : FiniteObservation → Prop)
    (hC : ∀ f, Nat.Partrec f →
      (f ∈ C ↔ ∃ table, E table ∧ ObservationIncluded table f))
    (hempty : (fun _ : Nat => (Part.none : Part Nat)) ∈ C)
    {g : Nat →. Nat} (hg : Nat.Partrec g) : g ∈ C := by
  apply finiteWitness_extension C E hC Nat.Partrec.none hg ?_ hempty
  intro n y hy
  simp at hy

/-- A uniform partial-recursive switch always offers `f` and offers `g` once
the supplied code has halted. The two branches agree whenever both return. -/
theorem partial_switch_exists {f g : Nat →. Nat}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hext : NumericalExtension f g) :
    ∃ k : Nat.Partrec.Code × Nat →. Nat, Partrec k ∧
      ∀ c n y, y ∈ k (c, n) ↔
        y ∈ f n ∨ ((Nat.Partrec.Code.eval c 0).Dom ∧ y ∈ g n) := by
  let F : Nat.Partrec.Code × Nat →. Nat := fun p => f p.2
  let G : Nat.Partrec.Code × Nat →. Nat := fun p =>
    (Nat.Partrec.Code.eval p.1 0).bind fun _ => g p.2
  have hF : Partrec F := (Partrec.nat_iff.mpr hf).comp Computable.snd
  have hG : Partrec G := by
    apply (Nat.Partrec.Code.eval_part.comp Computable.fst (Computable.const 0)).bind
    exact ((Partrec.nat_iff.mpr hg).comp (Computable.snd.comp Computable.fst)).to₂
  have compat : ∀ p x, x ∈ F p → ∀ y, y ∈ G p → x = y := by
    intro p x hx y hy
    have hy' : y ∈ g p.2 := by
      rcases Part.mem_bind_iff.mp hy with ⟨_, _, h⟩
      exact h
    exact Part.mem_unique (hext p.2 x hx) hy'
  obtain ⟨k, hk, hk_spec⟩ := Partrec.merge hF hG compat
  refine ⟨k, hk, ?_⟩
  intro c n y
  rw [hk_spec]
  change y ∈ f n ∨ y ∈ (Nat.Partrec.Code.eval c 0).bind (fun _ => g n) ↔ _
  simp only [Part.mem_bind_iff, Part.dom_iff_mem]
  aesop

/-- At input `n`, use `f n` only if the control code has not halted within
`n` steps. This is a finite prefix of `f` when the control code halts. -/
def cutoffObservation (p : Nat.Partrec.Code × Nat) : Bool :=
  (Nat.Partrec.Code.evaln p.2 p.1 0).isSome

theorem cutoffObservation_primrec : Primrec cutoffObservation := by
  exact Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0)))

def cutoffValue (f : Nat →. Nat) (p : Nat.Partrec.Code × Nat) : Part Nat :=
  bif cutoffObservation p then Part.none else f p.2

theorem cutoffValue_partrec {f : Nat →. Nat} (hf : Nat.Partrec f) :
    Partrec (cutoffValue f) := by
  exact Partrec.cond cutoffObservation_primrec.to_comp Partrec.none
    ((Partrec.nat_iff.mpr hf).comp Computable.snd)

theorem cutoffValue_no_halt (f : Nat →. Nat) (c : Nat.Partrec.Code)
    (hc : ¬ (Nat.Partrec.Code.eval c 0).Dom) :
    (fun n => cutoffValue f (c, n)) = f := by
  funext n
  have hnone : Nat.Partrec.Code.evaln n c 0 = none := by
    cases h : Nat.Partrec.Code.evaln n c 0 with
    | none => rfl
    | some y =>
      have hy : y ∈ Nat.Partrec.Code.eval c 0 :=
        Nat.Partrec.Code.evaln_sound (by rw [h]; simp)
      exact False.elim (hc ((Part.dom_iff_mem).2 ⟨y, hy⟩))
  simp [cutoffValue, cutoffObservation, hnone]

theorem cutoffValue_halt_bounded (f : Nat →. Nat) (c : Nat.Partrec.Code)
    (hc : (Nat.Partrec.Code.eval c 0).Dom) :
    ∃ b, ∀ n, b ≤ n → ¬ (cutoffValue f (c, n)).Dom := by
  obtain ⟨y, hy⟩ := (Part.dom_iff_mem).1 hc
  obtain ⟨b, hb⟩ := Nat.Partrec.Code.evaln_complete.mp hy
  refine ⟨b, ?_⟩
  intro n hn
  have hm := Nat.Partrec.Code.evaln_mono hn hb
  have hs : (Nat.Partrec.Code.evaln n c 0).isSome = true := by
    cases he : Nat.Partrec.Code.evaln n c 0 with
    | none => simp [he] at hm
    | some z => rfl
  simp [cutoffValue, cutoffObservation, hs]

theorem cutoffValue_below (f : Nat →. Nat) (c : Nat.Partrec.Code) :
    NumericalExtension (fun n => cutoffValue f (c, n)) f := by
  intro n y hy
  cases h : cutoffObservation (c, n) <;> simp [cutoffValue, h] at hy
  exact hy

set_option backward.isDefEq.respectTransparency false in
/-- A semidecidable semantic property has a finite accepted restriction of
each of its partial computable members. -/
theorem semidecidable_finite_witness (C : Set (Nat →. Nat))
    (hC : REPred (fun t : Term => Scoped 0 t ∧ numericalValue t ∈ C))
    {f : Nat →. Nat} (hf : Nat.Partrec f) (hin : f ∈ C) :
    ∃ table, finiteValue table ∈ C ∧ ObservationIncluded table f := by
  classical
  by_contra hnone
  have houts (c : Nat.Partrec.Code) (hc : (Nat.Partrec.Code.eval c 0).Dom) :
      (fun n => cutoffValue f (c, n)) ∉ C := by
    intro hm
    obtain ⟨b, hb⟩ := cutoffValue_halt_bounded f c hc
    let table := graphPrefix (fun n => cutoffValue f (c, n)) b
    have hval : finiteValue table = fun n => cutoffValue f (c, n) :=
      boundedGraph_realized _ b hb
    apply hnone
    refine ⟨table, ?_, ?_⟩
    · rw [hval]
      exact hm
    · apply (observationIncluded_iff _ _).2
      rw [hval]
      exact cutoffValue_below f c
  have hk := cutoffValue_partrec hf
  change Nat.Partrec (fun n => Part.bind
      (Part.ofOption (Encodable.decode (α := Nat.Partrec.Code × Nat) n)) fun p =>
      (cutoffValue f p).map Encodable.encode) at hk
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hk
  have hu' (c : Nat.Partrec.Code) (n : Nat) :
      Nat.Partrec.Code.eval u (Nat.pair (Encodable.encode c) n) =
        cutoffValue f (c, n) := by
    have h := congrFun hu (Encodable.encode (c, n))
    simpa [Encodable.encode_prod_val, Part.map_id'] using h
  let prog : Nat.Partrec.Code → Term := fun c =>
    compileLambdaTotal (Nat.Partrec.Code.curry u (Encodable.encode c))
  have hprog : Primrec prog :=
    primrec_compileLambdaTotal.comp
      (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode)
  have hrun (c : Nat.Partrec.Code) :
      numericalValue (prog c) = fun n => cutoffValue f (c, n) := by
    funext n
    change numericalValue (compileLambdaTotal (Nat.Partrec.Code.curry u
      (Encodable.encode c))) n = cutoffValue f (c, n)
    rw [(compileLambdaTotal_sound _).2 n, Nat.Partrec.Code.eval_curry, hu']
  have hre : REPred (fun c : Nat.Partrec.Code =>
      Scoped 0 (prog c) ∧ numericalValue (prog c) ∈ C) := hC.comp hprog.to_comp
  apply ComputablePred.halting_problem_not_re 0
  apply hre.of_eq
  intro c
  by_cases hc : (Nat.Partrec.Code.eval c 0).Dom
  · constructor
    · intro h
      exact False.elim (houts c hc (by simpa only [hrun c] using h.2))
    · intro h
      exact (h hc).elim
  · have hs : Scoped 0 (prog c) := (compileLambdaTotal_sound _).1
    have hval : numericalValue (prog c) = f := by rw [hrun, cutoffValue_no_halt f c hc]
    constructor
    · intro _
      exact hc
    · intro _
      exact ⟨hs, by simpa only [hval] using hin⟩

set_option backward.isDefEq.respectTransparency false in
/-- A semidecidable extensional closed-program property is upward closed on
partial computable numerical functions. -/
theorem semidecidable_extension (C : Set (Nat →. Nat))
    (hC : REPred (fun t : Term => Scoped 0 t ∧ numericalValue t ∈ C))
    {f g : Nat →. Nat} (hf : Nat.Partrec f) (hg : Nat.Partrec g)
    (hext : NumericalExtension f g) (hin : f ∈ C) : g ∈ C := by
  classical
  by_contra hout
  obtain ⟨k, hk, hspec⟩ := partial_switch_exists hf hg hext
  change Nat.Partrec (fun n => Part.bind
      (Part.ofOption (Encodable.decode (α := Nat.Partrec.Code × Nat) n)) fun p =>
      (k p).map Encodable.encode) at hk
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hk
  have hu' (c : Nat.Partrec.Code) (n : Nat) :
      Nat.Partrec.Code.eval u (Nat.pair (Encodable.encode c) n) = k (c, n) := by
    have h := congrFun hu (Encodable.encode (c, n))
    simpa [Encodable.encode_prod_val, Part.map_id'] using h
  let prog : Nat.Partrec.Code → Term := fun c =>
    compileLambdaTotal (Nat.Partrec.Code.curry u (Encodable.encode c))
  have hprog : Primrec prog :=
    primrec_compileLambdaTotal.comp
      (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode)
  have hrun (c : Nat.Partrec.Code) : numericalValue (prog c) = fun n => k (c, n) := by
    funext n
    change numericalValue (compileLambdaTotal (Nat.Partrec.Code.curry u
      (Encodable.encode c))) n = k (c, n)
    rw [(compileLambdaTotal_sound _).2 n, Nat.Partrec.Code.eval_curry, hu']
  have hnot (c : Nat.Partrec.Code) (hc : ¬ (Nat.Partrec.Code.eval c 0).Dom) :
      numericalValue (prog c) = f := by
    rw [hrun]
    funext n
    apply Part.ext
    intro y
    rw [hspec]
    simp [hc]
  have hyes (c : Nat.Partrec.Code) (hc : (Nat.Partrec.Code.eval c 0).Dom) :
      numericalValue (prog c) = g := by
    rw [hrun]
    funext n
    apply Part.ext
    intro y
    rw [hspec]
    simp only [hc, true_and]
    exact ⟨fun h => h.elim (hext n y) id, Or.inr⟩
  have hre : REPred (fun c : Nat.Partrec.Code =>
      Scoped 0 (prog c) ∧ numericalValue (prog c) ∈ C) := hC.comp hprog.to_comp
  apply ComputablePred.halting_problem_not_re 0
  apply hre.of_eq
  intro c
  by_cases hc : (Nat.Partrec.Code.eval c 0).Dom
  · constructor
    · intro h
      exact False.elim (hout (by simpa only [hyes c hc] using h.2))
    · intro h
      exact (h hc).elim
  · have hs : Scoped 0 (prog c) := (compileLambdaTotal_sound _).1
    constructor
    · intro _
      exact hc
    · intro _
      exact ⟨hs, by simpa only [hnot c hc] using hin⟩

/-- A semidecidable semantic property containing the everywhere-undefined
numerical function contains every partial computable numerical function. -/
theorem semidecidable_empty_forces_all (C : Set (Nat →. Nat))
    (hC : REPred (fun t : Term => Scoped 0 t ∧ numericalValue t ∈ C))
    (hempty : (fun _ : Nat => (Part.none : Part Nat)) ∈ C)
    {g : Nat →. Nat} (hg : Nat.Partrec g) : g ∈ C := by
  apply semidecidable_extension C hC Nat.Partrec.none hg ?_ hempty
  intro n y hy
  simp at hy

/-- A bounded positive observation at one position of a finite table. -/
abbrev TableCheckInput := (Term × FiniteObservation) × List Nat

def tablePointCheck (p : TableCheckInput × Nat) : Bool :=
  let expected := finiteLookup (p.1.1.2, p.2)
  let fuel := (p.1.2[p.2]?).getD 0
  let actual := (breadthObservations fuel p.1.1.1 p.2).head?
  !expected.isSome || decide (actual = expected)

theorem tablePointCheck_primrec : Primrec tablePointCheck := by
  let P := TableCheckInput × Nat
  have ht : Primrec (fun p : P => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htable : Primrec (fun p : P => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hfuels : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun p : P => p.2) := Primrec.snd
  have hfuel : Primrec (fun p : P => (p.1.2[p.2]?).getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp hfuels hi) (Primrec.const 0)
  have hval : Primrec (fun p : P => finiteLookup (p.1.1.2, p.2)) :=
    finiteLookup_primrec.comp (htable.pair hi)
  have hobs : Primrec (fun p : P =>
      (breadthObservations ((p.1.2[p.2]?).getD 0) p.1.1.1 p.2).head?) :=
    primrec_uniformBreadthObservation.comp (ht.pair hi) hfuel
  exact Primrec.or.comp (Primrec.not.comp (Primrec.option_isSome.comp hval))
    (Primrec.eq.comp hobs hval).decide

/-- A certificate supplies one search fuel for each specified table entry. -/
def tableCertificate (p : TableCheckInput) : Prop :=
  ∀ i ∈ List.range p.1.2.length, tablePointCheck (p, i) = true

theorem tableCertificate_primrec : PrimrecPred tableCertificate := by
  have hrel : PrimrecRel (fun (i : Nat) (p : TableCheckInput) =>
      tablePointCheck (p, i) = true) :=
    Primrec.eq.comp (tablePointCheck_primrec.comp (Primrec.snd.pair Primrec.fst))
      (Primrec.const true)
  have hl : Primrec (fun p : TableCheckInput => List.range p.1.2.length) :=
    Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
  exact hrel.forall_mem_list.comp hl Primrec.id

theorem numericalValue_iff_breadth_head (t : Term) (n y : Nat) :
    y ∈ numericalValue t n ↔
      ∃ fuel, (breadthObservations fuel t n).head? = some y := by
  constructor
  · intro hy
    have hy' : y ∈ breadthSearch t n := by rwa [breadthSearch_eq_numericalValue]
    obtain ⟨fuel, hfuel⟩ := Nat.rfindOpt_spec hy'
    exact ⟨fuel, by simpa using hfuel⟩
  · rintro ⟨fuel, hfuel⟩
    apply (mem_numericalValue_iff _ _ _).2
    apply (numeral_iff_breadth _ _ _).2
    exact ⟨fuel, List.mem_of_mem_head? (by simpa using hfuel)⟩

/-- A table is included in a program's numerical graph exactly when a finite
list of positive-observation fuels certifies its specified entries. -/
theorem tableCertificate_iff (t : Term) (table : FiniteObservation) :
    ObservationIncluded table (numericalValue t) ↔
      ∃ fuels, tableCertificate ((t, table), fuels) := by
  classical
  constructor
  · intro hbelow
    have hall (i : Nat) : ∃ fuel, ∀ y,
        finiteLookup (table, i) = some y →
          (breadthObservations fuel t i).head? = some y := by
      cases hget : finiteLookup (table, i) with
      | none => exact ⟨0, by simp⟩
      | some y =>
        have hv : y ∈ finiteValue table i := by simp [finiteValue, hget]
        have ht : y ∈ numericalValue t i :=
          hbelow i y ((finiteValue_mem_iff table i y).1 hv)
        obtain ⟨fuel, hfuel⟩ := (numericalValue_iff_breadth_head t i y).1 ht
        refine ⟨fuel, ?_⟩
        intro z hz
        have : y = z := by simpa [hget] using hz
        simpa [this] using hfuel
    let fuel : Nat → Nat := fun i => Classical.choose (hall i)
    let fuels := (List.range table.length).map fuel
    refine ⟨fuels, ?_⟩
    intro i hi
    have hlt : i < table.length := by simpa using hi
    have hidx : (fuels[i]?).getD 0 = fuel i := by simp [fuels, hlt]
    cases hget : finiteLookup (table, i) with
    | none => simp [tablePointCheck, hget]
    | some y =>
      have hy : (breadthObservations (fuel i) t i).head? = some y :=
        Classical.choose_spec (hall i) y hget
      simpa [tablePointCheck, hget, hidx] using hy
  · rintro ⟨fuels, hcert⟩ i y hentry
    have hlt : i < table.length := (List.getElem?_eq_some_iff.1 hentry).choose
    have hv : y ∈ finiteValue table i := (finiteValue_mem_iff table i y).2 hentry
    have hget : finiteLookup (table, i) = some y := by
      simpa [finiteValue] using hv
    have hc := hcert i (by simpa using hlt)
    have hobs : (breadthObservations ((fuels[i]?).getD 0) t i).head? = some y := by
      simpa [tablePointCheck, hget] using hc
    exact (numericalValue_iff_breadth_head t i y).2 ⟨_, hobs⟩

noncomputable def tableCertificateBool (p : TableCheckInput) : Bool := by
  classical
  exact decide (tableCertificate p)

theorem tableCertificateBool_primrec : Primrec tableCertificateBool := by
  classical
  exact tableCertificate_primrec.decide

abbrev TableSearchWitness := (FiniteObservation × List Nat) × Nat

def decodeTableSearchWitness (w : Nat) : TableSearchWitness :=
  (Encodable.decode w).getD (([], []), 0)

theorem decodeTableSearchWitness_primrec : Primrec decodeTableSearchWitness :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const _)

/-- One finite stage of a dovetailing search for an accepted table and its
positive numerical-observation certificate. -/
noncomputable def tableSearchCheck (u : Nat.Partrec.Code) (p : Term × Nat) : Bool :=
  let w := decodeTableSearchWitness p.2
  (Nat.Partrec.Code.evaln w.2 u (Encodable.encode w.1.1)).isSome &&
    tableCertificateBool ((p.1, w.1.1), w.1.2)

theorem tableSearchCheck_primrec (u : Nat.Partrec.Code) : Primrec (tableSearchCheck u) := by
  let P := Term × Nat
  have hw : Primrec (fun p : P => decodeTableSearchWitness p.2) :=
    decodeTableSearchWitness_primrec.comp Primrec.snd
  have ht : Primrec (fun p : P => (decodeTableSearchWitness p.2).1.1) :=
    Primrec.fst.comp (Primrec.fst.comp hw)
  have hf : Primrec (fun p : P => (decodeTableSearchWitness p.2).1.2) :=
    Primrec.snd.comp (Primrec.fst.comp hw)
  have hk : Primrec (fun p : P => (decodeTableSearchWitness p.2).2) :=
    Primrec.snd.comp hw
  have heval : Primrec (fun p : P =>
      (Nat.Partrec.Code.evaln (decodeTableSearchWitness p.2).2 u
        (Encodable.encode (decodeTableSearchWitness p.2).1.1)).isSome) :=
    Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      ((hk.pair (Primrec.const u)).pair (Primrec.encode.comp ht)))
  have hcert : Primrec (fun p : P => tableCertificateBool
      ((p.1, (decodeTableSearchWitness p.2).1.1), (decodeTableSearchWitness p.2).1.2)) :=
    tableCertificateBool_primrec.comp ((Primrec.fst.pair ht).pair hf)
  exact Primrec.and.comp heval hcert

theorem reFamily_code_exists (E : FiniteObservation → Prop) (hE : REPred E) :
    ∃ u : Nat.Partrec.Code, ∀ table,
      (Nat.Partrec.Code.eval u (Encodable.encode table)).Dom ↔ E table := by
  have hp := hE
  change Nat.Partrec (fun n => Part.bind
      (Part.ofOption (Encodable.decode (α := FiniteObservation) n)) fun table =>
      (Part.assert (E table) (fun _ => Part.some ())).map Encodable.encode) at hp
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨u, ?_⟩
  intro table
  have he : Nat.Partrec.Code.eval u (Encodable.encode table) =
      (Part.assert (E table) (fun _ => Part.some ())).map Encodable.encode := by
    have h := congrFun hu (Encodable.encode table)
    simpa using h
  rw [he]
  by_cases h : E table
  · simp [Part.assert_pos h, h]
  · simp [Part.assert_neg h, h]

theorem evaln_some_iff_dom (u : Nat.Partrec.Code) (n : Nat) :
    (Nat.Partrec.Code.eval u n).Dom ↔
      ∃ k, (Nat.Partrec.Code.evaln k u n).isSome = true := by
  constructor
  · intro hd
    obtain ⟨v, hv⟩ := (Part.dom_iff_mem).1 hd
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨k, ?_⟩
    cases h : Nat.Partrec.Code.evaln k u n with
    | none => simp [h] at hk
    | some x => rfl
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k u n with
    | none => simp [h] at hk
    | some v =>
      exact (Part.dom_iff_mem).2 ⟨v, Nat.Partrec.Code.evaln_sound (by rw [h]; simp)⟩

noncomputable def tableSearchOption (u : Nat.Partrec.Code) (p : Term × Nat) : Option Unit :=
  bif tableSearchCheck u p then some () else none

theorem tableSearchOption_primrec (u : Nat.Partrec.Code) :
    Primrec (tableSearchOption u) :=
  Primrec.cond (tableSearchCheck_primrec u) (Primrec.const _) (Primrec.const _)

/-- Effective enumeration of a family of finite tables yields a semidecision
procedure for inclusion of one of its members in a program's graph. -/
theorem enumerableTableWitness_re (E : FiniteObservation → Prop) (hE : REPred E) :
    REPred (fun t : Term => ∃ table, E table ∧ ObservationIncluded table (numericalValue t)) := by
  classical
  obtain ⟨u, hu⟩ := reFamily_code_exists E hE
  have hsearch : Partrec (fun t : Term => Nat.rfindOpt fun w => tableSearchOption u (t, w)) :=
    Partrec.rfindOpt (tableSearchOption_primrec u).to_comp
  apply hsearch.dom_re.of_eq
  intro t
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨w, x, hw⟩
    cases x
    have hc : tableSearchCheck u (t, w) = true := by
      cases h : tableSearchCheck u (t, w) <;> simp [tableSearchOption, h] at hw ⊢
    let a := decodeTableSearchWitness w
    have hpieces : (Nat.Partrec.Code.evaln a.2 u (Encodable.encode a.1.1)).isSome = true ∧
        tableCertificate ((t, a.1.1), a.1.2) := by
      simpa [tableSearchCheck, tableCertificateBool, a] using hc
    refine ⟨a.1.1, ?_, (tableCertificate_iff t a.1.1).2 ⟨a.1.2, hpieces.2⟩⟩
    exact (hu _).1 ((evaln_some_iff_dom _ _).2 ⟨a.2, hpieces.1⟩)
  · rintro ⟨table, htable, hbelow⟩
    obtain ⟨fuels, hcert⟩ := (tableCertificate_iff t table).1 hbelow
    obtain ⟨k, hk⟩ := (evaln_some_iff_dom _ _).1 ((hu table).2 htable)
    let w := Encodable.encode (((table, fuels), k) : TableSearchWitness)
    have hw : decodeTableSearchWitness w = ((table, fuels), k) := by
      simp [decodeTableSearchWitness, w]
    refine ⟨w, (), ?_⟩
    simp [tableSearchOption, tableSearchCheck, hw, hk, tableCertificateBool, hcert]

theorem finiteValue_natPartrec (table : FiniteObservation) : Nat.Partrec (finiteValue table) :=
  Partrec.nat_iff.mp (finiteValue_partrec.comp ((Computable.const table).pair Computable.id))

theorem numericalValue_natPartrec (t : Term) : Nat.Partrec (numericalValue t) :=
  Partrec.nat_iff.mp
    (uniformNumericalValue_partrec.comp ((Computable.const t).pair Computable.id))

/-- Effective Rice–Shapiro for the numerical semantics of closed lambda
programs. The characterization ranges over partial computable functions. -/
theorem effective_rice_shapiro (C : Set (Nat →. Nat)) :
    REPred (fun t : Term => Scoped 0 t ∧ numericalValue t ∈ C) ↔
      ∃ E : FiniteObservation → Prop, REPred E ∧
        ∀ f, Nat.Partrec f →
          (f ∈ C ↔ ∃ table, E table ∧ ObservationIncluded table f) := by
  classical
  constructor
  · intro hC
    refine ⟨fun table => finiteValue table ∈ C, acceptedFiniteTables_re C hC, ?_⟩
    intro f hf
    constructor
    · exact semidecidable_finite_witness C hC hf
    · rintro ⟨table, hin, hbelow⟩
      exact semidecidable_extension C hC (finiteValue_natPartrec table) hf
        ((observationIncluded_iff table f).1 hbelow) hin
  · rintro ⟨E, hE, hchar⟩
    let R : Term → Prop := fun t => ∃ table, E table ∧ ObservationIncluded table (numericalValue t)
    have hR : REPred R := enumerableTableWitness_re E hE
    let closed : Term → Bool := fun t => decide (requiredDepth t ≤ 0)
    have hclosed : Computable closed :=
      (Primrec.nat_le.comp primrec_requiredDepth (Primrec.const 0)).decide.to_comp
    have hguard : Partrec (fun t : Term =>
        bif closed t then Part.assert (R t) (fun _ => Part.some ()) else Part.none) :=
      Partrec.cond hclosed hR Partrec.none
    apply hguard.dom_re.of_eq
    intro t
    have hchar' : numericalValue t ∈ C ↔ R t := hchar _ (numericalValue_natPartrec t)
    by_cases hs : Scoped 0 t
    · have hd : requiredDepth t ≤ 0 := (scoped_iff_requiredDepth_le t 0).1 hs
      have hz : requiredDepth t = 0 := Nat.le_zero.mp hd
      by_cases hr : R t
      · have hc : numericalValue t ∈ C := hchar'.2 hr
        simp [closed, hz, Part.assert_pos hr, hs, hc]
      · have hc : numericalValue t ∉ C := fun h => hr (hchar'.1 h)
        simp [closed, hz, Part.assert_neg hr, hs, hc]
    · have hd : ¬ requiredDepth t ≤ 0 := fun h => hs ((scoped_iff_requiredDepth_le t 0).2 h)
      have hz : requiredDepth t ≠ 0 := fun h => hd (by omega)
      simp [closed, hz, hs]

#print axioms finiteTable_closed_realization
#print axioms acceptedFiniteTables_re
#print axioms finiteWitness_empty_forces_all
#print axioms semidecidable_extension
#print axioms semidecidable_empty_forces_all
#print axioms semidecidable_finite_witness
#print axioms enumerableTableWitness_re
#print axioms effective_rice_shapiro
#print axioms consistentFinitePairs_represented
end LambdaTuring
