/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ExtensionalMachine
public meta import LambdaTuring.ExtensionalMachine

@[expose] public section

namespace LambdaTuring.Machine

/- A data-only table representation removes the dependent state bound while
preserving every transition of a well-formed public finite machine. -/
abbrev RawTable := List (Option (Nat × Action))
abbrev RawConfig := Nat × Tape

def eraseInstruction (x : Option (Fin (states+1) × Action)) : Option (Nat × Action) :=
  x.map fun qa => (qa.1.val, qa.2)

def eraseProgram {states : Nat} (p : Program states) : RawTable :=
  p.table.map eraseInstruction

def eraseConfig {states : Nat} (c : Config states) : RawConfig := (c.state.val, c.tape)

def rawInstruction (p : RawTable) (q : Nat) (s : Symbol) : Option (Nat × Action) :=
  (p[q * 3 + symbolIndex s]?).getD none

def rawStep (p : RawTable) (c : RawConfig) : Option RawConfig :=
  (rawInstruction p c.1 c.2.head).map fun qa => (qa.1, perform qa.2 c.2)

theorem rawInstruction_erase {states : Nat} (p : Program states) (q : Fin (states+1)) (s : Symbol) :
    rawInstruction (eraseProgram p) q.val s = eraseInstruction (instruction p q s) := by
  unfold rawInstruction eraseProgram instruction
  cases h : p.table[q.val * 3 + symbolIndex s]? with
  | none => simp [List.getElem?_map, h, eraseInstruction]
  | some x => simp [List.getElem?_map, h, eraseInstruction]

theorem rawStep_erase {states : Nat} (p : Program states) (c : Config states) :
    rawStep (eraseProgram p) (eraseConfig c) = (step p c).map eraseConfig := by
  simp only [rawStep, eraseConfig, rawInstruction_erase, step]
  cases h : instruction p c.state c.tape.head with
  | none => simp [eraseInstruction]
  | some qa => cases qa; simp [eraseInstruction, eraseConfig]

def rawRunExact (p : RawTable) : Nat → RawConfig → Option RawConfig
  | 0, c => some c
  | fuel+1, c => (rawRunExact p fuel c).bind (rawStep p)

theorem rawRunExact_erase {states : Nat} (p : Program states) (fuel : Nat) (c : Config states) :
    rawRunExact (eraseProgram p) fuel (eraseConfig c) = (runExact p fuel c).map eraseConfig := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    rw [rawRunExact, ih, runExact]
    cases h : runExact p fuel c with
    | none => simp
    | some d => simp [rawStep_erase]

def rawObserveExact (p : RawTable) (n fuel : Nat) : Option Nat :=
  (rawRunExact p fuel (0, ⟨[], .one, List.replicate n .one⟩)).bind fun c =>
    if rawStep p c = none then decode (c.2.head :: c.2.right) else none

theorem rawObserveExact_erase {states : Nat} (p : Program states) (n fuel : Nat) :
    rawObserveExact (eraseProgram p) n fuel = observeExact p n fuel := by
  unfold rawObserveExact observeExact
  change (rawRunExact (eraseProgram p) fuel (eraseConfig (initial (states := states) n))).bind _ = _
  rw [rawRunExact_erase]
  cases h : runExact p fuel (initial n) with
  | none => simp
  | some c =>
    simp only [Option.map_some, Option.bind_some]
    rw [rawStep_erase]
    cases hs : step p c <;> simp [eraseConfig]

theorem rawObserveExact_erase_iff {states : Nat} (p : Program states) (n m : Nat) :
    Yields p n m ↔ ∃ fuel, rawObserveExact (eraseProgram p) n fuel = some m := by
  rw [yields_iff_observeExact]
  simp only [rawObserveExact_erase]

theorem primrec_rawStep : Primrec₂ rawStep := by
  let P := RawTable × RawConfig
  have htab : Primrec (fun x : P => x.1) := Primrec.fst
  have hq : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  have hi : Primrec (fun x : P => x.2.1 * 3 + symbolIndex x.2.2.head) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hq (Primrec.const 3))
      (primrec_symbolIndex.comp (primrec_tapeHead.comp ht))
  have hlookup : Primrec (fun x : P => rawInstruction x.1 x.2.1 x.2.2.head) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp htab hi) (Primrec.const none)
  have hnext : Primrec₂ (fun (x : P) (qa : Nat × Action) => (qa.1, perform qa.2 x.2.2)) := by
    have hq' : Primrec (fun y : P × (Nat × Action) => y.2.1) := Primrec.fst.comp Primrec.snd
    have ha : Primrec (fun y : P × (Nat × Action) => y.2.2) := Primrec.snd.comp Primrec.snd
    have ht' : Primrec (fun y : P × (Nat × Action) => y.1.2.2) := ht.comp Primrec.fst
    exact hq'.pair (primrec_perform.comp ha ht')
  exact Primrec.option_map hlookup hnext

theorem primrec_rawRunExact : Primrec (fun x : (RawTable × RawConfig) × Nat =>
    rawRunExact x.1.1 x.2 x.1.2) := by
  let P := RawTable × RawConfig
  have hbase : Primrec (fun x : P => some x.2) := Primrec.option_some.comp Primrec.snd
  have hstep : Primrec₂ (fun (x : P) (q : Nat × Option RawConfig) =>
      q.2.bind (rawStep x.1)) := by
    apply Primrec.option_bind (Primrec.snd.comp Primrec.snd)
    exact (primrec_rawStep.comp
      ((Primrec.fst : Primrec (fun x : P => x.1)).comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.snd : Primrec (fun x : (P × (Nat × Option RawConfig)) × RawConfig => x.2))).to₂
  have h := Primrec.nat_rec hbase hstep
  change Primrec₂ (fun (x : P) fuel => rawRunExact x.1 fuel x.2)
  apply h.of_eq
  intro p fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [rawRunExact, ih]

theorem primrec_rawObserveExact :
    Primrec₂ (fun i : RawTable × Nat => fun fuel => rawObserveExact i.1 i.2 fuel) := by
  let I := RawTable × Nat
  let Q := I × RawConfig
  have ht : Primrec (fun i : I => (⟨[], .one, List.replicate i.2 .one⟩ : Tape)) :=
    primrec_tapeMk.comp ((Primrec.const []).pair
      ((Primrec.const Symbol.one).pair (primrec_replicateOne.comp Primrec.snd)))
  have hstart : Primrec (fun i : I => ((0, ⟨[], .one, List.replicate i.2 .one⟩) : RawConfig)) :=
    (Primrec.const 0).pair ht
  have hrun : Primrec (fun x : I × Nat => rawRunExact x.1.1 x.2
      (0, ⟨[], .one, List.replicate x.1.2 .one⟩)) :=
    primrec_rawRunExact.comp
      (((Primrec.fst.comp Primrec.fst).pair (hstart.comp Primrec.fst)).pair Primrec.snd)
  have hq : Primrec (fun q : Q => q.2.2) := Primrec.snd.comp Primrec.snd
  have hd : Primrec (fun q : Q => decode (q.2.2.head :: q.2.2.right)) :=
    primrec_decode.comp (Primrec.list_cons.comp (primrec_tapeHead.comp hq) (primrec_tapeRight.comp hq))
  have hp : Primrec₂ (fun (i : I) (c : RawConfig) =>
      if rawStep i.1 c = none then decode (c.2.head :: c.2.right) else none) :=
    Primrec.ite
      (Primrec.eq.comp (primrec_rawStep.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.const none)) hd (Primrec.const none)
  exact Primrec.option_bind hrun
    (hp.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

noncomputable def rawValue (p : RawTable) (n : Nat) : Part Nat :=
  Nat.rfindOpt fun fuel => rawObserveExact p n fuel

theorem rawValue_erase {states : Nat} (p : Program states) (n : Nat) :
    rawValue (eraseProgram p) n = exactValue p n := by
  unfold rawValue exactValue
  congr 1
  funext fuel
  exact rawObserveExact_erase p n fuel

theorem mem_rawValue_erase_iff {states : Nat} (p : Program states) (n m : Nat) :
    m ∈ rawValue (eraseProgram p) n ↔ Yields p n m := by
  rw [rawValue_erase, mem_exactValue_iff]

theorem uniformRawValue_partrec : Partrec (fun p : RawTable × Nat => rawValue p.1 p.2) :=
  Partrec.rfindOpt primrec_rawObserveExact.to_comp

def UniformMachineCode (u : Nat.Partrec.Code) : Prop :=
  ∀ p n, Nat.Partrec.Code.eval u (Nat.pair (Encodable.encode p) n) = rawValue p n

theorem uniformMachineCode_exists : ∃ u, UniformMachineCode u := by
  have hp := uniformRawValue_partrec
  change Nat.Partrec (fun n => Part.bind (Part.ofOption (Encodable.decode (α := RawTable × Nat) n)) fun p =>
    (rawValue p.1 p.2).map Encodable.encode) at hp
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨u, ?_⟩
  intro p n
  have h := congrFun hu (Encodable.encode (p, n))
  simpa [Encodable.encode_prod_val, Part.map_id'] using h

def specializeMachineCode (u : Nat.Partrec.Code) {states : Nat} (p : Program states) :
    Nat.Partrec.Code := Nat.Partrec.Code.curry u (Encodable.encode (eraseProgram p))

theorem specializeMachineCode_eval (u : Nat.Partrec.Code) (hu : UniformMachineCode u)
    {states : Nat} (p : Program states) (n : Nat) :
    Nat.Partrec.Code.eval (specializeMachineCode u p) n = rawValue (eraseProgram p) n := by
  rw [specializeMachineCode, Nat.Partrec.Code.eval_curry, hu]

def machineToLambdaWith (u : Nat.Partrec.Code) {states : Nat} (p : Program states) : Term :=
  compileLambdaTotal (specializeMachineCode u p)

theorem machineToLambdaWith_correct (u : Nat.Partrec.Code) (hu : UniformMachineCode u)
    {states : Nat} (p : Program states) : Scoped 0 (machineToLambdaWith u p) ∧ ∀ n m,
      NumericalResult (machineToLambdaWith u p) n m ↔ Yields p n m := by
  refine ⟨(compileLambdaTotal_sound (specializeMachineCode u p)).1, ?_⟩
  intro n m
  rw [machineToLambdaWith, ← mem_numericalValue_iff,
    (compileLambdaTotal_sound (specializeMachineCode u p)).2 n,
    specializeMachineCode_eval u hu, mem_rawValue_erase_iff]

#print axioms primrec_rawStep
#print axioms primrec_rawRunExact
#print axioms primrec_rawObserveExact
#print axioms uniformMachineCode_exists
#print axioms machineToLambdaWith_correct

#print axioms rawStep_erase
#print axioms rawObserveExact_erase_iff
end LambdaTuring.Machine
