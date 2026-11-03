/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedPostRun
public meta import LambdaTuring.EncodedPostRun

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def observeTableCode : Code := .comp .left .left
def observeNumberCode : Code := .comp .right .left
def observeFuelCode : Code := .right
def observeInitialCode : Code := .comp initialRawCode observeNumberCode
def observeRunInputCode : Code := .pair (.pair observeTableCode observeInitialCode) observeFuelCode
def observeRunCode : Code := .comp rawRunCode observeRunInputCode
def observeCode : Code := .comp postRunCode (.pair observeTableCode observeRunCode)

theorem observeCode_eval (p : RawTable) (n fuel : Nat) :
    observeCode.eval (Nat.pair (Nat.pair (Encodable.encode p) n) fuel) =
      Part.some (Encodable.encode (rawObserveExact p n fuel)) := by
  let input := Nat.pair (Nat.pair (Encodable.encode p) n) fuel
  let start : RawConfig := (0, ⟨[], .one, List.replicate n .one⟩)
  have hcontext : Code.eval .left input = Part.some (Nat.pair (Encodable.encode p) n) := by
    simp [input, Code.eval]
  have hp' : Code.eval .left (Nat.pair (Encodable.encode p) n) = Part.some (Encodable.encode p) := by
    simp [Code.eval]
  have hn' : Code.eval .right (Nat.pair (Encodable.encode p) n) = Part.some n := by
    simp [Code.eval]
  have hp := evalCompSome .left .left _ _ _ hcontext hp'
  have hn := evalCompSome .right .left _ _ _ hcontext hn'
  have hf : observeFuelCode.eval input = Part.some fuel := by simp [input, observeFuelCode, Code.eval]
  have hstart := evalCompSome initialRawCode observeNumberCode _ _ _ hn (initialRawCode_eval n)
  have hpair := evalPairSome observeTableCode observeInitialCode _ _ _ hp hstart
  have hrunInput := evalPairSome (.pair observeTableCode observeInitialCode) observeFuelCode _ _ _ hpair hf
  have hrun := evalCompSome rawRunCode observeRunInputCode _ _ _ hrunInput (rawRunCode_eval p start fuel)
  have hpostInput := evalPairSome observeTableCode observeRunCode _ _ _ hp hrun
  have h := evalCompSome postRunCode _ _ _ _ hpostInput (postRunCode_eval p (rawRunExact p fuel start))
  simpa [observeCode, rawObserveExact, input, start] using h

theorem observeCode_public_yields {states : Nat} (p : Program states) (n m : Nat) :
    Yields p n m ↔ ∃ fuel,
      observeCode.eval (Nat.pair (Nat.pair (Encodable.encode (eraseProgram p)) n) fuel) =
        Part.some (Encodable.encode (some m)) := by
  rw [rawObserveExact_erase_iff]
  constructor
  · rintro ⟨fuel, hf⟩
    refine ⟨fuel, ?_⟩
    rw [observeCode_eval, hf]
  · rintro ⟨fuel, hf⟩
    rw [observeCode_eval] at hf
    have hcode : Encodable.encode (rawObserveExact (eraseProgram p) n fuel) = Encodable.encode (some m) := by
      exact Part.some_injective hf
    exact ⟨fuel, Encodable.encode_injective hcode⟩

#print axioms observeCode
#print axioms observeCode_eval
#print axioms observeCode_public_yields
end LambdaTuring.Machine
