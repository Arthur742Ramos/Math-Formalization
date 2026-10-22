/- Uses the unchanged comparison/axiom APIs from the pinned Lean toolchain.
   Local native check only; this is not the registry sandbox runner. -/
import Lake.Check.Compare
import Lake.Check.Axioms

open Lean Lake.Check

def primitive : Array Name := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor,
  ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
  ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char, ``optParam,
  ``autoParam, ``semiOutParam, ``outParam]

def main (args : List String) : IO UInt32 := do
  let challengePath :: solutionPath :: targets := args
    | throw <| IO.userError "challenge, solution and theorem targets required"
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  let names := targets.toArray.map String.toName
  let axioms := #[``propext, ``Quot.sound, ``Classical.choice]
  match compareAt challenge solution (names ++ axioms) #[] primitive with
  | .error error => IO.eprintln error; return 1
  | .ok () => IO.println s!"Pinned compareAt: PASS ({names.size} theorem targets, zero definition holes, all primitives)"
  match checkAxioms solution names #[] axioms with
  | .error error => IO.eprintln error; return 1
  | .ok () => IO.println "Pinned checkAxioms: PASS"
  let helper := "SparseCompletion.envelope".toName
  let some (.defnInfo value) := solution.constMap[helper]?
    | throw <| IO.userError "fixed envelope helper missing"
  -- A well-typed let wrapper changes the fixed definition's exact value.
  -- It remains outside definition holes and must be rejected through closure.
  let changed := { value with value := .letE `regressionWitness value.type value.value (.bvar 0) false }
  let altered := { solution with constMap := solution.constMap.insert helper (.defnInfo changed) }
  match compareAt challenge altered (names ++ axioms) #[] primitive with
  | .ok () => IO.eprintln "Altered fixed helper was accepted"; return 1
  | .error error =>
    unless error.contains "SparseCompletion.envelope" do
      throw <| IO.userError s!"Unexpected negative-control rejection: {error}"
    IO.println s!"Altered fixed envelope helper rejected: {error}"
  return 0
