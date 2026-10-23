module
public import Lake.Check.Compare
public import Lake.Check.Axioms
open Lean
@[expose] public section
def main (args : List String) : IO Unit := do
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk args[0]! .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk args[1]! .read)
  let targets : Array Name := #["SierpinskiRationals.countable_hasClopenBasis".toName,"SierpinskiRationals.exists_binary_scheme".toName,"SierpinskiRationals.BinaryScheme.code_has_both_bits".toName,"SierpinskiRationals.BinaryScheme.codeOrder_topology".toName,"SierpinskiRationals.nonempty_homeomorph".toName,"SierpinskiRationals.nonempty_homeomorph_iff".toName]
  let legal : Array Name := #["propext".toName,"Quot.sound".toName,"Classical.choice".toName]
  let primitive : Array Name := #["Nat.add".toName,"Nat.sub".toName,"Nat.mul".toName,"Nat.pow".toName,"Nat.gcd".toName,"Nat.div".toName,"Nat.mod".toName,"Nat.beq".toName,"Nat.ble".toName,"Nat.land".toName,"Nat.lor".toName,"Nat.xor".toName,"Nat.shiftLeft".toName,"Nat.shiftRight".toName,"String.ofList".toName,"Char.ofNat".toName,"List".toName,"eagerReduce".toName,"Nat".toName,"String".toName,"String.mk".toName,"Char".toName,"optParam".toName,"autoParam".toName,"semiOutParam".toName,"outParam".toName]
  IO.ofExcept <| Lake.Check.compareAt challenge solution (targets ++ legal) #[] primitive
  IO.ofExcept <| Lake.Check.checkAxioms solution targets #[] legal
  IO.println "Native protected comparison and transitive axiom audit passed"
