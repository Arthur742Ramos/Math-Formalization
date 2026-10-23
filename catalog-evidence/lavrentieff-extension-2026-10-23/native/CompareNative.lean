module
public import Lake.Check.Compare
public import Lake.Check.Axioms
open Lean
@[expose] public section
def main (args : List String) : IO Unit := do
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk args[0]! .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk args[1]! .read)
  let targets : Array Name := #["Lavrentieff.extensionDomain_isG\u03b4".toName,"Lavrentieff.subset_extensionDomain".toName,"Lavrentieff.cauchy_at_extensionDomain".toName,"Lavrentieff.continuous_extension".toName,"Lavrentieff.isG\u03b4_inter_preimage".toName,"Lavrentieff.extend_inverse_maps".toName,"Lavrentieff.homeomorph_extension".toName,"Lavrentieff.completely_metrizable_extension".toName]
  let legal : Array Name := #["propext".toName,"Quot.sound".toName,"Classical.choice".toName]
  let primitive : Array Name := #["Nat.add".toName,"Nat.sub".toName,"Nat.mul".toName,"Nat.pow".toName,"Nat.gcd".toName,"Nat.div".toName,"Nat.mod".toName,"Nat.beq".toName,"Nat.ble".toName,"Nat.land".toName,"Nat.lor".toName,"Nat.xor".toName,"Nat.shiftLeft".toName,"Nat.shiftRight".toName,"String.ofList".toName,"Char.ofNat".toName,"List".toName,"eagerReduce".toName,"Nat".toName,"String".toName,"String.mk".toName,"Char".toName,"optParam".toName,"autoParam".toName,"semiOutParam".toName,"outParam".toName]
  IO.ofExcept <| Lake.Check.compareAt challenge solution (targets ++ legal) #[] primitive
  IO.ofExcept <| Lake.Check.checkAxioms solution targets #[] legal
  IO.println "Native protected comparison and transitive axiom audit passed"
