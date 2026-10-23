/- AI-assisted formalization. Executable rational graph-fuel pair controls; execution status is receipt-bound. -/
module
public import RationalPaperGraphFlow
public meta import RationalPaperGraphFlow
public meta import RationalFeatureDeletion
public meta import RationalTableAugmentation
@[expose] public section
open SparseCompletion
open scoped BigOperators

private def D0 : Fin 2 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
private def E0 : Fin 0 → Fin 2 → ℚ := fun a => Fin.elim0 a
private def p0 : Fin 0 → ℚ := fun a => Fin.elim0 a
private def pair : (Fin 2 → ℚ) × RationalFlowTable 2 :=
  rationalPaperExactGraphFlow D0 E0 p0 (fun _ => 1/2) 1 1 1
private def Bpair : Fin 2 → Fin 2 → ℚ := rationalFlowTableEntry pair.2

#guard (rationalWeightSupport pair.1).card=1
#guard (∑ i, pair.1 i)=1
#guard ∀ i j, Bpair i j= -Bpair j i
#guard ∀ i j, -1 ≤ Bpair i j ∧ Bpair i j ≤ 1
#guard ∀ i, (∑ j, Bpair i j*pair.1 j) ≤ 1

private def zeropair : (Fin 2 → ℚ) × RationalFlowTable 2 :=
  rationalPaperExactGraphFlow D0 E0 p0 (fun _ => 0) 1 0 1
#guard ∀ i, zeropair.1 i=0
#guard ∀ i j, rationalFlowTableEntry zeropair.2 i j=0

private def generalpair : (Fin 2 → ℚ) × RationalFlowTable 2 :=
  rationalPaperGeneralGraphFlow D0 E0 p0 (fun _ => 1/2) 1 1 0 1
#guard (∑ i, generalpair.1 i)=1
#guard ∀ i j, rationalFlowTableEntry generalpair.2 i j=
  -rationalFlowTableEntry generalpair.2 j i
#guard ∀ i, (∑ j, rationalFlowTableEntry generalpair.2 i j*generalpair.1 j) ≤ 1
