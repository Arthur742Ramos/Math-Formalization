/- AI-assisted actual public-pair asserted fixtures.
Exact execution status is external. -/
module
public import RationalGaussianPaperTableEncoding
public meta import RationalGaussianPaperTableEncoding
public meta import RationalGaussianPaperFlow
public meta import RationalFlowEncodingBounds
public section
open SparseCompletion

private def checkPaperTableControl (label : String) (ok : Bool) : IO Unit := do
  if ok then IO.println (label ++ ": PASS") else throw (IO.userError (label ++ ": FAIL"))

#eval checkPaperTableControl "literal general pair retains dimension-bounded support"
  (let D : Fin 2 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
   let E : Fin 0 → Fin 2 → ℚ := fun a => Fin.elim0 a
   let p : Fin 0 → ℚ := Fin.elim0
   let out := rationalGaussianPaperGeneralFlow D E p (fun _ => 1) 1 2 0 1
   decide (out.1.get 0 = 1 ∧ out.1.get 1 = 1 ∧
     rationalFlowTableEntry out.2 0 1 = 0 ∧ rationalFlowTableEntry out.2 1 0 = 0))

#eval checkPaperTableControl "literal exact pair retains dimension-bounded support"
  (let D : Fin 2 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
   let E : Fin 0 → Fin 2 → ℚ := fun a => Fin.elim0 a
   let p : Fin 0 → ℚ := Fin.elim0
   let out := rationalGaussianPaperExactFlow D E p (fun _ => 1) 1 2 1
   decide (out.1.get 0 = 1 ∧ out.1.get 1 = 1 ∧
     rationalFlowTableEntry out.2 0 1 = 0 ∧ rationalFlowTableEntry out.2 1 0 = 0))

#eval checkPaperTableControl "literal exact zero mass and zero weights"
  (let D : Fin 2 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
   let E : Fin 0 → Fin 2 → ℚ := fun a => Fin.elim0 a
   let p : Fin 0 → ℚ := Fin.elim0
   let out := rationalGaussianPaperExactFlow D E p (fun _ => 0) 1 0 1
   decide ((∀ i, out.1.get i = 0) ∧ ∀ i j, rationalFlowTableEntry out.2 i j = 0))

#eval checkPaperTableControl "literal general and exact table canonical budgets"
  (let D : Fin 2 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
   let E : Fin 0 → Fin 2 → ℚ := fun a => Fin.elim0 a
   let p : Fin 0 → ℚ := Fin.elim0
   let g := rationalGaussianPaperGeneralFlow D E p (fun _ => 1) 1 2 0 1
   let e := rationalGaussianPaperExactFlow D E p (fun _ => 1) 1 2 1
   decide ((∀ i j, rationalCanonicalEncodingBits (rationalFlowTableEntry g.2 i j) ≤
       2*gaussianPaperGeneralTableHeight 0 0 2 1 1 2 1+3) ∧
     ∀ i j, rationalCanonicalEncodingBits (rationalFlowTableEntry e.2 i j) ≤
       2*gaussianPaperExactTableHeight 0 0 2 1 1 2 1+3))
