/- Asserted runtime fixtures; exact run status belongs to receipts. -/
module
public import GaussianFeatureBits
public import GaussianTransientArithmetic
public meta import RationalGaussianKernel
public meta import GaussianInputEncoding
public meta import GaussianOutputBits
public meta import RationalGaussianFeature
public section
open SparseCompletion SparseCompletion.Gaussian

private def checkControl (label : String) (ok : Bool) : IO Unit := do
  if ok then IO.println (label ++ ": PASS") else throw (IO.userError (label ++ ": FAIL"))

#eval checkControl "cleared input 1/2,1/3"
  (let A := tableOfFn (r := 1) (n := 2) (fun _ j => if j = 0 then 1/2 else 1/3)
   decide (Matrix.den (entry A) = 6 ∧ Matrix.num (entry A) 0 0 = 3 ∧
     Matrix.num (entry A) 0 1 = 2))

#eval checkControl "actual rational return and digit bound"
  (let A := tableOfFn (r := 1) (n := 2) (fun _ j => if j = 0 then 1/2 else 1/3)
   match kernel 1 2 A with
   | none => false
   | some w => decide (w.toList = [-2/3, 1] ∧
       (∀ j, Nat.size (w.get j).num.natAbs ≤ kernelOutputBitBound 1 2 2 ∧
         Nat.size (w.get j).den ≤ kernelOutputBitBound 1 2 2)))

#eval checkControl "zero rows unit size"
  (match kernel 0 1 (tableOfFn (fun i => Fin.elim0 i)) with
   | none => false
   | some w => decide (w.toList = [1] ∧ Nat.size (w.get 0).den ≤ kernelOutputBitBound 0 1 0))

#eval checkControl "zero columns fail"
  ((kernel 1 0 (tableOfFn (fun _ j => Fin.elim0 j))).isNone)

#eval checkControl "independent columns fail"
  ((kernel 2 2 (tableOfFn (fun i j => if i = j then 1 else 0))).isNone)

#eval checkControl "fixed feature ignores weight magnitudes"
  (let A : Fin 1 → Fin 2 → ℚ := fun _ _ => 1
   let small := (rationalGaussianFeatureKernel A (fun _ => 1)).map List.ofFn
   let large := (rationalGaussianFeatureKernel A (fun _ => (2:ℚ)^100)).map List.ofFn
   decide (small = some [-1, 1] ∧ large = small))
