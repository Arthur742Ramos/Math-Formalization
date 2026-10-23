/- Asserted controls for actual input clearing, Cramer coordinates and actual
fixed/interval/repertoire constructors. Classical existence is not executed. -/
module
public import RationalConstructedLPSmallWitness
meta import RationalConstructedLPSmallWitness
open scoped BigOperators Matrix
open SparseCompletion

def lp35A : Matrix (Fin 2) (Fin 2) ℤ := !![2,1;1,3]
def lp35b : Fin 2 → ℤ := ![1,2]
def lp35S : RationalLinearSystem (Fin 2) 1 :=
  ⟨fun i _ => if i=0 then (1/2 : ℚ) else -1/3, fun i => if i=0 then (1/3 : ℚ) else 2/5⟩
#guard lp35A.det = 5
#guard rationalIntegerCramerWitness lp35A lp35b 0 = 1/5
#guard rationalIntegerCramerWitness lp35A lp35b 1 = 3/5
#guard (rationalIntegerCramerWitness lp35A lp35b 0).den = 5
#guard ∀ j, RationalInputHeight (rationalIntegerCramerWitness lp35A lp35b j) 3
#guard rationalLPAugmentedMatrix lp35S 0 none = 1/3
#guard rationalLPAugmentedMatrix lp35S 1 (some 0) = -1/3
#guard rationalLPInputDenominator lp35S = 30
#guard rationalLPIntegerInput lp35S 0 (some 0) = 15
#guard rationalLPIntegerInput lp35S 1 none = 12
#guard rationalLPSmallWitnessHeight 2 1 3 = 16
#guard rationalLPSmallWitnessHeight 7 0 3 = 0
#guard Matrix.det (fun _ _ => (0 : ℤ) : Matrix (Fin 0) (Fin 0) ℤ) = 1

def lp35Fixed := (rationalGapSystem (k := 0) (m := 1) (fun a => Fin.elim0 a)
  (fun _ a => Fin.elim0 a) (fun a => Fin.elim0 a) 1 1 1 1).append
    (⟨fun (_ : Fin 1) (_ : Fin 1) => (1/2 : ℚ), fun _ => (1 : ℚ)⟩ : RationalLinearSystem (Fin 1) 1)
#guard lp35Fixed.Satisfies (fun _ => 1)
#guard ¬lp35Fixed.Satisfies (fun _ => 0)

def lp35Interval := rationalIntervalRepertoireSystem (k := 0) (m := 1)
  (fun a => Fin.elim0 a) (fun a => Fin.elim0 a) (fun _ a => Fin.elim0 a)
  (fun _ a => Fin.elim0 a) (fun a => Fin.elim0 a) 1 1 1 1
  (⟨fun (_ : Fin 1) _ => (1/2 : ℚ), fun _ => (1 : ℚ)⟩ :
    RationalLinearSystem (Fin 1) (1+(1*0+(0*0+0*1))))
def lp35Point := intervalPack (k := 0) (m := 1) (H := rationalGridSize 1 1 1)
  (fun _ => (1 : ℚ)) (fun _ a => Fin.elim0 a) (fun a => Fin.elim0 a) (fun _ _ => 0)
#guard lp35Interval.Satisfies lp35Point
#guard rationalIntervalRecover (fun (_ : Fin 1) (_ : Fin 1) => (-2/3 : ℚ))
  (fun _ _ => 0) (fun _ => 0) 0 0 = -2/3
#guard rationalIntervalRecover (fun (_ : Fin 1) (_ : Fin 1) => (-2/3 : ℚ))
  (fun _ _ => 1/3) (fun _ => 1/2) 0 0 = 2/3
