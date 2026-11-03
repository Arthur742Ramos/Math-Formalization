module
/- Lean 4.19.0 execution is recorded by run_formal.py and verification_report.json. -/
public import Std
public section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace CoveringFormalRound3

@[expose] def countDigit (d : Nat) (xs : List (Fin 3)) : Nat :=
  xs.foldl (fun n x => n + if x.val = d then 1 else 0) 0

@[expose] def Moments (xs : List (Fin 3)) : Prop :=
  (xs.foldl (fun n x => n + x.val) 0) % 3 = 0 ∧
  (xs.foldl (fun n x => n + x.val * x.val) 0) % 3 = 2

@[expose] def ExactFiber (zeroMultiplicity : Nat) (xs : List (Fin 3)) : Prop :=
  countDigit 0 xs = zeroMultiplicity ∧ countDigit 1 xs = 1 ∧ countDigit 2 xs = 1

theorem threeDigitMomentCriterion :
    ∀ a b c : Fin 3, Moments [a,b,c] ↔ ExactFiber 1 [a,b,c] := by
  unfold Moments ExactFiber
  decide

theorem fourDigitMomentCriterion :
    ∀ a b c d : Fin 3, Moments [a,b,c,d] ↔ ExactFiber 2 [a,b,c,d] := by
  unfold Moments ExactFiber
  decide

@[expose] def lowDigit (x : Fin 9) : Nat := x.val % 3
@[expose] def highDigit (x : Fin 9) : Nat := x.val / 3
@[expose] def carryModThree (x y : Fin 9) : Nat := if lowDigit x < lowDigit y then 2 else 0

theorem exactCarryIdentity : ∀ x y : Fin 9,
    (x.val + 9 - y.val) % 9 =
      (lowDigit x + 3 - lowDigit y) % 3 +
      3 * ((highDigit x + 3 - highDigit y + carryModThree x y) % 3) := by decide

@[expose] def cyclicSeeds : List (List Nat) := [[0, 5, 2, 0, 1, 0], [0, 5, 7, 8, 2, 0], [0, 3, 0, 4, 6, 1]]

@[expose] def seedEntry (row column : Nat) : Nat :=
  (cyclicSeeds.getD (row / 6) []).getD ((column + row % 6) % 6) 0

@[expose] def seedDifferenceCount (i j residue : Nat) : Nat :=
  (List.range 18).foldl (fun n r =>
    n + if (seedEntry r j + 9 - seedEntry r i) % 9 = residue then 1 else 0) 0

/-- The original index-two difference property, with all ordered column pairs. -/
theorem cyclicSeedIndexTwo : ∀ i j : Fin 6, i ≠ j →
    ∀ d : Fin 9, seedDifferenceCount i.val j.val d.val = 2 := by decide

#print axioms threeDigitMomentCriterion
#print axioms fourDigitMomentCriterion
#print axioms exactCarryIdentity
#print axioms cyclicSeedIndexTwo

end CoveringFormalRound3
