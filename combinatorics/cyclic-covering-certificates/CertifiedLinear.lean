module
public import F3Linear
public import ArithmeticCertificate
public section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace CoveringCertifiedLinear
open CoveringF3 CoveringFormalRound3Linear

@[expose] def matrix3 (w : LinearWitness) (r c : Nat) : F3 := ofNat (coefficient w r c)
@[expose] def right3 (w : LinearWitness) (r : Nat) : F3 := ofNat (rhs w r)
@[expose] def multiplier3 (w : LinearWitness) (r : Nat) : F3 := ofNat (w.multiplier.getD r 0)

@[expose] def ValidCertificate (w : LinearWitness) : Prop :=
  (∀ c : Fin 10, CoveringF3.sum 15 (fun r => mul (multiplier3 w r) (matrix3 w r c.val)) = 0) ∧
  CoveringF3.sum 15 (fun r => mul (multiplier3 w r) (right3 w r)) = 1

instance (w : LinearWitness) : Decidable (ValidCertificate w) := by
  unfold ValidCertificate
  infer_instance

@[expose] def validCertificate (w : LinearWitness) : Bool := decide (ValidCertificate w)

theorem allCertificatesValid : witnesses.all validCertificate = true := by decide

theorem valid_of_member (w : LinearWitness) (h : w ∈ witnesses) : ValidCertificate w := by
  have hh := List.all_eq_true.mp allCertificatesValid w h
  exact of_decide_eq_true hh

/-- Every one of the 71 literal certificates rules out all vectors over F3.
    The input matrix and RHS are computed from its representative and lower
    digit profile, with the carry convention from the paper. -/
theorem no_linear_solution (w : LinearWitness) (h : w ∈ witnesses) :
    ¬ ∃ v : Nat → F3, ∀ r, r < 15 →
      CoveringF3.sum 10 (fun c => mul (matrix3 w r c) (v c)) = right3 w r := by
  obtain ⟨hA, hb⟩ := valid_of_member w h
  exact left_nullspace_sound 15 10 (matrix3 w) (right3 w) (multiplier3 w)
    (fun c hc => hA ⟨c,hc⟩) hb

#print axioms allCertificatesValid
#print axioms no_linear_solution
end CoveringCertifiedLinear
