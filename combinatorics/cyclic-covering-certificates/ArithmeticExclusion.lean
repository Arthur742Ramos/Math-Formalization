module
/- Complete exclusion by the arithmetic certificate, for all lower profiles
   of the seventeen supplied representatives. The final bridge from arbitrary
   Z9 coverings and classification completeness remains outside this module. -/
public import ProfileCoverage
public section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace CoveringArithmeticExclusion
open CoveringF3 CoveringProfiles CoveringFormalRound3Linear CoveringProfileCoverage

@[expose] def base (c : Nat) (xs : List Trit) : LinearWitness := ⟨c,xs.map Fin.val,[]⟩
@[expose] def upper (w : LinearWitness) (v : Nat → F3) (r j : Nat) : F3 :=
  add (v r) (neg (ofNat (entry w.classIndex r j / 3 +
    if w.low.getD r 0 < entry w.classIndex r j % 3 then 1 else 0)))
@[expose] def secondMoment (w : LinearWitness) (v : Nat → F3) (j t : Nat) : F3 :=
  CoveringF3.sum 10 (fun r => if phaseAt w r j = t then mul (upper w v r j) (upper w v r j) else 0)

@[expose] def LiftEquations (c : Nat) (xs : List Trit) (v : Nat → F3) : Prop :=
  (∀ r, r < 15 → CoveringF3.sum 10 (fun i =>
      mul (CoveringCertifiedLinear.matrix3 (base c xs) r i) (v i)) =
      CoveringCertifiedLinear.right3 (base c xs) r) ∧
  (∀ j, j < 5 → ∀ t, t < 3 → secondMoment (base c xs) v j t = 2)

theorem exceptional_moment_is_quadratic (v : Nat → F3) :
    secondMoment CoveringExceptional.exceptional v 2 1 = CoveringExceptional.quadratic v := by
  simp [secondMoment, CoveringF3.sum, phaseAt, CoveringExceptional.exceptional,
    entry, representatives, upper, CoveringExceptional.quadratic,
    CoveringExceptional.upperDifference, add_zero, zero_add, add_assoc]

/-- The 71 left-nullspace witnesses and one affine obstruction jointly
    exclude every digit-lifting system for every eligible lower profile. -/
theorem no_digit_lift (c : Nat) (hc : c < 17) (xs : List Trit)
    (he : Eligible c xs) : ¬ ∃ v : Nat → F3, LiftEquations c xs v := by
  rintro ⟨v,hl,hq⟩
  rcases every_eligible_profile_has_certificate c hc xs he with
    ⟨w,hw,hci,hlo⟩ | ⟨hci,hlo⟩
  · apply CoveringCertifiedLinear.no_linear_solution w hw
    refine ⟨v,?_⟩
    simpa [CoveringCertifiedLinear.matrix3, CoveringCertifiedLinear.right3,
      base, coefficient, phaseAt, rhs, hci, hlo] using hl
  · subst c
    have hb : base 12 xs = CoveringExceptional.exceptional := by
      simp only [base, hlo]
      rfl
    rw [hb] at hl hq
    apply CoveringExceptional.no_fibre_solution v
    · exact hl
    · rw [← exceptional_moment_is_quadratic]
      exact hq 2 (by decide) 1 (by decide)

#print axioms exceptional_moment_is_quadratic
#print axioms no_digit_lift
end CoveringArithmeticExclusion
