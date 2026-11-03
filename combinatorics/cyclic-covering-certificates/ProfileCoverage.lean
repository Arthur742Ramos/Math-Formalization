module
/- This module links the seventeen finite table equalities to the complete
   quota enumeration, and matches each resulting profile to its arithmetic
   certificate. It does not assert global classification completeness. -/
public import ProfileCheck00
public import ProfileCheck01
public import ProfileCheck02
public import ProfileCheck03
public import ProfileCheck04
public import ProfileCheck05
public import ProfileCheck06
public import ProfileCheck07
public import ProfileCheck08
public import ProfileCheck09
public import ProfileCheck10
public import ProfileCheck11
public import ProfileCheck12
public import ProfileCheck13
public import ProfileCheck14
public import ProfileCheck15
public import ProfileCheck16
public import CertifiedLinear
public import ExceptionalProfile
public section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace CoveringProfileCoverage
open CoveringProfiles CoveringProfileData CoveringProfileChecks CoveringFormalRound3Linear

theorem profile_tables (c : Nat) (hc : c < 17) :
    filteredProfiles c = expectedProfiles.getD c [] := by
  have h : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨
      c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile00
  · exact profile01
  · exact profile02
  · exact profile03
  · exact profile04
  · exact profile05
  · exact profile06
  · exact profile07
  · exact profile08
  · exact profile09
  · exact profile10
  · exact profile11
  · exact profile12
  · exact profile13
  · exact profile14
  · exact profile15
  · exact profile16

@[expose] def Eligible (c : Nat) (xs : List Trit) : Prop :=
  xs.length = 10 ∧ count 0 xs = 4 ∧ count 1 xs = 3 ∧ count 2 xs = 3 ∧ profileOK c xs = true

theorem every_eligible_profile_is_listed (c : Nat) (hc : c < 17)
    (xs : List Trit) (h : Eligible c xs) : xs ∈ expectedProfiles.getD c [] := by
  obtain ⟨hlen,hz,ho,ht,hcols⟩ := h
  rw [← profile_tables c hc]
  exact List.mem_filter.mpr ⟨balanced_complete xs hlen hz ho ht, hcols⟩

@[expose] def hasCertificate (c : Nat) (xs : List Trit) : Bool :=
  witnesses.any (fun w => decide (w.classIndex = c ∧ w.low = xs.map Fin.val)) ||
  decide (c = 12 ∧ xs.map Fin.val = CoveringExceptional.exceptional.low)

theorem all_profiles_have_certificates : ∀ c : Fin 17,
    (expectedProfiles.getD c.val []).all (hasCertificate c.val) = true := by decide

theorem exactly_seventy_two_profiles : expectedProfiles.flatten.length = 72 := by decide

/-- Every possible lower profile of one of the seventeen fixed representatives
    is covered by one of the 71 linear certificates or the one affine certificate. -/
theorem every_eligible_profile_has_certificate (c : Nat) (hc : c < 17)
    (xs : List Trit) (h : Eligible c xs) :
    (∃ w ∈ witnesses, w.classIndex = c ∧ w.low = xs.map Fin.val) ∨
    (c = 12 ∧ xs.map Fin.val = CoveringExceptional.exceptional.low) := by
  have hmem := every_eligible_profile_is_listed c hc xs h
  have hh := List.all_eq_true.mp (all_profiles_have_certificates ⟨c,hc⟩) xs hmem
  obtain hl | hr := Bool.or_eq_true_iff.mp hh
  · obtain ⟨w,hw,hmatch⟩ := List.any_eq_true.mp hl
    exact Or.inl ⟨w,hw,of_decide_eq_true hmatch⟩
  · exact Or.inr (of_decide_eq_true hr)

#print axioms every_eligible_profile_is_listed
#print axioms exactly_seventy_two_profiles
#print axioms every_eligible_profile_has_certificate
end CoveringProfileCoverage
