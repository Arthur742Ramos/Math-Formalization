/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierLeafCertificate
public import ErdosOverlap.Numerics.IntegralClaim

/-!
# Finite adjacent-block assembly for checked native integral leaves

A block exports only its two rational endpoints, exact integer total, and
integral inequality. The explicit width errors telescope, permitting later
balanced gluing without re-expanding the individual leaf arithmetic.
-/

@[expose] public section

namespace ErdosOverlap.FrontierLeaves

open Numerics MeasureTheory

def ProfileLeaf.claim (leaf : ProfileLeaf) : IntegralClaim :=
  ⟨leaf.geometry.val.left,leaf.geometry.val.right,leaf.lower⟩

def CentralLeaf.claim (leaf : CentralLeaf) : IntegralClaim :=
  ⟨leaf.geometry.val.left,leaf.geometry.val.right,leaf.lower⟩

def DenominatorLeaf.claim (leaf : DenominatorLeaf) : IntegralClaim :=
  ⟨leaf.geometry.val.left,leaf.geometry.val.right,leaf.upper⟩

def profileClaims {mode : Fin 20} (leaves : List (CheckedProfileLeaf mode)) : List IntegralClaim :=
  leaves.map (fun leaf => leaf.val.claim)

def centralClaims (leaves : List CheckedCentralLeaf) : List IntegralClaim :=
  leaves.map (fun leaf => leaf.val.claim)

def denominatorClaims (leaves : List CheckedDenominatorLeaf) : List IntegralClaim :=
  leaves.map (fun leaf => leaf.val.claim)

theorem profileClaims_integrable {mode : Fin 20} (leaves : List (CheckedProfileLeaf mode)) :
    ∀ c ∈ profileClaims leaves,
      IntervalIntegrable (profileIntegrand mode) volume (c.left : ℝ) (c.right : ℝ) := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨leaf,_,rfl⟩
  exact Geometry.intervalIntegrable leaf.val.geometry.valid (profileIntegrand_integrable mode)

theorem centralClaims_integrable (leaves : List CheckedCentralLeaf) :
    ∀ c ∈ centralClaims leaves,
      IntervalIntegrable centralIntegrand volume (c.left : ℝ) (c.right : ℝ) := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨leaf,_,rfl⟩
  exact Geometry.intervalIntegrable leaf.val.geometry.valid centralIntegrand_integrable

theorem denominatorClaims_integrable (leaves : List CheckedDenominatorLeaf) :
    ∀ c ∈ denominatorClaims leaves,
      IntervalIntegrable denominatorIntegrand volume (c.left : ℝ) (c.right : ℝ) := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨leaf,_,rfl⟩
  exact Geometry.intervalIntegrable leaf.val.geometry.valid denominatorIntegrand_integrable

theorem profileBlock_integrable {mode : Fin 20} (leaves : List (CheckedProfileLeaf mode))
    {lo hi : ℚ} (hc : IntegralClaim.chainCheck lo hi (profileClaims leaves) = true) :
    IntervalIntegrable (profileIntegrand mode) volume (lo : ℝ) (hi : ℝ) :=
  IntegralClaim.chain_integrable hc (profileClaims_integrable leaves)

theorem centralBlock_integrable (leaves : List CheckedCentralLeaf)
    {lo hi : ℚ} (hc : IntegralClaim.chainCheck lo hi (centralClaims leaves) = true) :
    IntervalIntegrable centralIntegrand volume (lo : ℝ) (hi : ℝ) :=
  IntegralClaim.chain_integrable hc (centralClaims_integrable leaves)

theorem denominatorBlock_integrable (leaves : List CheckedDenominatorLeaf)
    {lo hi : ℚ} (hc : IntegralClaim.chainCheck lo hi (denominatorClaims leaves) = true) :
    IntervalIntegrable denominatorIntegrand volume (lo : ℝ) (hi : ℝ) :=
  IntegralClaim.chain_integrable hc (denominatorClaims_integrable leaves)

theorem profileBlock_lower {mode : Fin 20} (leaves : List (CheckedProfileLeaf mode))
    {lo hi : ℚ} {amount : ℤ}
    (hc : IntegralClaim.chainCheck lo hi (profileClaims leaves) = true)
    (hs : IntegralClaim.total (profileClaims leaves) = amount)
    (ha : ∀ leaf ∈ leaves, leaf.val.geometry.val.Approximation) :
    (((amount : ℚ)/fixedScale-2*approximationError*(hi-lo) : ℚ) : ℝ) ≤
      ∫ t in (lo : ℝ)..(hi : ℝ), profileIntegrand mode t := by
  rw [← hs]
  apply IntegralClaim.lower_bound_rat hc (profileClaims_integrable leaves)
  intro c hcmem
  rcases List.mem_map.mp hcmem with ⟨leaf,hleaf,rfl⟩
  exact leaf.val.sound mode leaf.property (ha leaf hleaf)

theorem centralBlock_lower (leaves : List CheckedCentralLeaf)
    {lo hi : ℚ} {amount : ℤ}
    (hc : IntegralClaim.chainCheck lo hi (centralClaims leaves) = true)
    (hs : IntegralClaim.total (centralClaims leaves) = amount)
    (ha : ∀ leaf ∈ leaves, leaf.val.geometry.val.Approximation) :
    (((amount : ℚ)/fixedScale-2*approximationError*(hi-lo) : ℚ) : ℝ) ≤
      ∫ t in (lo : ℝ)..(hi : ℝ), centralIntegrand t := by
  rw [← hs]
  apply IntegralClaim.lower_bound_rat hc (centralClaims_integrable leaves)
  intro c hcmem
  rcases List.mem_map.mp hcmem with ⟨leaf,hleaf,rfl⟩
  exact leaf.val.sound leaf.property (ha leaf hleaf)

theorem denominatorBlock_upper (leaves : List CheckedDenominatorLeaf)
    {lo hi : ℚ} {amount : ℤ}
    (hc : IntegralClaim.chainCheck lo hi (denominatorClaims leaves) = true)
    (hs : IntegralClaim.total (denominatorClaims leaves) = amount)
    (ha : ∀ leaf ∈ leaves, leaf.val.geometry.val.Approximation) :
    (∫ t in (lo : ℝ)..(hi : ℝ), denominatorIntegrand t) ≤
      (((amount : ℚ)/fixedScale+4*approximationError*(hi-lo) : ℚ) : ℝ) := by
  rw [← hs]
  apply IntegralClaim.upper_bound_rat hc (denominatorClaims_integrable leaves)
  intro c hcmem
  rcases List.mem_map.mp hcmem with ⟨leaf,hleaf,rfl⟩
  exact leaf.val.sound leaf.property (ha leaf hleaf)

end ErdosOverlap.FrontierLeaves
