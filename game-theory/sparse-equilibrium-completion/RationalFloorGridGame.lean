/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalFloorGridPhysical
public import RationalIntervalWitnessClass
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_game {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ)
    (u : Fin m → ℚ) (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i)
    (hR : d.R=rationalResidualFloors u)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (hsp : ∀ a,(s a : ℝ) ≤ p a) (huq : ∀ i,(u i : ℝ) ≤ q i)
    (hmass : (∑ a,p a)+(∑ i,q i)=1) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (hDI : ∀ i a,(d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ))
    (hB : IsSkew B) (hBI : ∀ i l,-(d.M : ℝ) ≤ B i l ∧ B i l ≤ (d.M : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      ∃ h : ∀ a,s a ≤ rationalAnchorAllocation s δ z a,
        ∃ hc : (d.withAllocation (rationalAnchorAllocation s δ z)
          (fun a => le_trans (hs a) (h a))).Compatible,
          ∃ q' : Fin m → ℝ,
            (q',D,K,B) ∈ intervalGameClass
              ((d.withAllocation (rationalAnchorAllocation s δ z)
                (fun a => le_trans (hs a) (h a))).toModel hc) ∧
            exploitability (blockMatrix K D B)
              (blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q') ≤
              exploitability (blockMatrix K D B) (blockWeights p q)+
                (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ) := by
  obtain ⟨z,hsz,hz,hc⟩ := rational_floor_grid_compatible d s u hs hu hR
    p q K D B hsp huq hmass hK hKI hDI hB hBI δ hδ j
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  let q' := transferredResidual q
    (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j
  have hf := allocation_rounding_preserves_floors (fun a => (s a : ℝ)) p
    (fun i => (u i : ℝ)) q (δ : ℝ) j hsp huq hδR
  have hq' : ∀ i,0 ≤ q' i := fun i => le_trans (by exact_mod_cast hu i) (hf.2 i)
  have hm := allocation_rounding_mass (fun a => (s a : ℝ)) p q (δ : ℝ) j
  have hzsum : (∑ a,(rationalAnchorAllocation s δ z a : ℝ))=
      ∑ a,roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ) a :=
    Finset.sum_congr rfl (fun a _ => hz a)
  have hmq' : (∑ i,q' i)=
      (((d.withAllocation (rationalAnchorAllocation s δ z)
        (fun a => le_trans (hs a) (hsz a))).toModel hc).r : ℝ) := by
    change (∑ i,q' i)=((1-∑ a,rationalAnchorAllocation s δ z a : ℚ) : ℝ)
    push_cast
    change (∑ i,transferredResidual q
      (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j i)=_
    linarith
  have hRq' : d.R.RealSatisfies (intervalPack q' (fun i a => q' i*D i a) K (H := 0) Fin.elim0) := by
    rw [hR,rational_residual_floors_real_pack]
    exact hf.2
  refine ⟨z,hsz,hc,q',interval_game_class_of_witness _ q' K D B
    hq' hmq' hK hKI hDI hB hBI hRq',?_⟩
  have hAb := blockMatrix_bounds K D B (d.M : ℝ)
    (fun a b => ⟨le_trans (by exact_mod_cast d.coreLower a b) (hKI a b).1,
      le_trans (hKI a b).2 (by exact_mod_cast d.coreUpper a b)⟩)
    (fun i a => ⟨le_trans (by exact_mod_cast d.crossLower i a) (hDI i a).1,
      le_trans (hDI i a).2 (by exact_mod_cast d.crossUpper i a)⟩) hBI
  have hE := allocation_rounding_value_bound (fun a => (s a : ℝ)) p q
    (δ : ℝ) (d.M : ℝ) j (blockMatrix K D B) hsp hδR
    (by exact_mod_cast le_of_lt d.positiveBound) (fun a b => abs_le.mpr (hAb a b))
  have hw : blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q'=
      blockWeights (roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ)) q' := by
    funext a
    cases a with
    | inl a => exact hz a
    | inr i => rfl
  rw [hw]
  simpa only [Fintype.card_fin] using hE

end
end SparseCompletion
