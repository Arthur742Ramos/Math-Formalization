/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalFloorRepertoire
public import RationalAnchorApproximation
public import RationalAllocationCompleteness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_compatible {k m : ℕ}
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
        (∀ a,(rationalAnchorAllocation s δ z a : ℝ)=
          roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ) a) ∧
        (d.withAllocation (rationalAnchorAllocation s δ z)
          (fun a => le_trans (hs a) (h a))).Compatible := by
  have hp0 : ∀ a,0 ≤ p a := fun a => le_trans (by exact_mod_cast hs a) (hsp a)
  have hq0 : ∀ i,0 ≤ q i := fun i => le_trans (by exact_mod_cast hu i) (huq i)
  have hp1 : ∀ a,p a ≤ 1 := by
    intro a
    have hsingle := Finset.single_le_sum (fun b _ => hp0 b) (Finset.mem_univ a)
    have hqsum : 0 ≤ ∑ i,q i := Finset.sum_nonneg fun i _ => hq0 i
    linarith
  obtain ⟨z,hz⟩ := rational_anchor_rounding_enumerated s p δ hs hp1 hδ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hf := allocation_rounding_preserves_floors (fun a => (s a : ℝ)) p
    (fun i => (u i : ℝ)) q (δ : ℝ) j hsp huq hδR
  have hsz : ∀ a,s a ≤ rationalAnchorAllocation s δ z a := by
    intro a
    have hh := hf.1 a
    rw [←hz a] at hh
    exact_mod_cast hh
  let q' := transferredResidual q
    (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j
  have hm := allocation_rounding_mass (fun a => (s a : ℝ)) p q (δ : ℝ) j
  have hzsum : (∑ a,(rationalAnchorAllocation s δ z a : ℝ))=
      ∑ a,roundedAllocation (fun a => (s a : ℝ)) p (δ : ℝ) a :=
    Finset.sum_congr rfl (fun a _ => hz a)
  refine ⟨z,hsz,hz,q',K,D,B,?_,?_,hK,hKI,hDI,hB,hBI,?_⟩
  · exact fun i => le_trans (by exact_mod_cast hu i) (hf.2 i)
  · change (∑ i,q' i)=((1-∑ a,rationalAnchorAllocation s δ z a : ℚ) : ℝ)
    push_cast
    change (∑ i,transferredResidual q
      (removedAnchorMass (fun a => (s a : ℝ)) p (δ : ℝ)) j i)=_
    linarith
  · change d.R.RealSatisfies (intervalPack q' (fun i a => q' i*D i a) K (H := 0) Fin.elim0)
    rw [hR,rational_residual_floors_real_pack]
    exact hf.2

end
end SparseCompletion
