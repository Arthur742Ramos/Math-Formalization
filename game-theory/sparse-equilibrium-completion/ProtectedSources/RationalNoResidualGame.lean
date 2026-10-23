/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalReservoirRepresentation
public import ProtectedSources.RationalIntervalWitnessClass
public import ProtectedSources.RationalFloorRepertoire
public import ProtectedSources.RationalAllocationRun
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_no_residual_grid_game {k : ℕ} [Nonempty (Fin k ⊕ Fin 0)]
    (d : RationalIntervalParameters k 0 (Fin 0)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (Fin.elim0 : Fin 0 → ℚ))
    (p : Fin k → ℝ) (hp : p ∈ floorStrategies (fun a => (s a : ℝ)))
    (K : Fin k → Fin k → ℝ) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin k) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      ∃ h : ∀ a,s a ≤ rationalReservoirAllocation s δ j z a,
        ∃ hc : (d.withAllocation (rationalReservoirAllocation s δ j z)
          (fun a => le_trans (hs a) (h a))).Compatible,
          (Fin.elim0,Fin.elim0,K,Fin.elim0) ∈ intervalGameClass
            ((d.withAllocation (rationalReservoirAllocation s δ j z)
              (fun a => le_trans (hs a) (h a))).toModel hc) ∧
          exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
            (blockWeights (fun a => (rationalReservoirAllocation s δ j z a : ℝ)) Fin.elim0) ≤
            exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
              (blockWeights p Fin.elim0)+(2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ) := by
  obtain ⟨z,hz⟩ := rational_reservoir_rounding_enumerated s p δ j hs hp hδ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hsz : ∀ a,s a ≤ rationalReservoirAllocation s δ j z a := by
    intro a
    have hh := reservoir_rounded_floors (fun a => (s a : ℝ)) p (δ : ℝ) j hp.1 hδR a
    rw [←hz] at hh
    change (s a : ℝ) ≤ (rationalReservoirAllocation s δ j z a : ℝ) at hh
    exact_mod_cast hh
  let dz := d.withAllocation (rationalReservoirAllocation s δ j z)
    (fun a => le_trans (hs a) (hsz a))
  have hm : (∑ i : Fin 0,(Fin.elim0 i : ℝ))=(dz.r : ℝ) := by
    change (∑ i : Fin 0,(Fin.elim0 i : ℝ))=((1-∑ a,rationalReservoirAllocation s δ j z a : ℚ) : ℝ)
    rw [rational_reservoir_allocation_mass]
    norm_num
  have hRp : dz.R.RealSatisfies
      (intervalPack (Fin.elim0 : Fin 0 → ℝ)
        (fun (i : Fin 0) (a : Fin k) => (Fin.elim0 i : ℝ)*((Fin.elim0 i : Fin k → ℝ) a)) K (H := 0) Fin.elim0) := by
    change d.R.RealSatisfies _
    rw [hR,rational_residual_floors_real_pack]
    exact fun i => Fin.elim0 i
  have hc : dz.Compatible :=
    ⟨Fin.elim0,K,Fin.elim0,Fin.elim0,(fun i => Fin.elim0 i),hm,hK,hKI,
      (fun i => Fin.elim0 i),(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),hRp⟩
  refine ⟨z,hsz,hc,interval_game_class_of_witness (dz.toModel hc)
    Fin.elim0 K Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) hm hK hKI
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hRp,?_⟩
  let A := blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0
  have hAb := blockMatrix_bounds K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0 (d.M : ℝ)
    (fun a b => ⟨le_trans (by exact_mod_cast d.coreLower a b) (hKI a b).1,
      le_trans (hKI a b).2 (by exact_mod_cast d.coreUpper a b)⟩)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hd : (∑ a : Fin k ⊕ Fin 0,
      |blockWeights p (Fin.elim0 : Fin 0 → ℝ) a-
        blockWeights (fun b => (rationalReservoirAllocation s δ j z b : ℝ)) Fin.elim0 a|) ≤
      (2 : ℕ)*(k : ℝ)*(δ : ℝ) := by
    rw [Fintype.sum_sum_type]
    simp only [blockWeights,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_zero,add_zero]
    simp_rw [show ∀ a,(rationalReservoirAllocation s δ j z a : ℝ)=
      reservoirRounded (fun a => (s a : ℝ)) p (δ : ℝ) j a from fun a => congrFun hz a]
    simpa only [Fintype.card_fin] using
      reservoir_rounded_distance (fun a => (s a : ℝ)) p (δ : ℝ) j hp.1 hδR
  have hh := (abs_le.mp (exploitability_strategy_distance A
    (blockWeights p Fin.elim0)
    (blockWeights (fun b => (rationalReservoirAllocation s δ j z b : ℝ)) Fin.elim0)
    (d.M : ℝ) (fun a b => abs_le.mpr (hAb a b)))).1
  have hdM := mul_le_mul_of_nonneg_left hd (by exact_mod_cast le_of_lt d.positiveBound : 0 ≤ (d.M : ℝ))
  norm_num only [Nat.cast_ofNat] at hdM ⊢
  nlinarith

end
end SparseCompletion
