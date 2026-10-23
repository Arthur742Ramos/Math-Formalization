/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalIntervalSparseConditions
public import ProtectedSources.RationalSparseGapGame
public import ProtectedSources.RationalIntervalWitnessClass
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_sparse_algorithm_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ρ : ℚ)
    (q : Fin m → ℚ) (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r ρ d.η d.R=
      some (q,(K,(D,B)))) :
    ((fun i => (q i : ℝ)),(fun i a => (D i a : ℝ)),
      (fun a b => (K a b : ℝ)),(fun i j => (B i j : ℝ))) ∈ intervalGameClass d ∧
    (∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun a => (d.p a : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(d.η : ℝ)) ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize d.M d.r d.η+Fintype.card I+1) := by
  rcases rational_interval_sparse_algorithm_conditions d.loK d.hiK d.lo d.hi d.p d.M d.r
    ρ d.η d.R d.orderedCross q K D B hout with ⟨hR,hK,hKI,hDI,hg,hB,hc⟩
  have hBreal := (residual_rat_real_iff q (rationalScore D d.p) d.M (ρ+d.η) B).mp hB
  have hRR := (rational_linear_real_cast_iff d.R
    (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)).mpr hR
  have hpack : (fun j => (intervalPack (α := ℚ) q (fun i a => q i*D i a) K (H := 0) Fin.elim0 j : ℝ))=
      intervalPack (fun i => (q i : ℝ)) (fun i a => (q i : ℝ)*(D i a : ℝ))
        (fun a b => (K a b : ℝ)) (H := 0) Fin.elim0 := by
    funext j
    unfold intervalPack intervalVariableEncode
    generalize (rationalIntervalVariableEquiv k m 0).symm j=v
    rcases v with i | v
    · rfl
    · rcases v with a | v
      · exact Rat.cast_mul _ _
      · rcases v with a | a
        · rfl
        · exact Fin.elim0 a.1
  rw [hpack] at hRR
  have hclass := interval_game_class_of_witness d (fun i => (q i : ℝ))
    (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ)) (fun i j => (B i j : ℝ))
    (fun i => by exact_mod_cast hg.1 i) (by exact_mod_cast hg.2.1)
    (fun a b => by change (K a b : ℝ)= -(K b a : ℝ); exact_mod_cast hK a b)
    (fun a b => by exact_mod_cast hKI a b) (fun i a => by exact_mod_cast hDI i a)
    hBreal.1 hBreal.2.1 hRR
  obtain ⟨_,_,_,_,_,hs⟩ := rational_interval_sparse_algorithm_origin d.loK d.hiK d.lo d.hi d.p
    d.M d.r ρ d.η d.R q K D B hout
  have hfull := rational_sparse_gap_algorithm_full_game K D d.p q d.M d.r ρ d.η d.positiveSlack
    d.anchorNonneg d.normalized hK
    (fun a b => ⟨le_trans (d.coreLower a b) (hKI a b).1,
      le_trans (hKI a b).2 (d.coreUpper a b)⟩)
    (fun i a => ⟨le_trans (d.crossLower i a) (hDI i a).1,
      le_trans (hDI i a).2 (d.crossUpper i a)⟩)
    (rationalFrozenPhysicalSystem K D d.R) B hs
  exact ⟨hclass,hfull.2.2.2.2,hc⟩

end SparseCompletion
