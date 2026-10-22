/- AI-assisted formalization under the repository Apache-2.0 license.
Attained minimum support for actual anchored completions and both commitments.
This is a noncomputable integer minimum, not a sparse selection algorithm. -/
module
public import GameModel
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def PhysicalAnchoredWitness {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 : Fin k → ℝ) (M ε : ℝ) (fixed : Bool)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
  (∀ h, p0 h ≤ p h) ∧ (fixed=true → p=p0) ∧
  IsSkew (blockMatrix K D B) ∧
  (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
  (∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε)

def physicalAnchoredSupportExists {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 : Fin k → ℝ) (M ε : ℝ) (fixed : Bool) : Prop :=
  ∃ s : ℕ, ∃ p q B, PhysicalAnchoredWitness K D p0 M ε fixed p q B ∧
    (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card=s

theorem physical_anchored_original {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 : Fin k → ℝ) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ) (M ε : ℝ) (fixed : Bool) (hε : 0 ≤ ε)
    (hn : ∀ a, 0 ≤ blockWeights p0 q a) (hm : (∑ a, blockWeights p0 q a)=1)
    (hsk : IsSkew (blockMatrix K D B))
    (hb : ∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M)
    (hr : ∀ a, response (blockMatrix K D B) (blockWeights p0 q) a ≤ 0) :
    PhysicalAnchoredWitness K D p0 M ε fixed p0 q B := by
  exact ⟨hn,hm,fun _ => le_refl _,fun _ => rfl,hsk,hb,fun a => le_trans (hr a) hε⟩

theorem physical_anchored_support_exists {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 p : Fin k → ℝ) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ) (M ε : ℝ) (fixed : Bool)
    (hw : PhysicalAnchoredWitness K D p0 M ε fixed p q B) :
    physicalAnchoredSupportExists K D p0 M ε fixed := by
  exact ⟨_,p,q,B,hw,rfl⟩

def physicalMinimumSupport {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 : Fin k → ℝ) (M ε : ℝ) (fixed : Bool)
    (hne : physicalAnchoredSupportExists K D p0 M ε fixed) : ℕ := by
  classical
  exact Nat.find hne

theorem physicalMinimumSupport_attained {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 : Fin k → ℝ) (M ε : ℝ) (fixed : Bool)
    (hne : physicalAnchoredSupportExists K D p0 M ε fixed) :
    ∃ p q B, PhysicalAnchoredWitness K D p0 M ε fixed p q B ∧
      (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card=
        physicalMinimumSupport K D p0 M ε fixed hne := by
  classical
  exact Nat.find_spec hne

theorem physicalMinimumSupport_le {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 : Fin k → ℝ) (M ε : ℝ) (fixed : Bool)
    (hne : physicalAnchoredSupportExists K D p0 M ε fixed)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hw : PhysicalAnchoredWitness K D p0 M ε fixed p q B) :
    physicalMinimumSupport K D p0 M ε fixed hne ≤
      (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card := by
  classical
  exact Nat.find_min' hne ⟨p,q,B,hw,rfl⟩

theorem physicalMinimumSupport_finite_bound {k m : ℕ} (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (p0 : Fin k → ℝ) (M ε : ℝ) (fixed : Bool)
    (hne : physicalAnchoredSupportExists K D p0 M ε fixed) :
    physicalMinimumSupport K D p0 M ε fixed hne ≤ k+m := by
  classical
  obtain ⟨p,q,B,_,hc⟩ := physicalMinimumSupport_attained K D p0 M ε fixed hne
  rw [←hc]
  exact le_trans (Finset.card_filter_le _ _) (by simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]; exact le_rfl)

end
end SparseCompletion
