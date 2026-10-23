/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalValue
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_game_class_of_witness {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (hq : ∀ i,0 ≤ q i) (hm : (∑ i,q i)=(d.r : ℝ)) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (hDI : ∀ i a,(d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ))
    (hB : IsSkew B) (hBI : ∀ i l,-(d.M : ℝ) ≤ B i l ∧ B i l ≤ (d.M : ℝ))
    (hR : d.R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)) :
    (q,D,K,B) ∈ intervalGameClass d := by
  refine ⟨⟨⟨hq,?_⟩,⟨fun i a => (hDI i a).1,fun i a => (hDI i a).2⟩,
    ⟨fun a b => (hKI a b).1,fun a b => (hKI a b).2⟩,hB,hBI⟩,hm,hK,hR⟩
  intro i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hq j)
    (Finset.mem_univ i)
  rwa [hm] at hi

end
end SparseCompletion
