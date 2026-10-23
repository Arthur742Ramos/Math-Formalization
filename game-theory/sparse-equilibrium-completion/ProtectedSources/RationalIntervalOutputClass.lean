/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalValue
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def rationalIntervalOutputData {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ) : IntervalGameData k m :=
  (fun i => (intervalQ (α := ℚ) x i : ℝ),
    fun i a => (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ),
    fun a b => (intervalK (α := ℚ) x a b : ℝ),fun i j => (B i j : ℝ))

theorem rational_interval_output_physical {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hV : ∀ i a, d.lo i a*intervalQ (α := ℚ) x i ≤ intervalV (α := ℚ) x i a ∧
      intervalV (α := ℚ) x i a ≤ d.hi i a*intervalQ (α := ℚ) x i) :
    intervalGamePhysical (rationalIntervalOutputData d x B)=
      fun j => (intervalPhysicalVector (α := ℚ) x j : ℝ) := by
  have hprod := rational_interval_recovered_product d.lo d.hi (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) hV
  funext j
  simp only [interval_physical_projection]
  unfold intervalGamePhysical intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with i | v
  · rfl
  · rcases v with v | v
    · change (intervalQ (α := ℚ) x v.1 : ℝ)*
        (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) v.1 v.2 : ℝ)=(intervalV (α := ℚ) x v.1 v.2 : ℝ)
      exact_mod_cast hprod v.1 v.2
    · rcases v with v | v
      · rfl
      · exact Fin.elim0 v.1

theorem rational_interval_algorithm_output_class {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ρ : ℚ)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r ρ d.η d.R=some (x,B)) :
    rationalIntervalOutputData d x B ∈ intervalGameClass d := by
  obtain ⟨hpoint,hR,hB⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
    d.p d.M d.r ρ d.η d.R x B hout
  have hsave := hpoint
  obtain ⟨hq,hm,hV,hK,hKb,_⟩ := hsave
  have hD := (rational_interval_gap_recovered _ d.lo d.hi _ d.p _ d.M d.r ρ d.η d.orderedCross
    (rational_interval_point_gap d.loK d.hiK d.lo d.hi _ _ d.p _ d.M d.r ρ d.η _ hpoint).2.2).1
  have hbR := rational_residual_completion_real_sound (intervalQ (α := ℚ) x)
    (rationalScore (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x)) d.p) d.M (ρ+d.η) B hB
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,hbR.1,hbR.2.1⟩,?_,?_,?_⟩
  · intro i
    change (0 : ℝ) ≤ (intervalQ (α := ℚ) x i : ℝ)
    exact_mod_cast hq i
  · intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hq j)
      (Finset.mem_univ i)
    rw [hm] at hi
    change (intervalQ (α := ℚ) x i : ℝ) ≤ (d.r : ℝ)
    exact_mod_cast hi
  · intro i a
    change (d.lo i a : ℝ) ≤ (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ)
    exact_mod_cast (hD i a).1
  · intro i a
    change (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ) ≤ (d.hi i a : ℝ)
    exact_mod_cast (hD i a).2
  · intro a b
    change (d.loK a b : ℝ) ≤ (intervalK (α := ℚ) x a b : ℝ)
    exact_mod_cast (hKb a b).1
  · intro a b
    change (intervalK (α := ℚ) x a b : ℝ) ≤ (d.hiK a b : ℝ)
    exact_mod_cast (hKb a b).2
  · change (∑ i, (intervalQ (α := ℚ) x i : ℝ))=(d.r : ℝ)
    exact_mod_cast hm
  · intro a b
    change (intervalK (α := ℚ) x a b : ℝ)= -(intervalK (α := ℚ) x b a : ℝ)
    exact_mod_cast hK a b
  · rw [rational_interval_output_physical d x B hV]
    exact (rational_linear_real_cast_iff d.R _).mpr hR

end
end SparseCompletion
