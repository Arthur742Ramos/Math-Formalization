/- AI-assisted formalization under the repository Apache-2.0 license.
Separate source draft. Actual Gaussian deletion with materialized vector states.
No coefficient-height, operation-cost, bit-cost or polynomial-runtime theorem.
Frozen FM/paper modules remain unchanged; FM in imports is not a runtime call. -/
module
public import ProtectedSources.RationalGaussianFeature
public import ProtectedSources.RationalFeatureIterate
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Every successful Gaussian deletion is materialized before it becomes the
next state. The total fallback keeps the input vector; above dimension the
existing proved Gaussian completeness theorem excludes that fallback. -/
def rationalGaussianReduceVector {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Gaussian.QVec m) : Gaussian.QVec m :=
  if (rationalWeightSupport q.get).card ≤ d then q
  else Option.rec q List.Vector.ofFn (rationalGaussianFeatureDelete A q.get)

theorem rational_gaussian_reduce_vector_done {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Gaussian.QVec m)
    (hc : (rationalWeightSupport q.get).card ≤ d) :
    rationalGaussianReduceVector A q=q := by
  simp only [rationalGaussianReduceVector, ite_eq_left hc]

theorem rational_gaussian_reduce_vector_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Gaussian.QVec m)
    (hq : ∀ i, 0 ≤ q.get i) (a₀ : Fin d) (hmass : ∀ i, A a₀ i=1) :
    RationalFeaturePreservation A q.get (rationalGaussianReduceVector A q).get ∧
      (rationalWeightSupport (rationalGaussianReduceVector A q).get).card ≤
        (rationalWeightSupport q.get).card ∧
      (d < (rationalWeightSupport q.get).card →
        (rationalWeightSupport (rationalGaussianReduceVector A q).get).card <
          (rationalWeightSupport q.get).card) := by
  by_cases hc : (rationalWeightSupport q.get).card ≤ d
  · rw [rational_gaussian_reduce_vector_done A q hc]
    refine ⟨rational_feature_preservation_refl A q.get hq, le_rfl, ?_⟩
    intro hgt
    exact False.elim ((Nat.not_lt_of_ge hc) hgt)
  · have hgt : d < (rationalWeightSupport q.get).card := Nat.lt_of_not_ge hc
    obtain ⟨v, hv, hn, hs, hm, hz, hcard⟩ :=
      rational_gaussian_deletion_above_dimension A q.get hq a₀ hmass hgt
    have hstep : rationalGaussianReduceVector A q=List.Vector.ofFn v := by
      simp only [rationalGaussianReduceVector, ite_eq_right hc, hv]
    rw [hstep]
    simpa only [Gaussian.vecGet_ofFn] using
      (show RationalFeaturePreservation A q.get v ∧
        (rationalWeightSupport v).card ≤ (rationalWeightSupport q.get).card ∧
        (d < (rationalWeightSupport q.get).card →
          (rationalWeightSupport v).card < (rationalWeightSupport q.get).card) from
        ⟨⟨hn, hs, hm, hz⟩, le_of_lt hcard, fun _ => hcard⟩)

def rationalGaussianVectorIterates {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Gaussian.QVec m) (fuel : ℕ) : Gaussian.QVec m :=
  Nat.rec q (fun _ previous => rationalGaussianReduceVector A previous) fuel

theorem rational_gaussian_vector_iterates_zero {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Gaussian.QVec m) :
    rationalGaussianVectorIterates A q 0=q := rfl

theorem rational_gaussian_vector_iterates_succ {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Gaussian.QVec m) (fuel : ℕ) :
    rationalGaussianVectorIterates A q (Nat.succ fuel)=
      rationalGaussianReduceVector A (rationalGaussianVectorIterates A q fuel) := rfl

theorem rational_gaussian_vector_iterates_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Gaussian.QVec m)
    (hq : ∀ i, 0 ≤ q.get i) (a₀ : Fin d) (hmass : ∀ i, A a₀ i=1) (fuel : ℕ) :
    RationalFeaturePreservation A q.get (rationalGaussianVectorIterates A q fuel).get ∧
      ((rationalWeightSupport (rationalGaussianVectorIterates A q fuel).get).card ≤ d ∨
        (rationalWeightSupport (rationalGaussianVectorIterates A q fuel).get).card+fuel ≤
          (rationalWeightSupport q.get).card) := by
  induction fuel with
  | zero =>
    refine ⟨rational_feature_preservation_refl A q.get hq, Or.inr ?_⟩
    simp only [rational_gaussian_vector_iterates_zero, Nat.add_zero, le_refl]
  | succ fuel ih =>
    obtain ⟨hprev, hcount⟩ := ih
    have hstep := rational_gaussian_reduce_vector_contract A
      (rationalGaussianVectorIterates A q fuel) hprev.1 a₀ hmass
    constructor
    · rw [rational_gaussian_vector_iterates_succ]
      exact rational_feature_preservation_trans A q.get
        (rationalGaussianVectorIterates A q fuel).get
        (rationalGaussianReduceVector A (rationalGaussianVectorIterates A q fuel)).get
        hprev hstep.1
    · by_cases hc : (rationalWeightSupport (rationalGaussianVectorIterates A q fuel).get).card ≤ d
      · left
        rw [rational_gaussian_vector_iterates_succ,
          rational_gaussian_reduce_vector_done A (rationalGaussianVectorIterates A q fuel) hc]
        exact hc
      · right
        have hgt : d < (rationalWeightSupport (rationalGaussianVectorIterates A q fuel).get).card :=
          Nat.lt_of_not_ge hc
        have hstrict := hstep.2.2 hgt
        have hremaining := hcount.resolve_left hc
        rw [rational_gaussian_vector_iterates_succ]
        omega

/-- Fully materialized actual Gaussian compressor. Initial positive-support
cardinality is its sole fuel; no numerical payoff or denominator fuel is used. -/
def rationalGaussianCompressVector {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Fin m → ℚ) : Gaussian.QVec m :=
  rationalGaussianVectorIterates A (List.Vector.ofFn q) (rationalWeightSupport q).card

theorem rational_gaussian_compress_vector_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i=1) :
    RationalFeaturePreservation A q (rationalGaussianCompressVector A q).get ∧
      rationalWeightSupport (rationalGaussianCompressVector A q).get ⊆ rationalWeightSupport q ∧
      (rationalWeightSupport (rationalGaussianCompressVector A q).get).card ≤
        min (rationalWeightSupport q).card d := by
  obtain ⟨hpres, hprogress⟩ := rational_gaussian_vector_iterates_contract A
    (List.Vector.ofFn q) (by simpa only [Gaussian.vecGet_ofFn] using hq) a₀ hmass
    (rationalWeightSupport q).card
  simp only [Gaussian.vecGet_ofFn] at hpres hprogress
  have hp : RationalFeaturePreservation A q (rationalGaussianCompressVector A q).get := hpres
  have hs := rational_feature_preservation_support A q (rationalGaussianCompressVector A q).get hp
  have hc : (rationalWeightSupport (rationalGaussianCompressVector A q).get).card ≤ d := by
    rcases hprogress with hdone | hcount
    · exact hdone
    · change (rationalWeightSupport (rationalGaussianCompressVector A q).get).card+
        (rationalWeightSupport q).card ≤ (rationalWeightSupport q).card at hcount
      omega
  exact ⟨hp, hs, Nat.le_min.mpr ⟨Finset.card_le_card hs, hc⟩⟩

theorem rational_gaussian_compress_iteration_fuel_le {m : ℕ}
    (q : Fin m → ℚ) :
    (rationalWeightSupport q).card ≤ m := by
  exact le_trans (Finset.card_filter_le _ _) (by simp)

def rationalGaussianCompressVectorWithMass {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Fin m → ℚ) : Gaussian.QVec m :=
  rationalGaussianCompressVector (rationalFeatureAdjoinMass A) q

theorem rational_gaussian_compress_vector_with_mass_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i) :
    RationalFeaturePreservation A q (rationalGaussianCompressVectorWithMass A q).get ∧
      rationalWeightSupport (rationalGaussianCompressVectorWithMass A q).get ⊆ rationalWeightSupport q ∧
      (rationalWeightSupport (rationalGaussianCompressVectorWithMass A q).get).card ≤
        min (rationalWeightSupport q).card (d+1) := by
  obtain ⟨hp, hs, hc⟩ := rational_gaussian_compress_vector_contract
    (rationalFeatureAdjoinMass A) q hq 0 (fun _ => rfl)
  refine ⟨⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩, hs, hc⟩
  intro a
  simpa only [rationalGaussianCompressVectorWithMass, rationalFeatureAdjoinMass, Fin.cons_succ] using
    hp.2.2.1 a.succ

end SparseCompletion
