/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Actual bounded iteration of the rational FM
kernel/deletion program. Initial support cardinality is structural fuel.
No supplied runtime kernel, polynomial LP/bit cost, or paper-specific feature
instantiation is assumed. Earlier reviewed kernel/dimension files are unchanged. -/
module
public import ProtectedSources.RationalFeatureDimension
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalFeaturePreservation {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q v : Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = ∑ i, q i ∧
    (∀ a, (∑ i, v i * A a i) = ∑ i, q i * A a i) ∧
    ∀ i, q i = 0 → v i = 0

theorem rational_feature_preservation_refl {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i) :
    RationalFeaturePreservation A q q :=
  ⟨hq, rfl, fun _ => rfl, fun _ h => h⟩

theorem rational_feature_preservation_trans {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q v w : Fin m → ℚ)
    (hqv : RationalFeaturePreservation A q v)
    (hvw : RationalFeaturePreservation A v w) :
    RationalFeaturePreservation A q w :=
  ⟨hvw.1, hvw.2.1.trans hqv.2.1,
    fun a => (hvw.2.2.1 a).trans (hqv.2.2.1 a),
    fun i hi => hvw.2.2.2 i (hqv.2.2.2 i hi)⟩

theorem rational_feature_preservation_support {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q v : Fin m → ℚ)
    (h : RationalFeaturePreservation A q v) :
    rationalWeightSupport v ⊆ rationalWeightSupport q := by
  intro i hi
  have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  intro hqi
  exact hvi (h.2.2.2 i hqi)

/-- The fallback is the unchanged input, making the program total even on
invalid inputs. For nonnegative inputs above the dimension threshold, the
dimension theorem proves the actual kernel call succeeds, excluding fallback.
No later LP call is made after the support has reached the threshold. -/
def rationalFeatureReduceStep {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Fin m → ℚ) : Fin m → ℚ :=
  if (rationalWeightSupport q).card ≤ d then q
  else Option.rec q (fun v => v) (rationalFeatureKernelDelete A q)

theorem rational_feature_reduce_step_done {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ)
    (hc : (rationalWeightSupport q).card ≤ d) :
    rationalFeatureReduceStep A q = q := by
  simp only [rationalFeatureReduceStep, ite_eq_left hc]

theorem rational_feature_reduce_step_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i = 1) :
    RationalFeaturePreservation A q (rationalFeatureReduceStep A q) ∧
      (rationalWeightSupport (rationalFeatureReduceStep A q)).card ≤
        (rationalWeightSupport q).card ∧
      (d < (rationalWeightSupport q).card →
        (rationalWeightSupport (rationalFeatureReduceStep A q)).card <
          (rationalWeightSupport q).card) := by
  by_cases hc : (rationalWeightSupport q).card ≤ d
  · rw [rational_feature_reduce_step_done A q hc]
    refine ⟨rational_feature_preservation_refl A q hq, le_rfl, ?_⟩
    intro hgt
    exact False.elim ((Nat.not_lt_of_ge hc) hgt)
  · have hgt : d < (rationalWeightSupport q).card := Nat.lt_of_not_ge hc
    obtain ⟨v, hv, hnonneg, hsum, hmom, hzero, hcard⟩ :=
      rational_feature_computed_deletion_above_dimension A q hq a₀ hmass hgt
    have hstep : rationalFeatureReduceStep A q = v := by
      simp only [rationalFeatureReduceStep, ite_eq_right hc, hv]
    rw [hstep]
    exact ⟨⟨hnonneg, hsum, hmom, hzero⟩, le_of_lt hcard, fun _ => hcard⟩

def rationalFeatureIterates {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Fin m → ℚ) (fuel : ℕ) : Fin m → ℚ :=
  Nat.rec q (fun _ previous => rationalFeatureReduceStep A previous) fuel

theorem rational_feature_iterates_zero {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) :
    rationalFeatureIterates A q 0 = q := rfl

theorem rational_feature_iterates_succ {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (fuel : ℕ) :
    rationalFeatureIterates A q (Nat.succ fuel) =
      rationalFeatureReduceStep A (rationalFeatureIterates A q fuel) := rfl

/-- Either the target support is already reached, or every elapsed step has
removed at least one original support point. The progress disjunction is
earned from actual successful deletions, not provided as an oracle argument. -/
theorem rational_feature_iterates_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i = 1) (fuel : ℕ) :
    RationalFeaturePreservation A q (rationalFeatureIterates A q fuel) ∧
      ((rationalWeightSupport (rationalFeatureIterates A q fuel)).card ≤ d ∨
        (rationalWeightSupport (rationalFeatureIterates A q fuel)).card + fuel ≤
          (rationalWeightSupport q).card) := by
  induction fuel with
  | zero =>
    refine ⟨rational_feature_preservation_refl A q hq, Or.inr ?_⟩
    simp only [rational_feature_iterates_zero, Nat.add_zero, le_refl]
  | succ fuel ih =>
    obtain ⟨hprev, hcount⟩ := ih
    have hstep := rational_feature_reduce_step_contract A
      (rationalFeatureIterates A q fuel) hprev.1 a₀ hmass
    constructor
    · rw [rational_feature_iterates_succ]
      exact rational_feature_preservation_trans A q (rationalFeatureIterates A q fuel)
        (rationalFeatureReduceStep A (rationalFeatureIterates A q fuel)) hprev hstep.1
    · by_cases hc : (rationalWeightSupport (rationalFeatureIterates A q fuel)).card ≤ d
      · left
        rw [rational_feature_iterates_succ,
          rational_feature_reduce_step_done A (rationalFeatureIterates A q fuel) hc]
        exact hc
      · right
        have hgt : d < (rationalWeightSupport (rationalFeatureIterates A q fuel)).card :=
          Nat.lt_of_not_ge hc
        have hstrict := hstep.2.2 hgt
        have hremaining := hcount.resolve_left hc
        rw [rational_feature_iterates_succ]
        omega

/-- Actual bounded compressor. Its fuel is the computed input support size,
so no dimension/existence proof is passed to the running program. -/
def rationalFeatureCompress {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Fin m → ℚ) : Fin m → ℚ :=
  rationalFeatureIterates A q (rationalWeightSupport q).card

theorem rational_feature_compress_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i = 1) :
    RationalFeaturePreservation A q (rationalFeatureCompress A q) ∧
      rationalWeightSupport (rationalFeatureCompress A q) ⊆ rationalWeightSupport q ∧
      (rationalWeightSupport (rationalFeatureCompress A q)).card ≤
        min (rationalWeightSupport q).card d := by
  obtain ⟨hpres, hprogress⟩ := rational_feature_iterates_contract A q hq a₀ hmass
    (rationalWeightSupport q).card
  have hp : RationalFeaturePreservation A q (rationalFeatureCompress A q) := hpres
  have hs := rational_feature_preservation_support A q (rationalFeatureCompress A q) hp
  have hc : (rationalWeightSupport (rationalFeatureCompress A q)).card ≤ d := by
    rcases hprogress with hdone | hcount
    · exact hdone
    · change (rationalWeightSupport (rationalFeatureCompress A q)).card +
        (rationalWeightSupport q).card ≤ (rationalWeightSupport q).card at hcount
      omega
  exact ⟨hp, hs, Nat.le_min.mpr ⟨Finset.card_le_card hs, hc⟩⟩

def rationalFeatureAdjoinMass {d m : ℕ} (A : Fin d → Fin m → ℚ) :
    Fin (d + 1) → Fin m → ℚ :=
  Fin.cons (α := fun _ => Fin m → ℚ) (fun _ => 1) A

def rationalFeatureCompressWithMass {d m : ℕ} (A : Fin d → Fin m → ℚ)
    (q : Fin m → ℚ) : Fin m → ℚ :=
  rationalFeatureCompress (rationalFeatureAdjoinMass A) q

/-- Arbitrary features use an explicit extra mass coordinate. This gives d+1,
while the separate constant-feature contract above gives the sharper d. -/
theorem rational_feature_compress_with_mass_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i) :
    RationalFeaturePreservation A q (rationalFeatureCompressWithMass A q) ∧
      rationalWeightSupport (rationalFeatureCompressWithMass A q) ⊆
        rationalWeightSupport q ∧
      (rationalWeightSupport (rationalFeatureCompressWithMass A q)).card ≤
        min (rationalWeightSupport q).card (d + 1) := by
  obtain ⟨hp, hs, hc⟩ := rational_feature_compress_contract
    (rationalFeatureAdjoinMass A) q hq 0 (fun _ => rfl)
  refine ⟨⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩, hs, hc⟩
  intro a
  simpa only [rationalFeatureCompressWithMass, rationalFeatureAdjoinMass, Fin.cons_succ] using hp.2.2.1 a.succ

end SparseCompletion
