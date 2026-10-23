/- AI-assisted formalization under repository Apache-2.0.
Development source; exact-source verification is recorded separately. Actual bounded materialized augmentation loop.
A common input denominator earns a positive quantum, giving finite fuel from
source capacity. The bound is pseudopolynomial, not capacity-independent or a
polynomial bit-runtime claim. No target max-flow theorem is assumed. -/
module
public import RationalTableAugmentation
public import RationalFlowLattice
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalTableFlowInvariant {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (D : ℕ) : Prop :=
  (∀ u v, rationalFlowTableEntry F u v ≤ rationalFlowTableEntry C u v) ∧
  (∀ u v, rationalFlowTableEntry F u v = -rationalFlowTableEntry F v u) ∧
  (∀ u, u ≠ s → u ≠ t → (∑ v, rationalFlowTableEntry F u v) = 0) ∧
  ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry F u v)

def rationalTableFlowValue {n : ℕ} (F : RationalFlowTable n) (s : Fin n) : ℚ :=
  ∑ v, rationalFlowTableEntry F s v

def rationalTableFlowUpper {n : ℕ} (C : RationalFlowTable n) (s : Fin n) : ℚ :=
  ∑ v, rationalFlowTableEntry C s v

theorem rational_table_flow_source_upper {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (D : ℕ) (hF : RationalTableFlowInvariant C F s t D) :
    rationalTableFlowValue F s ≤ rationalTableFlowUpper C s :=
  Finset.sum_le_sum (fun v _ => hF.1 s v)

theorem rational_table_augmentation_lattice {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (D : ℕ)
    (hC : ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry C u v))
    (hF : ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry F u v))
    (out : RationalAugmentResult n) (ho : rationalAugmentOnce C F s t = some out) :
    RationalDenominatorLattice D out.amount ∧
      ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry out.flow u v) := by
  obtain ⟨_, _, _, hm, hflow⟩ := rational_augment_once_origin C F s t out ho
  have hδ := rational_path_bottleneck_lattice D (rationalFlowTableEntry C)
    (rationalFlowTableEntry F) hC hF s out.path.tail out.amount hm
  refine ⟨hδ, ?_⟩
  intro u v
  rw [hflow, rational_table_push_path_entry]
  exact rational_net_push_path_lattice D (rationalFlowTableEntry F) hF s
    out.path.tail out.amount hδ u v

theorem rational_table_augmentation_invariant {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (D : ℕ)
    (hC : ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry C u v))
    (hF : RationalTableFlowInvariant C F s t D)
    (out : RationalAugmentResult n) (ho : rationalAugmentOnce C F s t = some out) :
    RationalTableFlowInvariant C out.flow s t D := by
  obtain ⟨_, hs, hc, hcons, _⟩ := rational_augment_once_sound C F s t out hF.1 hF.2.1 ho
  refine ⟨hc, hs, ?_, (rational_table_augmentation_lattice C F s t D hC hF.2.2.2 out ho).2⟩
  intro u hus hut
  exact (hcons u hus hut).trans (hF.2.2.1 u hus hut)

theorem rational_table_augmentation_quantum {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (D : ℕ) (hD : 0 < D)
    (hC : ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry C u v))
    (hF : RationalTableFlowInvariant C F s t D)
    (out : RationalAugmentResult n) (ho : rationalAugmentOnce C F s t = some out) :
    (1 : ℚ) ≤ (D : ℚ) *
      (rationalTableFlowValue out.flow s - rationalTableFlowValue F s) := by
  obtain ⟨hpos, _, _, _, hvalue⟩ := rational_augment_once_sound C F s t out hF.1 hF.2.1 ho
  have hlat := (rational_table_augmentation_lattice C F s t D hC hF.2.2.2 out ho).1
  have hδ := rational_lattice_positive_step D hD out.amount hlat hpos
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hmul : (1 : ℚ) ≤ out.amount * (D : ℚ) := (div_le_iff₀ hDq).mp hδ
  change (∑ v, rationalFlowTableEntry out.flow s v) =
    (∑ v, rationalFlowTableEntry F s v) + out.amount at hvalue
  unfold rationalTableFlowValue
  nlinarith

/-- Public structural recursion constructs a state transformer. Only a Some
branch applies the continuation to a newly materialized table. -/
def rationalTableFlowIterate {n : ℕ} (C : RationalFlowTable n) (s t : Fin n)
    (fuel : ℕ) (F : RationalFlowTable n) : RationalFlowTable n :=
  Nat.rec (motive := fun _ => RationalFlowTable n → RationalFlowTable n)
    (fun current => current)
    (fun _ ih current => Option.rec current (fun out => ih out.flow)
      (rationalAugmentOnce C current s t)) fuel F

theorem rational_table_flow_iterate_zero {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) : rationalTableFlowIterate C s t 0 F = F := rfl

theorem rational_table_flow_iterate_succ {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (fuel : ℕ) :
    rationalTableFlowIterate C s t (fuel + 1) F =
      Option.rec F (fun out => rationalTableFlowIterate C s t fuel out.flow)
        (rationalAugmentOnce C F s t) := rfl

/-- Termination certificate follows the EXECUTED option-returning updates.
Its strict budget premise is a source-capacity arithmetic bound, not an assumed
absence of paths, progress hypothesis or desired target theorem. -/
theorem rational_table_flow_iterate_stops {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (D : ℕ) (hD : 0 < D)
    (hC : ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry C u v))
    (fuel : ℕ) (F : RationalFlowTable n)
    (hF : RationalTableFlowInvariant C F s t D)
    (hbudget : (D : ℚ) * (rationalTableFlowUpper C s - rationalTableFlowValue F s) < (fuel : ℚ)) :
    RationalTableFlowInvariant C (rationalTableFlowIterate C s t fuel F) s t D ∧
      rationalAugmentOnce C (rationalTableFlowIterate C s t fuel F) s t = none := by
  induction fuel generalizing F with
  | zero =>
    have hu := rational_table_flow_source_upper C F s t D hF
    have hDq : (0 : ℚ) ≤ (D : ℚ) := by positivity
    have hn := mul_nonneg hDq (sub_nonneg.mpr hu)
    norm_num only [Nat.cast_zero] at hbudget
    exact False.elim ((not_lt_of_ge hn) hbudget)
  | succ fuel ih =>
    rw [rational_table_flow_iterate_succ]
    cases ho : rationalAugmentOnce C F s t with
    | none => exact ⟨hF, ho⟩
    | some out =>
      have hnew := rational_table_augmentation_invariant C F s t D hC hF out ho
      have hstep := rational_table_augmentation_quantum C F s t D hD hC hF out ho
      have hb : (D : ℚ) *
          (rationalTableFlowUpper C s - rationalTableFlowValue out.flow s) < (fuel : ℚ) := by
        push_cast at hbudget
        nlinarith
      exact ih out.flow hnew hb

def rationalZeroFlowTable (n : ℕ) : RationalFlowTable n :=
  Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0))

theorem rational_zero_flow_table_entry {n : ℕ} (u v : Fin n) :
    rationalFlowTableEntry (rationalZeroFlowTable n) u v = 0 := by
  simp only [rationalFlowTableEntry, rationalZeroFlowTable, cached_vector_get_ofFn]

theorem rational_zero_flow_table_invariant {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (D : ℕ) (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    RationalTableFlowInvariant C (rationalZeroFlowTable n) s t D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v; simpa only [rational_zero_flow_table_entry] using hC u v
  · intro u v; simp only [rational_zero_flow_table_entry, neg_zero]
  · intro u _ _; simp only [rational_zero_flow_table_entry, Finset.sum_const_zero]
  · intro u v; rw [rational_zero_flow_table_entry]; exact rational_lattice_zero D

/-- Explicit input-derived finite fuel. Its possible exponential magnitude in
binary input size is intentional and is not a polynomial iteration guarantee. -/
def rationalTableFlowFuel {n : ℕ} (C : RationalFlowTable n) (s : Fin n) : ℕ :=
  Nat.floor ((rationalCapacityDenominator (rationalFlowTableEntry C) : ℚ) *
    rationalTableFlowUpper C s) + 1

def rationalTableFindFlow {n : ℕ} (C : RationalFlowTable n) (s t : Fin n) :
    RationalFlowTable n :=
  rationalTableFlowIterate C s t (rationalTableFlowFuel C s) (rationalZeroFlowTable n)

theorem rational_table_find_flow_stops {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    RationalTableFlowInvariant C (rationalTableFindFlow C s t) s t
      (rationalCapacityDenominator (rationalFlowTableEntry C)) ∧
      rationalAugmentOnce C (rationalTableFindFlow C s t) s t = none := by
  apply rational_table_flow_iterate_stops C s t
    (rationalCapacityDenominator (rationalFlowTableEntry C))
    (rational_capacity_denominator_positive _) (rational_capacity_lattice _)
    (rationalTableFlowFuel C s) (rationalZeroFlowTable n)
    (rational_zero_flow_table_invariant C s t _ hC)
  have hf := Nat.lt_floor_add_one
    ((rationalCapacityDenominator (rationalFlowTableEntry C) : ℚ) * rationalTableFlowUpper C s)
  simpa only [rationalTableFlowFuel, rationalTableFlowValue,
    rational_zero_flow_table_entry, Finset.sum_const_zero, sub_zero,
    Nat.cast_add, Nat.cast_one] using hf

end SparseCompletion
