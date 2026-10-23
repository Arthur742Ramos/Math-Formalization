/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. A fixed rational denominator lattice, its actual
capacity-data denominator, and closure of the executed edge/path updates.
This is a pseudopolynomial stepping foundation, not a flow finder, termination
proof, Edmonds-Karp bound, or primitive/bit/runtime cost claim. -/
module
public import ProtectedSources.RationalPathSaturation
public import ProtectedSources.RationalDenominatorGrowth
public import Mathlib.Tactic
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Exact membership in one shared denominator lattice. Integer witnesses are
proof data only; all path updates and bottleneck computations remain rational
programs from the imported modules. -/
def RationalDenominatorLattice (D : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ) / (D : ℚ)

theorem rational_lattice_zero (D : ℕ) : RationalDenominatorLattice D 0 := by
  exact ⟨0, by simp⟩

theorem rational_lattice_add (D : ℕ) (a b : ℚ)
    (ha : RationalDenominatorLattice D a) (hb : RationalDenominatorLattice D b) :
    RationalDenominatorLattice D (a + b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x + y, ?_⟩
  simp only [hx, hy, Int.cast_add, add_div]

theorem rational_lattice_sub (D : ℕ) (a b : ℚ)
    (ha : RationalDenominatorLattice D a) (hb : RationalDenominatorLattice D b) :
    RationalDenominatorLattice D (a - b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x - y, ?_⟩
  simp only [hx, hy, Int.cast_sub, sub_div]

theorem rational_lattice_neg (D : ℕ) (q : ℚ)
    (hq : RationalDenominatorLattice D q) : RationalDenominatorLattice D (-q) := by
  simpa only [zero_sub] using rational_lattice_sub D 0 q (rational_lattice_zero D) hq

theorem rational_lattice_finset_sum {ι : Type*} (D : ℕ) (s : Finset ι) (q : ι → ℚ)
    (hq : ∀ i ∈ s, RationalDenominatorLattice D (q i)) :
    RationalDenominatorLattice D (∑ i ∈ s, q i) := by
  classical
  revert hq
  induction s using Finset.induction_on with
  | empty =>
    intro hq
    simpa only [Finset.sum_empty] using rational_lattice_zero D
  | @insert a s ha ih =>
    intro hq
    rw [Finset.sum_insert ha]
    exact rational_lattice_add D (q a) (∑ i ∈ s, q i)
      (hq a (Finset.mem_insert_self a s))
      (ih (fun i hi => hq i (Finset.mem_insert_of_mem hi)))

theorem rational_lattice_sum {ι : Type*} [Fintype ι] (D : ℕ) (q : ι → ℚ)
    (hq : ∀ i, RationalDenominatorLattice D (q i)) :
    RationalDenominatorLattice D (∑ i, q i) := by
  exact rational_lattice_finset_sum D Finset.univ q (fun i _ => hq i)

/-- A positive lattice value has at least one unit of the fixed rational mesh.
The positive denominator premise is essential and is not silently assumed. -/
theorem rational_lattice_positive_step (D : ℕ) (hD : 0 < D) (q : ℚ)
    (hq : RationalDenominatorLattice D q) (hpos : 0 < q) :
    (1 : ℚ) / (D : ℚ) ≤ q := by
  obtain ⟨z, hz⟩ := hq
  have hDQ : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hzpos : (0 : ℚ) < (z : ℚ) := by
    apply (div_pos_iff_of_pos_right hDQ).mp
    simpa only [← hz] using hpos
  have hzint : (0 : ℤ) < z := by exact_mod_cast hzpos
  have hzintone : (1 : ℤ) ≤ z := by omega
  have hzone : (1 : ℚ) ≤ (z : ℚ) := by exact_mod_cast hzintone
  rw [hz]
  exact div_le_div_of_nonneg_right hzone (le_of_lt hDQ)

theorem rational_lattice_scaled_integer (D : ℕ) (hD : 0 < D) (q : ℚ)
    (hq : RationalDenominatorLattice D q) :
    ∃ z : ℤ, (D : ℚ) * q = (z : ℚ) := by
  obtain ⟨z, hz⟩ := hq
  refine ⟨z, ?_⟩
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  rw [hz]
  field_simp [hDQ]

/-- Unlike a sum-denominator bound, this says that each actual input
denominator divides the computed common denominator. -/
theorem rational_member_denominator_divides_product (xs : List ℚ) (q : ℚ)
    (hq : q ∈ xs) : q.den ∣ rationalDenominatorProduct xs := by
  revert hq
  induction xs with
  | nil => intro hq; cases hq
  | cons a xs ih =>
    intro hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      exact ⟨rationalDenominatorProduct xs, rfl⟩
    · obtain ⟨k, hk⟩ := ih hq
      refine ⟨Nat.mul a.den k, ?_⟩
      change Nat.mul a.den (rationalDenominatorProduct xs) =
        Nat.mul q.den (Nat.mul a.den k)
      rw [hk]
      exact Nat.mul_left_comm a.den q.den k

theorem rational_lattice_of_den_divides (D : ℕ) (hD : 0 < D) (q : ℚ)
    (hdiv : q.den ∣ D) : RationalDenominatorLattice D q := by
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨q.num * (k : ℤ), ?_⟩
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hn : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden).mp q.num_div_den
  apply (eq_div_iff hDQ).mpr
  rw [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    q * ((q.den : ℚ) * (k : ℚ)) = (q * (q.den : ℚ)) * (k : ℚ) := by ring
    _ = (q.num : ℚ) * (k : ℚ) := congrArg (fun x : ℚ => x * (k : ℚ)) hn.symm

/-- The canonical reduced denominator also divides the fixed lattice scale.
This is needed to connect a lattice invariant to actual encoding-size bounds;
membership alone is not substituted for that canonical-denominator claim. -/
theorem rational_lattice_den_divides (D : ℕ) (q : ℚ)
    (hq : RationalDenominatorLattice D q) : q.den ∣ D := by
  obtain ⟨z, hz⟩ := hq
  have hcast : (q.den : ℤ) ∣ (D : ℤ) := by
    have h := Rat.den_dvd z (D : ℤ)
    simpa only [Rat.divInt_eq_div, Int.cast_natCast, ← hz] using h
  exact Int.natCast_dvd_natCast.mp hcast

theorem rational_lattice_iff_den_divides (D : ℕ) (hD : 0 < D) (q : ℚ) :
    RationalDenominatorLattice D q ↔ q.den ∣ D :=
  ⟨rational_lattice_den_divides D q, rational_lattice_of_den_divides D hD q⟩

theorem rational_lattice_den_le (D : ℕ) (hD : 0 < D) (q : ℚ)
    (hq : RationalDenominatorLattice D q) : q.den ≤ D :=
  Nat.le_of_dvd hD (rational_lattice_den_divides D q hq)

theorem rational_lattice_input_list (xs : List ℚ) (q : ℚ) (hq : q ∈ xs) :
    RationalDenominatorLattice (rationalDenominatorProduct xs) q :=
  rational_lattice_of_den_divides _ (rational_denominator_product_positive xs) q
    (rational_member_denominator_divides_product xs q hq)

/-- A genuine finite rational enumeration of the capacity data. -/
def rationalMatrixEntries {n : ℕ} (C : Fin n → Fin n → ℚ) : List ℚ :=
  (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => C u v))

def rationalCapacityDenominator {n : ℕ} (C : Fin n → Fin n → ℚ) : ℕ :=
  rationalDenominatorProduct (rationalMatrixEntries C)

theorem rational_capacity_denominator_positive {n : ℕ} (C : Fin n → Fin n → ℚ) :
    0 < rationalCapacityDenominator C :=
  rational_denominator_product_positive (rationalMatrixEntries C)

theorem rational_capacity_lattice {n : ℕ} (C : Fin n → Fin n → ℚ) (u v : Fin n) :
    RationalDenominatorLattice (rationalCapacityDenominator C) (C u v) := by
  apply rational_lattice_input_list (rationalMatrixEntries C) (C u v)
  apply List.mem_flatMap.mpr
  refine ⟨u, List.mem_finRange u, ?_⟩
  exact List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩

theorem rational_residual_lattice {n : ℕ} (D : ℕ)
    (C F : Fin n → Fin n → ℚ)
    (hC : ∀ u v, RationalDenominatorLattice D (C u v))
    (hF : ∀ u v, RationalDenominatorLattice D (F u v)) (u v : Fin n) :
    RationalDenominatorLattice D (C u v - F u v) :=
  rational_lattice_sub D (C u v) (F u v) (hC u v) (hF u v)

theorem rational_path_residuals_lattice {n : ℕ} (D : ℕ)
    (C F : Fin n → Fin n → ℚ)
    (hC : ∀ u v, RationalDenominatorLattice D (C u v))
    (hF : ∀ u v, RationalDenominatorLattice D (F u v))
    (a : Fin n) (tail : List (Fin n)) (z : ℚ)
    (hz : z ∈ rationalPathResiduals C F a tail) : RationalDenominatorLattice D z := by
  revert hz
  induction tail generalizing a with
  | nil => intro hz; cases hz
  | cons b tail ih =>
    intro hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact rational_residual_lattice D C F hC hF a b
    · exact ih b hz

/-- The computed minimum is an actual original residual value, so it retains
the input lattice without any rounding or denominator-growth assumption. -/
theorem rational_path_bottleneck_lattice {n : ℕ} (D : ℕ)
    (C F : Fin n → Fin n → ℚ)
    (hC : ∀ u v, RationalDenominatorLattice D (C u v))
    (hF : ∀ u v, RationalDenominatorLattice D (F u v))
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ)
    (ho : rationalPathBottleneck C F a tail = some δ) :
    RationalDenominatorLattice D δ :=
  rational_path_residuals_lattice D C F hC hF a tail δ
    (rational_nonempty_minimum_some (rationalPathResiduals C F a tail) δ ho).1

theorem rational_net_push_edge_lattice {n : ℕ} (D : ℕ)
    (F : Fin n → Fin n → ℚ) (hF : ∀ u v, RationalDenominatorLattice D (F u v))
    (a b : Fin n) (δ : ℚ) (hδ : RationalDenominatorLattice D δ) :
    ∀ u v, RationalDenominatorLattice D (rationalNetPushEdge F a b δ u v) := by
  intro u v
  unfold rationalNetPushEdge
  apply rational_lattice_sub
  · apply rational_lattice_add D _ _ (hF u v)
    split_ifs
    · exact hδ
    · exact rational_lattice_zero D
  · split_ifs
    · exact hδ
    · exact rational_lattice_zero D

theorem rational_net_push_path_lattice {n : ℕ} (D : ℕ)
    (F : Fin n → Fin n → ℚ) (hF : ∀ u v, RationalDenominatorLattice D (F u v))
    (a : Fin n) (tail : List (Fin n)) (δ : ℚ)
    (hδ : RationalDenominatorLattice D δ) :
    ∀ u v, RationalDenominatorLattice D (rationalNetPushPath F a tail δ u v) := by
  induction tail generalizing a with
  | nil => exact hF
  | cons b tail ih =>
    rw [rational_net_push_path_cons]
    exact rational_net_push_edge_lattice D _ (ih b) a b δ hδ

/-- One actual positive bottleneck augmentation gains at least one common
denominator unit of source value. This is the stepping inequality needed for
a later integral-fuel termination argument, not that argument itself. -/
theorem rational_path_lattice_source_step {n : ℕ} (D : ℕ) (hD : 0 < D)
    (C F : Fin n → Fin n → ℚ)
    (hC : ∀ u v, RationalDenominatorLattice D (C u v))
    (hF : ∀ u v, RationalDenominatorLattice D (F u v))
    (a : Fin n) (tail : List (Fin n)) (hat : a ≠ rationalPathEnd a tail)
    (δ : ℚ) (ho : rationalPathBottleneck C F a tail = some δ) (hpos : 0 < δ) :
    (1 : ℚ) / (D : ℚ) ≤
      (∑ v, rationalNetPushPath F a tail δ a v) - (∑ v, F a v) := by
  have hlattice := rational_path_bottleneck_lattice D C F hC hF a tail δ ho
  have hstep := rational_lattice_positive_step D hD δ hlattice hpos
  rw [rational_net_push_path_source_value F a tail δ hat]
  linarith

end SparseCompletion
