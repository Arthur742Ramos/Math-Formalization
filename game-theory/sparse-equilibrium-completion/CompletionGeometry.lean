/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GameModel
public import Mathlib.Analysis.LocallyConvex.Separation
public import CompletionDual

@[expose] public section

open scoped BigOperators
open Set

namespace SparseCompletion
noncomputable section

def skewBox {ι : Type*} (M : ℝ) : Set (ι → ι → ℝ) :=
  {B | IsSkew B ∧ ∀ i j, -M ≤ B i j ∧ B i j ≤ M}

def weightedNegResponse {ι : Type*} [Fintype ι] (q : ι → ℝ) :
    (ι → ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun B i := -q i*response B q i
  map_add' B C := by
    ext i
    change -q i*response (B+C) q i = -q i*response B q i+-q i*response C q i
    simp only [response, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' a B := by
    ext i
    change -q i*(∑ j, (a*B i j)*q j) = a*(-q i*∑ j, B i j*q j)
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

theorem skewBox_zero {ι : Type*} (M : ℝ) (hM : 0 ≤ M) :
    (0 : ι → ι → ℝ) ∈ skewBox M := by
  constructor
  · intro i j
    simp
  · intro i j
    exact ⟨neg_nonpos.mpr hM, hM⟩

theorem skewBox_compact {ι : Type*} [Fintype ι] (M : ℝ) : IsCompact (skewBox (ι := ι) M) := by
  have hclosed : IsClosed {B : ι → ι → ℝ | IsSkew B} := by
    have heq : {B : ι → ι → ℝ | IsSkew B} = ⋂ i, ⋂ j, {B | B i j = -B j i} := by
      ext B
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, IsSkew]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  have heq : skewBox (ι := ι) M =
      Set.Icc (fun _ _ => -M) (fun _ _ => M) ∩ {B | IsSkew B} := by
    ext B
    constructor
    · rintro ⟨hsk, hb⟩
      exact ⟨⟨fun i j => (hb i j).1, fun i j => (hb i j).2⟩, hsk⟩
    · rintro ⟨⟨hl, hu⟩, hsk⟩
      exact ⟨hsk, fun i j => ⟨hl i j, hu i j⟩⟩
  rw [heq]
  exact isCompact_Icc.inter_right hclosed

theorem skewBox_convex {ι : Type*} (M : ℝ) : Convex ℝ (skewBox (ι := ι) M) := by
  intro B hB C hC a b ha hb hab
  constructor
  · intro i j
    change a*B i j+b*C i j = -(a*B j i+b*C j i)
    rw [hB.1 i j, hC.1 i j]
    ring
  · intro i j
    change -M ≤ a*B i j+b*C i j ∧ a*B i j+b*C i j ≤ M
    constructor
    · calc
        -M = a*(-M)+b*(-M) := by rw [← add_mul, hab, one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hB.2 i j).1 ha)
          (mul_le_mul_of_nonneg_left (hC.2 i j).1 hb)
    · calc
        _ ≤ a*M+b*M := add_le_add (mul_le_mul_of_nonneg_left (hB.2 i j).2 ha)
          (mul_le_mul_of_nonneg_left (hC.2 i j).2 hb)
        _ = M := by rw [← add_mul, hab, one_mul]

def weightedScoreSet {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) : Set (ι → ℝ) :=
  weightedNegResponse q '' skewBox M

theorem weightedScoreSet_compact {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) :
    IsCompact (weightedScoreSet q M) :=
  (skewBox_compact M).image (weightedNegResponse q).continuous_of_finiteDimensional

theorem weightedScoreSet_convex {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) :
    Convex ℝ (weightedScoreSet q M) := (skewBox_convex M).linear_image (weightedNegResponse q)

theorem weightedScoreSet_zero {ι : Type*} [Fintype ι] (q : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) :
    (0 : ι → ℝ) ∈ weightedScoreSet q M :=
  ⟨0, skewBox_zero M hM, (weightedNegResponse q).map_zero⟩

def upperOrthant {ι : Type*} (d : ι → ℝ) : Set (ι → ℝ) := {z | ∀ i, d i ≤ z i}

theorem upperOrthant_closed {ι : Type*} (d : ι → ℝ) : IsClosed (upperOrthant d) := by
  have heq : upperOrthant d = ⋂ i, {z | d i ≤ z i} := by
    ext z
    simp only [upperOrthant, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)

theorem upperOrthant_convex {ι : Type*} (d : ι → ℝ) : Convex ℝ (upperOrthant d) := by
  intro z hz w hw a b ha hb hab i
  change d i ≤ a*z i+b*w i
  calc
    d i = a*d i+b*d i := by rw [← add_mul, hab, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hz i) ha) (mul_le_mul_of_nonneg_left (hw i) hb)

theorem dual_evaluation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : StrongDual ℝ (ι → ℝ)) (z : ι → ℝ) :
    f z = ∑ i, f (Pi.single i 1)*z i := by
  have hz : z = ∑ i, z i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hz, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  ring

theorem separator_coefficients_nonnegative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (f : StrongDual ℝ (ι → ℝ)) (v : ℝ)
    (hf : ∀ z ∈ upperOrthant d, v < f z) : ∀ i, 0 ≤ f (Pi.single i 1) := by
  intro i
  have hfd : v < f d := hf d (fun _ => le_rfl)
  by_contra hn
  have hneg : f (Pi.single i 1) < 0 := lt_of_not_ge hn
  let a := (f d-v+1)/(-f (Pi.single i 1))
  have ha : 0 ≤ a := le_of_lt (div_pos (by linarith) (neg_pos.mpr hneg))
  have hz : d+a • Pi.single i (1 : ℝ) ∈ upperOrthant d := by
    intro j
    change d j ≤ d j+a*(Pi.single i (1 : ℝ) : ι → ℝ) j
    have hsingle : 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := by
      simp only [Pi.single_apply]
      split <;> norm_num
    exact le_add_of_nonneg_right (mul_nonneg ha hsingle)
  have ht := hf _ hz
  rw [map_add, map_smul] at ht
  have hprod : a*f (Pi.single i 1) = -(f d-v+1) := by
    dsimp [a]
    field_simp [ne_of_lt hneg]
  change v < f d+a*f (Pi.single i 1) at ht
  rw [hprod] at ht
  linarith

theorem skew_dot_identity {ι : Type*} [Fintype ι]
    (q y : ι → ℝ) (B : ι → ι → ℝ) (hB : IsSkew B) :
    (∑ i, y i*weightedNegResponse q B i) =
      (∑ i, ∑ j, q i*q j*(-B i j)*(y i-y j))/2 := by
  let S₁ := ∑ i, ∑ j, q i*q j*B i j*y i
  let S₂ := ∑ i, ∑ j, q i*q j*B i j*y j
  have hdot : (∑ i, y i*weightedNegResponse q B i) = -S₁ := by
    change (∑ i, y i*(-q i*response B q i)) = -S₁
    dsimp [S₁, response]
    rw [← Finset.sum_neg_distrib]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hswap : S₂ = -S₁ := by
    dsimp [S₁, S₂]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hB j i]
    ring
  have hterm : ∀ i j, q i*q j*(-B i j)*(y i-y j) =
      -(q i*q j*B i j*y i)+q i*q j*B i j*y j := by intros; ring
  have hdiff : (∑ i, ∑ j, q i*q j*(-B i j)*(y i-y j)) = -S₁+S₂ := by
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rfl
  rw [hdot, hdiff, hswap]
  ring

def orderedMatrix {ι : Type*} (M : ℝ) (y : ι → ℝ) (i j : ι) : ℝ := by
  classical
  exact if y j < y i then -M else if y i < y j then M else 0

theorem orderedMatrix_skew {ι : Type*} (M : ℝ) (y : ι → ℝ) : IsSkew (orderedMatrix M y) := by
  intro i j
  rcases lt_trichotomy (y i) (y j) with hij | heq | hji
  · simp [orderedMatrix, hij, not_lt.mpr (le_of_lt hij)]
  · simp [orderedMatrix, heq]
  · simp [orderedMatrix, hji, not_lt.mpr (le_of_lt hji)]

theorem orderedMatrix_mem_box {ι : Type*} (M : ℝ) (y : ι → ℝ) (hM : 0 ≤ M) :
    orderedMatrix M y ∈ skewBox M := by
  refine ⟨orderedMatrix_skew M y, ?_⟩
  intro i j
  unfold orderedMatrix
  split_ifs <;> constructor <;> linarith

theorem orderedMatrix_pair {ι : Type*} (M : ℝ) (y : ι → ℝ) (i j : ι) :
    (-orderedMatrix M y i j)*(y i-y j) = M*|y i-y j| := by
  classical
  by_cases hij : y j < y i
  · simp only [orderedMatrix, ite_eq_left hij, neg_neg, abs_of_pos (sub_pos.mpr hij)]
  · by_cases hji : y i < y j
    · simp only [orderedMatrix, ite_eq_right hij, ite_eq_left hji, abs_of_neg (sub_neg.mpr hji)]
      ring
    · have heq : y i = y j := by linarith
      simp [orderedMatrix, heq]

theorem orderedMatrix_dot {ι : Type*} [Fintype ι] (M : ℝ) (q y : ι → ℝ) :
    (∑ i, y i*weightedNegResponse q (orderedMatrix M y) i) = M*weightedVariation q y := by
  rw [skew_dot_identity q y _ (orderedMatrix_skew M y)]
  have ht : ∀ i j, q i*q j*(-orderedMatrix M y i j)*(y i-y j) = M*(q i*q j*|y i-y j|) := by
    intro i j
    calc
      _ = q i*q j*((-orderedMatrix M y i j)*(y i-y j)) := by ring
      _ = _ := by rw [orderedMatrix_pair]; ring
  simp only [ht, ← Finset.mul_sum, weightedVariation]
  ring

/-- Every family of subset cuts has a bounded skew realization in weighted
    coordinates. Zero weights require no cancellation in this theorem. -/
theorem cuts_weighted_completion {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hM : 0 ≤ M)
    (hr : ∑ i, q i = r) (hc : Cuts M r q v) :
    ∃ B ∈ skewBox M, ∀ i, q i*v i ≤ -q i*response B q i := by
  classical
  let d : ι → ℝ := fun i => q i*v i
  have hinter : (weightedScoreSet q M ∩ upperOrthant d).Nonempty := by
    by_contra hn
    have hdisj : Disjoint (weightedScoreSet q M) (upperOrthant d) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨f, u, w, hleft, huw, hright⟩ :=
      geometric_hahn_banach_compact_closed (weightedScoreSet_convex q M)
        (weightedScoreSet_compact q M) (upperOrthant_convex d)
        (upperOrthant_closed d) hdisj
    let y : ι → ℝ := fun i => f (Pi.single i 1)
    have hy : ∀ i, 0 ≤ y i := separator_coefficients_nonnegative d f w hright
    have hbound : f d ≤ M*weightedVariation q y := by
      rw [dual_evaluation]
      have hterms : (∑ i, f (Pi.single i 1)*d i) = ∑ i, q i*v i*y i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [d, y]
        ring
      rw [hterms]
      exact cuts_dual_bound q v M r hr hc y hy
    have hscore : weightedNegResponse q (orderedMatrix M y) ∈ weightedScoreSet q M :=
      ⟨orderedMatrix M y, orderedMatrix_mem_box M y hM, rfl⟩
    have heval : f (weightedNegResponse q (orderedMatrix M y)) = M*weightedVariation q y := by
      rw [dual_evaluation]
      exact orderedMatrix_dot M q y
    have hl := hleft _ hscore
    have hrgt := hright d (fun _ => le_rfl)
    rw [heval] at hl
    linarith
  obtain ⟨z, ⟨B, hB, rfl⟩, hz⟩ := hinter
  exact ⟨B, hB, hz⟩

end
end SparseCompletion
