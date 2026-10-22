/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human authorship and maintainer membership remain unconfirmed. -/
module
public import SparseCompletion

@[expose] public section

open scoped BigOperators

namespace SparseCompletion
noncomputable section

def blockMatrix {α ι : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B : ι → ι → ℝ) : (α ⊕ ι) → (α ⊕ ι) → ℝ
  | .inl h, .inl h' => K h h'
  | .inl h, .inr i => -D i h
  | .inr i, .inl h => D i h
  | .inr i, .inr j => B i j

def blockWeights {α ι : Type*} (p : α → ℝ) (q : ι → ℝ) : (α ⊕ ι) → ℝ := Sum.elim p q

def score {α ι : Type*} [Fintype α] (D : ι → α → ℝ) (p : α → ℝ) (i : ι) : ℝ :=
  ∑ h, D i h*p h

def anchorResponse {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ) (h : α) : ℝ :=
  (∑ h', K h h'*p h')-∑ i, D i h*q i

theorem blockMatrix_skew {α ι : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B : ι → ι → ℝ) (hK : IsSkew K) (hB : IsSkew B) : IsSkew (blockMatrix K D B) := by
  intro a b
  cases a <;> cases b
  · exact hK _ _
  · rfl
  · simp only [blockMatrix, neg_neg]
  · exact hB _ _

theorem blockWeights_nonneg {α ι : Type*} (p : α → ℝ) (q : ι → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) : ∀ a, 0 ≤ blockWeights p q a := by
  intro a
  cases a with
  | inl h => exact hp h
  | inr i => exact hq i

theorem blockMatrix_bounds {α ι : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B : ι → ι → ℝ) (M : ℝ)
    (hK : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hD : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hB : ∀ i j, -M ≤ B i j ∧ B i j ≤ M) :
    ∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M := by
  intro a b
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact hK h h'
    | inr i =>
      have hi := hD i h
      change -M ≤ -D i h ∧ -D i h ≤ M
      constructor <;> linarith [hi.1, hi.2]
  | inr i =>
    cases b with
    | inl h => exact hD i h
    | inr j => exact hB i j

theorem blockWeights_mass {α ι : Type*} [Fintype α] [Fintype ι] (p : α → ℝ) (q : ι → ℝ) :
    (∑ a, blockWeights p q a) = (∑ h, p h)+(∑ i, q i) := by
  simp only [Fintype.sum_sum_type, blockWeights, Sum.elim_inl, Sum.elim_inr]

theorem block_response_anchor {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (h : α) :
    response (blockMatrix K D B) (blockWeights p q) (.inl h) = anchorResponse K D p q h := by
  simp only [response, Fintype.sum_sum_type, blockMatrix, blockWeights,
    Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, anchorResponse, sub_eq_add_neg]

theorem block_response_residual {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (i : ι) :
    response (blockMatrix K D B) (blockWeights p q) (.inr i) = score D p i+response B q i := by
  simp only [response, Fintype.sum_sum_type, blockMatrix, blockWeights,
    Sum.elim_inl, Sum.elim_inr, score]

theorem block_response_bounds_iff {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (ρ : ℝ) :
    (∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) ↔
      (∀ h, anchorResponse K D p q h ≤ ρ) ∧ (∀ i, score D p i+response B q i ≤ ρ) := by
  constructor
  · intro h
    exact ⟨fun a => (block_response_anchor K D B p q a) ▸ h (.inl a),
      fun i => (block_response_residual K D B p q i) ▸ h (.inr i)⟩
  · rintro ⟨hA, hR⟩ a
    cases a with
    | inl h => simpa only [block_response_anchor] using hA h
    | inr i => simpa only [block_response_residual] using hR i

theorem response_bounds {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (B : ι → ι → ℝ) (M r : ℝ) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : ∀ i j, -M ≤ B i j ∧ B i j ≤ M) :
    ∀ i, -M*r ≤ response B q i ∧ response B q i ≤ M*r := by
  intro i
  constructor
  · calc
      -M*r = ∑ j, (-M)*q j := by rw [← Finset.mul_sum, hmass]
      _ ≤ response B q i := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hB i j).1 (hq j)
  · calc
      response B q i ≤ ∑ j, M*q j := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hB i j).2 (hq j)
      _ = M*r := by rw [← Finset.mul_sum, hmass]

theorem compact_block_certificate_iff {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r σ : ℝ)
    (hs : ∀ i, i ∉ s → q i = 0) (hmass : ∑ i, q i = r) :
    (∀ a, response (blockMatrix K D (compactCompletion s M B)) (blockWeights p q) a ≤ σ) ↔
      (∀ h, anchorResponse K D p q h ≤ σ) ∧
      (∀ i ∈ s, score D p i+(∑ j ∈ s, B i j*q j) ≤ σ) ∧
      (∀ i, i ∉ s → score D p i-M*r ≤ σ) := by
  rw [block_response_bounds_iff, compact_certificate_responses_iff s M r σ B q (score D p) hs hmass]

theorem exact_supported_residual_zero {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hK : IsSkew K) (hB : IsSkew B)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∀ i, q i ≠ 0 → score D p i+response B q i = 0 := by
  intro i hi
  have hqi : 0 < q i := lt_of_le_of_ne (hq i) hi.symm
  have hz := supported_response_zero (blockWeights p q) (blockMatrix K D B)
    (blockWeights_nonneg p q hp hq) (blockMatrix_skew K D B hK hB) hresp (.inr i) hqi
  simpa only [block_response_residual] using hz

theorem exact_score_bounds {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r : ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∀ i, q i ≠ 0 → |score D p i| ≤ M*r := by
  intro i hi
  have hz := exact_supported_residual_zero K D B p q hp hq hK hB hresp i hi
  have hb := response_bounds q B M r hq hmass hbound i
  exact abs_le.mpr ⟨by linarith [hb.2], by linarith [hb.1]⟩

theorem exact_score_mean_zero {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hK : IsSkew K) (hB : IsSkew B)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∑ i, q i*score D p i = 0 := by
  have heq : (∑ i, q i*score D p i) = -(∑ i, q i*response B q i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : q i = 0
    · simp only [hi, zero_mul, neg_zero]
    · have hz := exact_supported_residual_zero K D B p q hp hq hK hB hresp i hi
      have ht : score D p i = -response B q i := by linarith
      rw [ht]
      ring
  have hb := skew_weighted_sum Finset.univ q B hB
  simp only [response, Finset.mul_sum] at heq
  simp only [mul_assoc] at hb
  rw [hb, neg_zero] at heq
  exact heq

end
end SparseCompletion
