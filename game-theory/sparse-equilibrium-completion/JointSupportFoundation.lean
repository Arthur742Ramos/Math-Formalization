/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import SupportMinimum
public import AllMassWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

abbrev CloneAnchors (n : ℕ) := Fin (n+1) ⊕ Unit

def cloneClass {n : ℕ} : CloneAnchors n → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

def aggregateClones {n : ℕ} (p : CloneAnchors n → ℝ) : Fin 2 → ℝ :=
  fun h => if h.val=0 then ∑ i : Fin (n+1), p (.inl i) else p (.inr ())

def clonedCore {n : ℕ} (K : Fin 2 → Fin 2 → ℝ) : CloneAnchors n → CloneAnchors n → ℝ :=
  fun h h' => K (cloneClass h) (cloneClass h')

def clonedCross {ι : Type*} {n : ℕ} (D : ι → Fin 2 → ℝ) : ι → CloneAnchors n → ℝ :=
  fun i h => D i (cloneClass h)

theorem aggregate_clones_mass {n : ℕ} (p : CloneAnchors n → ℝ) :
    (∑ h, aggregateClones p h)=∑ h, p h := by
  simp [aggregateClones,Fin.sum_univ_two,Fintype.sum_sum_type]

theorem aggregate_clones_nonnegative {n : ℕ} (p : CloneAnchors n → ℝ)
    (hp : ∀ h, 0 ≤ p h) : ∀ h, 0 ≤ aggregateClones p h := by
  intro h
  unfold aggregateClones
  split_ifs
  · exact Finset.sum_nonneg fun i _ => hp _
  · exact hp _

theorem aggregate_clones_mono {n : ℕ} (p p' : CloneAnchors n → ℝ)
    (hp : ∀ h, p h ≤ p' h) : ∀ h, aggregateClones p h ≤ aggregateClones p' h := by
  intro h
  unfold aggregateClones
  split_ifs
  · exact Finset.sum_le_sum fun i _ => hp _
  · exact hp _

theorem cloned_core_skew {n : ℕ} (K : Fin 2 → Fin 2 → ℝ) (hK : IsSkew K) :
    IsSkew (clonedCore (n := n) K) := fun _ _ => hK _ _

theorem cloned_anchor_response {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (h : CloneAnchors n) :
    anchorResponse (clonedCore K) (clonedCross D) p q h=
      anchorResponse K D (aggregateClones p) q (cloneClass h) := by
  cases h <;>
    simp [anchorResponse,clonedCore,clonedCross,cloneClass,aggregateClones,
      Fintype.sum_sum_type,Fin.sum_univ_two,←Finset.mul_sum]

theorem cloned_score {ι : Type*} {n : ℕ} (D : ι → Fin 2 → ℝ)
    (p : CloneAnchors n → ℝ) (i : ι) :
    score (clonedCross D) p i=score D (aggregateClones p) i := by
  simp [score,clonedCross,cloneClass,aggregateClones,Fintype.sum_sum_type,
    Fin.sum_univ_two,←Finset.mul_sum]

theorem cloned_response_anchor {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (h : CloneAnchors n) :
    response (blockMatrix (clonedCore K) (clonedCross D) B) (blockWeights p q) (.inl h)=
      response (blockMatrix K D B) (blockWeights (aggregateClones p) q) (.inl (cloneClass h)) := by
  rw [block_response_anchor,block_response_anchor,cloned_anchor_response]

theorem cloned_response_residual {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (i : ι) :
    response (blockMatrix (clonedCore K) (clonedCross D) B) (blockWeights p q) (.inr i)=
      response (blockMatrix K D B) (blockWeights (aggregateClones p) q) (.inr i) := by
  rw [block_response_residual,block_response_residual,cloned_score]

theorem cloned_response_bounds_iff {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ) (B : ι → ι → ℝ)
    (p : CloneAnchors n → ℝ) (q : ι → ℝ) (ε : ℝ) :
    (∀ v, response (blockMatrix (clonedCore K) (clonedCross D) B) (blockWeights p q) v ≤ ε) ↔
      ∀ v, response (blockMatrix K D B) (blockWeights (aggregateClones p) q) v ≤ ε := by
  constructor
  · intro h v
    cases v with
    | inl a =>
      fin_cases a
      · simpa [cloned_response_anchor,cloneClass] using h (.inl (.inl (0 : Fin (n+1))))
      · simpa [cloned_response_anchor,cloneClass] using h (.inl (.inr ()))
    | inr i => simpa only [cloned_response_residual] using h (.inr i)
  · intro h v
    cases v with
    | inl a => rw [cloned_response_anchor]; exact h _
    | inr i => rw [cloned_response_residual]; exact h _

def cloneShares (n : ℕ) : CloneAnchors n → ℝ :=
  Sum.elim (fun _ => ((3 : ℕ) : ℝ)/((8 : ℕ)*((n+1 : ℕ) : ℝ))) (fun _ => ((3 : ℕ) : ℝ)/(8 : ℕ))

theorem clone_shares_positive (n : ℕ) : ∀ h, 0 < cloneShares n h := by
  intro h
  cases h <;> simp only [cloneShares,Sum.elim_inl,Sum.elim_inr] <;> positivity

theorem aggregate_clone_shares (n : ℕ) : aggregateClones (cloneShares n)=twoShares (((3 : ℕ) : ℝ)/(4 : ℕ)) := by
  funext h
  fin_cases h
  · have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [aggregateClones,ite_true,cloneShares,Sum.elim_inl,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,twoShares]
    field_simp
    norm_num
  · norm_num [aggregateClones,cloneShares,twoShares]

theorem aggregate_clone_lower {n : ℕ} (p : CloneAnchors n → ℝ)
    (hp : ∀ h, cloneShares n h ≤ p h) : ∀ h, (((3 : ℕ) : ℝ)/(8 : ℕ) : ℝ) ≤ aggregateClones p h := by
  have hh := aggregate_clones_mono (cloneShares n) p hp
  rw [aggregate_clone_shares] at hh
  intro h
  have hx := hh h
  norm_num [twoShares] at hx
  exact hx

theorem clone_support_card {m n : ℕ}
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (hp : ∀ h, cloneShares n h ≤ p h) :
    (Finset.univ.filter fun v => blockWeights p q v ≠ 0).card=n+2+supportSize q := by
  classical
  have hpa : (Finset.univ.filter fun h => p h ≠ 0)=(Finset.univ : Finset (CloneAnchors n)) := by
    ext h
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact ne_of_gt (lt_of_lt_of_le (clone_shares_positive n h) (hp h))
  rw [block_support_card,hpa]
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
  rfl

end
end SparseCompletion
