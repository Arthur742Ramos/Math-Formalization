/- AI-assisted formalization under the repository Apache-2.0 license.
Uniform ceiling bound for any supplied observation cover, hence a minimum one. -/
module
public import ArbitraryCover
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem cover_residual_mass_le_one {ν : Type*} [Fintype ν]
    (C : Set ν) [DecidablePred (· ∈ C)] (x : ν → ℝ)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) :
    (∑ i : (Cᶜ : Set ν), x i) ≤ 1 := by
  have he := Equiv.sum_comp (coverEquiv C) x
  simp only [Fintype.sum_sum_type, cover_equiv_residual, hm] at he
  have ha : 0 ≤ ∑ h : Fin (Fintype.card C), x (coverEquiv C (.inl h)) :=
    Finset.sum_nonneg fun h _ => hn _
  linarith

theorem gridSize_uniform_mass_bound (M r η : ℝ)
    (hM : 0 ≤ M) (hr : r ≤ 1) (hη : 0 < η) :
    gridSize M r η ≤ Nat.ceil (Real.sqrt (M/η)) := by
  unfold gridSize
  apply Nat.ceil_mono
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hM hr) (le_of_lt hη)

/-- Uniform bound with r eliminated; applies to a minimum cover by choosing it
as C. The theorem retains the original cover shares and incident payoffs. -/
theorem arbitrary_vertex_cover_uniform_exact {ν : Type*} [Fintype ν]
    (C : Set ν) [DecidablePred (· ∈ C)] (A lo hi : ν → ν → ℝ)
    (x : ν → ℝ) (M η : ℝ) (hM : 0 < M) (hη : 0 < η)
    (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hcover : intervalVertexCover C lo hi M) (hresp : ∀ i, response A x i ≤ 0) :
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ η) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) (2*Fintype.card C+Nat.ceil (Real.sqrt (M/η))) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) := by
  classical
  obtain ⟨A',x',hqn,hqm,hsk,hb',hI',hr',hp',hz',_,ht',he',ha',_⟩ :=
    arbitrary_vertex_cover_exact C 0 (fun _ g => Fin.elim0 g) A lo hi x M η
      hM hη hA hb hn hm hI hcover hresp
  have hg := gridSize_uniform_mass_bound M (∑ i : (Cᶜ : Set ν), x i) η
    (le_of_lt hM) (cover_residual_mass_le_one C x hn hm) hη
  refine ⟨A',x',hqn,hqm,hsk,hb',hI',hr',hp',hz',?_,he',ha'⟩
  apply le_trans ht'
  apply min_le_min_left
  simp only [Nat.add_zero]
  omega

end
end SparseCompletion
