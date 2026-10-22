/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import CoverRelabel

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem arbitrary_vertex_cover_sparse {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hcover : intervalVertexCover C lo hi M) (hresp : ∀ i, response A x i ≤ ρ) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ ρ+η) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  let e := coverEquiv C
  let k := Fintype.card C
  let p := fun h : Fin k => x (e (.inl h))
  let q := fun i : (Cᶜ : Set ν) => x (e (.inr i))
  let r := ∑ i, q i
  let K := fun h h' : Fin k => A (e (.inl h)) (e (.inl h'))
  let D := fun (i : (Cᶜ : Set ν)) (h : Fin k) => A (e (.inr i)) (e (.inl h))
  let B := fun i j : (Cᶜ : Set ν) => A (e (.inr i)) (e (.inr j))
  let lo' := relabelMatrix e.symm lo
  let hi' := relabelMatrix e.symm hi
  have hxsplit : relabelWeights e.symm x=blockWeights p q := split_weights e x
  have hAsplit : relabelMatrix e.symm A=blockMatrix K D B := split_skew_matrix e A hA
  have hp : ∀ h, 0 ≤ p h := fun h => hn _
  have hq : ∀ i, 0 ≤ q i := fun i => hn _
  have hr : 0 ≤ r := Finset.sum_nonneg fun i _ => hq i
  have hpm : (∑ h, p h)+r=1 := by
    change (∑ h, p h)+(∑ i, q i)=1
    rw [←blockWeights_mass,←hxsplit,relabel_mass]
    exact hm
  have hK : IsSkew K := fun h h' => hA _ _
  have hB : IsSkew B := fun i j => hA _ _
  have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun _ _ => hb _ _
  have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun _ _ => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun _ _ => hb _ _
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ := by
    intro a
    rw [←hAsplit,←hxsplit,relabel_response]
    exact hresp _
  have hIv : offDiagonalIntervals lo' hi' (blockMatrix K D B) := by
    rw [←hAsplit]
    exact (relabel_intervals e.symm lo hi A).mpr hI
  obtain ⟨q',B',hqn,hqm,hpa,hs,hc,ht,_,hF,hsk,hbb,hresponse,hInt,hentries,hanchors⟩ :=
    normalized_cover_witness k d K D (fun i g => F i.val g) B p q M r ρ η hM hr hη hp hq hpm rfl
      hK hB hKb hDb hBb hrows lo' hi' (arbitrary_cover_free_residual C lo hi M hcover) hIv
  let A' := relabelMatrix e (blockMatrix K D B')
  let x' := relabelWeights e (blockWeights p q')
  have hres : ∀ i : (Cᶜ : Set ν), x' i.val=q' i := cover_relabel_on_residual C p q'
  have hdim : Fintype.card ν=k+Fintype.card (Cᶜ : Set ν) := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_sum,Fintype.card_fin] using hh.symm
  have hrform : r=∑ i : (Cᶜ : Set ν), x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg x (cover_equiv_residual C i)
  refine ⟨A',x',?_,?_,relabel_skew e _ hsk,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun i => hqn (e.symm i)
  · rw [relabel_mass]
    exact hqm
  · exact fun i j => hbb (e.symm i) (e.symm j)
  · intro i j hij
    have he : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simpa only [A',lo',hi',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hInt _ _ he
  · intro i
    rw [relabel_response]
    exact hresponse _
  · exact cover_relabel_on_anchor C x q'
  · intro v hv hz
    let i : (Cᶜ : Set ν) := ⟨v,hv⟩
    have hqi : q i=0 := by change x (e (.inr i))=0; rw [cover_equiv_residual]; exact hz
    exact (hres i).trans (hs i hqi)
  · have hcard : (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i.val ≠ 0)=
        Finset.univ.filter (fun i => q' i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hres]
    rw [hcard]
    simpa only [←hrform] using hc
  · rw [relabel_support_card]
    simpa only [←hrform,hdim] using ht
  · intro a b hab
    have he : (∃ h, e.symm a=Sum.inl h) ∨ ∃ h, e.symm b=Sum.inl h := by
      rcases hab with h | h
      · exact Or.inl (cover_equiv_inverse_anchor C a h)
      · exact Or.inr (cover_equiv_inverse_anchor C b h)
    have hh := hentries (e.symm a) (e.symm b) he
    rw [←hAsplit] at hh
    simpa only [A',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hh
  · intro v hv
    obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
    have hh := hanchors h
    rw [←hAsplit,←hxsplit,relabel_response] at hh
    change response A' x' v=response A x v
    rw [relabel_response,he]
    have hv' : e (.inl h)=v := by rw [←he]; exact e.apply_symm_apply v
    simpa only [Equiv.symm_symm,hv'] using hh
  · intro g
    simpa only [hres,q,e,cover_equiv_residual] using hF g

theorem arbitrary_vertex_cover_exact {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (d : ℕ) (F : ν → Fin d → ℝ) (A lo hi : ν → ν → ℝ) (x : ν → ℝ) (M η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hA : IsSkew A) (hb : ∀ i j, -M ≤ A i j ∧ A i j ≤ M)
    (hn : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) (hI : offDiagonalIntervals lo hi A)
    (hcover : intervalVertexCover C lo hi M) (hresp : ∀ i, response A x i ≤ 0) :
    let k := Fintype.card C
    let r := ∑ i : (Cᶜ : Set ν), x i
    ∃ (A' : ν → ν → ℝ) (x' : ν → ℝ),
      (∀ i, 0 ≤ x' i) ∧ (∑ i, x' i)=1 ∧ IsSkew A' ∧
      (∀ i j, -M ≤ A' i j ∧ A' i j ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ i, response A' x' i ≤ η) ∧ (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i ≠ 0).card ≤
        min (Fintype.card (Cᶜ : Set ν)) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun i => x' i ≠ 0).card ≤
        min (Fintype.card ν) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ a b, a ∈ C ∨ b ∈ C → A' a b=A a b) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ i : (Cᶜ : Set ν), x' i*F i g)=∑ i : (Cᶜ : Set ν), x i*F i g := by
  classical
  dsimp only
  let e := coverEquiv C
  let k := Fintype.card C
  let p := fun h : Fin k => x (e (.inl h))
  let q := fun i : (Cᶜ : Set ν) => x (e (.inr i))
  let r := ∑ i, q i
  let K := fun h h' : Fin k => A (e (.inl h)) (e (.inl h'))
  let D := fun (i : (Cᶜ : Set ν)) (h : Fin k) => A (e (.inr i)) (e (.inl h))
  let B := fun i j : (Cᶜ : Set ν) => A (e (.inr i)) (e (.inr j))
  let lo' := relabelMatrix e.symm lo
  let hi' := relabelMatrix e.symm hi
  have hxsplit : relabelWeights e.symm x=blockWeights p q := split_weights e x
  have hAsplit : relabelMatrix e.symm A=blockMatrix K D B := split_skew_matrix e A hA
  have hp : ∀ h, 0 ≤ p h := fun h => hn _
  have hq : ∀ i, 0 ≤ q i := fun i => hn _
  have hr : 0 ≤ r := Finset.sum_nonneg fun i _ => hq i
  have hpm : (∑ h, p h)+r=1 := by
    change (∑ h, p h)+(∑ i, q i)=1
    rw [←blockWeights_mass,←hxsplit,relabel_mass]
    exact hm
  have hK : IsSkew K := fun h h' => hA _ _
  have hB : IsSkew B := fun i j => hA _ _
  have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun _ _ => hb _ _
  have hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M := fun _ _ => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun _ _ => hb _ _
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0 := by
    intro a
    rw [←hAsplit,←hxsplit,relabel_response]
    exact hresp _
  have hIv : offDiagonalIntervals lo' hi' (blockMatrix K D B) := by
    rw [←hAsplit]
    exact (relabel_intervals e.symm lo hi A).mpr hI
  obtain ⟨q',B',hqn,hqm,hpa,hs,hc,ht,_,hF,hsk,hbb,hresponse,hInt,hentries,hanchors⟩ :=
    normalized_exact_cover_witness k d K D (fun i g => F i.val g) B p q M r η hM hr hη hp hq hpm rfl
      hK hB hKb hDb hBb hrows lo' hi' (arbitrary_cover_free_residual C lo hi M hcover) hIv
  let A' := relabelMatrix e (blockMatrix K D B')
  let x' := relabelWeights e (blockWeights p q')
  have hres : ∀ i : (Cᶜ : Set ν), x' i.val=q' i := cover_relabel_on_residual C p q'
  have hdim : Fintype.card ν=k+Fintype.card (Cᶜ : Set ν) := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_sum,Fintype.card_fin] using hh.symm
  have hrform : r=∑ i : (Cᶜ : Set ν), x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg x (cover_equiv_residual C i)
  refine ⟨A',x',?_,?_,relabel_skew e _ hsk,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun i => hqn (e.symm i)
  · rw [relabel_mass]
    exact hqm
  · exact fun i j => hbb (e.symm i) (e.symm j)
  · intro i j hij
    have he : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simpa only [A',lo',hi',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hInt _ _ he
  · intro i
    rw [relabel_response]
    exact hresponse _
  · exact cover_relabel_on_anchor C x q'
  · intro v hv hz
    let i : (Cᶜ : Set ν) := ⟨v,hv⟩
    have hqi : q i=0 := by change x (e (.inr i))=0; rw [cover_equiv_residual]; exact hz
    exact (hres i).trans (hs i hqi)
  · have hcard : (Finset.univ.filter fun i : (Cᶜ : Set ν) => x' i.val ≠ 0)=
        Finset.univ.filter (fun i => q' i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hres]
    rw [hcard]
    simpa only [←hrform] using hc
  · rw [relabel_support_card]
    simpa only [←hrform,hdim] using ht
  · intro a b hab
    have he : (∃ h, e.symm a=Sum.inl h) ∨ ∃ h, e.symm b=Sum.inl h := by
      rcases hab with h | h
      · exact Or.inl (cover_equiv_inverse_anchor C a h)
      · exact Or.inr (cover_equiv_inverse_anchor C b h)
    have hh := hentries (e.symm a) (e.symm b) he
    rw [←hAsplit] at hh
    simpa only [A',relabelMatrix,Equiv.symm_symm,Equiv.apply_symm_apply] using hh
  · intro v hv
    obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
    have hh := hanchors h
    rw [←hAsplit,←hxsplit,relabel_response] at hh
    change response A' x' v=response A x v
    rw [relabel_response,he]
    have hv' : e (.inl h)=v := by rw [←he]; exact e.apply_symm_apply v
    simpa only [Equiv.symm_symm,hv'] using hh
  · intro g
    simpa only [hres,q,e,cover_equiv_residual] using hF g

end
end SparseCompletion
