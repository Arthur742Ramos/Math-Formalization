/- AI-assisted formalization under the repository Apache-2.0 license.
Source-only draft. Full witness transport through the actual finite encoder.
The existing relabel lemmas are used only in proofs; executable indexing does
not call coverEquiv or Fintype.equivFin. No compressor runtime claim. -/
module
public import ExecutableCoverIndex
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem cover_residual_sum {n : ℕ} (C : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ v : {v : Fin n // v ∈ Cᶜ}, f v.val)=
      ∑ i : Fin Cᶜ.card, f (coverDecode C (.inr i)) := by
  exact (Equiv.sum_comp (coverResidualIndex C) (fun v => f v.val)).symm

theorem cover_residual_support {n : ℕ} (C : Finset (Fin n))
    (y : (Fin C.card ⊕ Fin Cᶜ.card) → ℝ) :
    (Finset.univ.filter fun v : {v : Fin n // v ∈ Cᶜ} =>
      coverDecodeWeights C y v.val ≠ 0).card =
    (Finset.univ.filter fun i : Fin Cᶜ.card => y (.inr i) ≠ 0).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h : (∑ i : Fin Cᶜ.card,
      if coverDecodeWeights C y (coverDecode C (.inr i)) ≠ 0 then (1 : ℕ) else 0)=
      ∑ v : {v : Fin n // v ∈ Cᶜ},
        if coverDecodeWeights C y v.val ≠ 0 then (1 : ℕ) else 0 :=
    Equiv.sum_comp (coverResidualIndex C)
      (fun v => if coverDecodeWeights C y v.val ≠ 0 then (1 : ℕ) else 0)
  simpa only [coverDecodeWeights, cover_encode_decode] using h.symm

theorem cover_executable_free_residual {n : ℕ} (C : Finset (Fin n))
    (lo hi : Fin n → Fin n → ℝ) (M : ℝ)
    (hc : intervalVertexCover (C : Set (Fin n)) lo hi M) :
    freeResidualIntervals (coverEncodeMatrix C lo) (coverEncodeMatrix C hi) M := by
  intro i j hij
  have hne : coverDecode C (.inr i) ≠ coverDecode C (.inr j) := by
    intro h
    have h' := congrArg (coverEncode C) h
    simp only [cover_encode_decode, Sum.inr.injEq] at h'
    exact hij h'
  by_contra hn
  have hbad : lo (coverDecode C (.inr i)) (coverDecode C (.inr j)) ≠ -M ∨
      hi (coverDecode C (.inr i)) (coverDecode C (.inr j)) ≠ M := by
    change ¬(lo (coverDecode C (.inr i)) (coverDecode C (.inr j))= -M ∧
      hi (coverDecode C (.inr i)) (coverDecode C (.inr j))=M) at hn
    tauto
  rcases hc _ _ ⟨hne, hbad⟩ with h | h
  · exact cover_decode_residual_not_mem C i h
  · exact cover_decode_residual_not_mem C j h

/-- All normalized compatible-game clauses are transported, including original
observation intervals, fixed anchor incident entries/responses, original zeros,
the supplied exact support bounds, and all residual moments. The hypotheses
are the literal split witness, rather than an assumed original-label outcome. -/
theorem cover_executable_full_witness {n d : ℕ} (C : Finset (Fin n))
    (A lo hi : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (F : Fin n → Fin d → ℝ)
    (y : (Fin C.card ⊕ Fin Cᶜ.card) → ℝ)
    (G : (Fin C.card ⊕ Fin Cᶜ.card) → (Fin C.card ⊕ Fin Cᶜ.card) → ℝ)
    (M ε : ℝ) (N T : ℕ)
    (hn : ∀ a, 0 ≤ y a) (hm : ∑ a, y a=1) (hsk : IsSkew G)
    (hb : ∀ a b, -M ≤ G a b ∧ G a b ≤ M)
    (hI : offDiagonalIntervals (coverEncodeMatrix C lo) (coverEncodeMatrix C hi) G)
    (hrows : ∀ a, response G y a ≤ ε)
    (ha : ∀ h, y (.inl h)=x (coverDecode C (.inl h)))
    (hz : ∀ i, x (coverDecode C (.inr i))=0 → y (.inr i)=0)
    (hc : (Finset.univ.filter fun i : Fin Cᶜ.card => y (.inr i) ≠ 0).card ≤ N)
    (ht : (Finset.univ.filter fun a => y a ≠ 0).card ≤ T)
    (hentries : ∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
      G a b=coverEncodeMatrix C A a b)
    (hanchors : ∀ h, response G y (.inl h)=response A x (coverDecode C (.inl h)))
    (hF : ∀ g, (∑ i : Fin Cᶜ.card, y (.inr i)*F (coverDecode C (.inr i)) g)=
      ∑ i : Fin Cᶜ.card, x (coverDecode C (.inr i))*F (coverDecode C (.inr i)) g) :
    let x' := coverDecodeWeights C y
    let A' := coverDecodeMatrix C G
    (∀ v, 0 ≤ x' v) ∧ (∑ v, x' v)=1 ∧ IsSkew A' ∧
      (∀ u v, -M ≤ A' u v ∧ A' u v ≤ M) ∧ offDiagonalIntervals lo hi A' ∧
      (∀ v, response A' x' v ≤ ε) ∧
      (∀ v, v ∈ C → x' v=x v) ∧
      (∀ v, v ∉ C → x v=0 → x' v=0) ∧
      (Finset.univ.filter fun v : {v : Fin n // v ∈ Cᶜ} => x' v.val ≠ 0).card ≤ N ∧
      (Finset.univ.filter fun v => x' v ≠ 0).card ≤ T ∧
      (∀ u v, u ∈ C ∨ v ∈ C → A' u v=A u v) ∧
      (∀ v, v ∈ C → response A' x' v=response A x v) ∧
      ∀ g, (∑ v : {v : Fin n // v ∈ Cᶜ}, x' v.val*F v.val g)=
        ∑ v : {v : Fin n // v ∈ Cᶜ}, x v.val*F v.val g := by
  classical
  dsimp only
  let e := coverExecutableEquiv C
  have hmass : (∑ v, coverDecodeWeights C y v)=∑ a, y a := relabel_mass e y
  have hresponse : ∀ v, response (coverDecodeMatrix C G) (coverDecodeWeights C y) v=
      response G y (coverEncode C v) := relabel_response e G y
  have hsupport : (Finset.univ.filter fun v => coverDecodeWeights C y v ≠ 0).card=
      (Finset.univ.filter fun a => y a ≠ 0).card := relabel_support_card e y
  refine ⟨fun v => hn _, hmass.trans hm, relabel_skew e G hsk,
    fun u v => hb _ _, ?_, fun v => (hresponse v).trans_le (hrows _),
    ?_, ?_, (cover_residual_support C y).trans_le hc, hsupport.trans_le ht, ?_, ?_, ?_⟩
  · intro u v huv
    have hne : coverEncode C u ≠ coverEncode C v := by
      intro he
      apply huv
      simpa only [cover_decode_encode] using congrArg (coverDecode C) he
    simpa only [coverEncodeMatrix, coverDecodeMatrix, cover_decode_encode] using
      hI (coverEncode C u) (coverEncode C v) hne
  · intro v hv
    let h := (coverAnchorIndex C).symm ⟨v, hv⟩
    have hdec : coverDecode C (.inl h)=v := by
      rw [← cover_encode_anchor C v hv]
      exact cover_decode_encode C v
    change y (coverEncode C v)=x v
    rw [cover_encode_anchor C v hv]
    exact (ha h).trans (congrArg x hdec)
  · intro v hv hzero
    let i := (coverResidualIndex C).symm ⟨v, Finset.mem_compl.mpr hv⟩
    have hdec : coverDecode C (.inr i)=v := by
      rw [← cover_encode_residual C v hv]
      exact cover_decode_encode C v
    change y (coverEncode C v)=0
    rw [cover_encode_residual C v hv]
    exact hz i (by rw [hdec]; exact hzero)
  · intro u v huv
    have hbranch : (∃ h, coverEncode C u=Sum.inl h) ∨
        ∃ h, coverEncode C v=Sum.inl h := by
      rcases huv with hu | hv
      · exact Or.inl ⟨_, cover_encode_anchor C u hu⟩
      · exact Or.inr ⟨_, cover_encode_anchor C v hv⟩
    simpa only [coverDecodeMatrix, coverEncodeMatrix, cover_decode_encode] using
      hentries (coverEncode C u) (coverEncode C v) hbranch
  · intro v hv
    rw [hresponse, cover_encode_anchor C v hv, hanchors]
    have hdec : coverDecode C
        (.inl ((coverAnchorIndex C).symm ⟨v, hv⟩))=v := by
      rw [← cover_encode_anchor C v hv]
      exact cover_decode_encode C v
    rw [hdec]
  · intro g
    rw [cover_residual_sum C (fun v => coverDecodeWeights C y v*F v g),
      cover_residual_sum C (fun v => x v*F v g)]
    simp only [coverDecodeWeights, cover_encode_decode]
    exact hF g

end SparseCompletion
