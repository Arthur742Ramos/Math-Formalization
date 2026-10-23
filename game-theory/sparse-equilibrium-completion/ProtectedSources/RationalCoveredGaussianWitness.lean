/- AI-assisted formalization under the repository Apache-2.0 license.
Source-only draft. Literal original-label contracts for the actually computed
supplied-cover Gaussian/graph-demand program. No runtime or height claim. -/
module
public import ProtectedSources.RationalCoveredGaussian
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalCoveredGaussianWitness {n d : ℕ} (C : Finset (Fin n))
    (A lo hi : Fin n → Fin n → ℚ) (E : Fin d → Fin n → ℚ) (x : Fin n → ℚ)
    (out : Gaussian.QVec n × Gaussian.QTable n n) (M ε : ℚ) (L : ℕ) : Prop :=
  let x' := fun v => (out.1.get v : ℝ)
  let A' := fun u v => (Gaussian.entry out.2 u v : ℝ)
  let x₀ := fun v => (x v : ℝ)
  let A₀ := fun u v => (A u v : ℝ)
  (∀ v, 0 ≤ x' v) ∧ (∑ v, x' v)=1 ∧ IsSkew A' ∧
    (∀ u v, -(M : ℝ) ≤ A' u v ∧ A' u v ≤ (M : ℝ)) ∧
    offDiagonalIntervals (fun u v => (lo u v : ℝ)) (fun u v => (hi u v : ℝ)) A' ∧
    (∀ v, response A' x' v ≤ (ε : ℝ)) ∧
    (∀ v, v ∈ C → x' v=x₀ v) ∧ (∀ v, v ∉ C → x₀ v=0 → x' v=0) ∧
    (Finset.univ.filter fun v : {v : Fin n // v ∈ Cᶜ} => x' v.val ≠ 0).card ≤
      min (Finset.univ.filter fun v : {v : Fin n // v ∈ Cᶜ} => x₀ v.val ≠ 0).card L ∧
    (Finset.univ.filter fun v => x' v ≠ 0).card ≤ min n (C.card+L) ∧
    (∀ u v, u ∈ C ∨ v ∈ C → A' u v=A₀ u v) ∧
    (∀ v, v ∈ C → response A' x' v=response A₀ x₀ v) ∧
    (∀ g, (∑ v : {v : Fin n // v ∈ Cᶜ}, x' v.val*(E g v.val : ℝ))=
      ∑ v : {v : Fin n // v ∈ Cᶜ}, x₀ v.val*(E g v.val : ℝ)) ∧
    (∑ v : {v : Fin n // v ∈ Cᶜ}, x' v.val)=
      ∑ v : {v : Fin n // v ∈ Cᶜ}, x₀ v.val

theorem rational_cover_cast_support {m : ℕ} (q : Fin m → ℚ) :
    (Finset.univ.filter fun i => (q i : ℝ) ≠ 0).card=(rationalWeightSupport q).card := by
  classical
  have heq : (Finset.univ.filter fun i => (q i : ℝ) ≠ 0)=rationalWeightSupport q := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rationalWeightSupport]
    constructor <;> intro h hz <;> apply h <;> exact_mod_cast hz
  exact congrArg Finset.card heq

theorem rational_cover_split_weights {n : ℕ} (C : Finset (Fin n)) (x : Fin n → ℚ) :
    coverEncodeWeights C (fun v => (x v : ℝ))=
      blockWeights (fun a => (rationalCoverAnchors (coverIndexTable C) x a : ℝ))
        (fun i => (rationalCoverWeights (coverIndexTable C) x i : ℝ)) := by
  funext a
  cases a <;> simp only [coverEncodeWeights, blockWeights, Sum.elim_inl, Sum.elim_inr,
    rationalCoverAnchors, rationalCoverWeights, cover_table_decode]

theorem rational_cover_split_matrix {n : ℕ} (C : Finset (Fin n))
    (A : Fin n → Fin n → ℚ) (hA : ∀ u v, A u v= -A v u) :
    coverEncodeMatrix C (fun u v => (A u v : ℝ))=
      blockMatrix (fun a b => (rationalCoverCore (coverIndexTable C) A a b : ℝ))
        (fun i a => (rationalCoverCross (coverIndexTable C) A i a : ℝ))
        (fun i j => (rationalCoverResidual (coverIndexTable C) A i j : ℝ)) := by
  funext a b
  cases a with
  | inl a =>
    cases b with
    | inl b => simp only [coverEncodeMatrix, blockMatrix, rationalCoverCore, cover_table_decode]
    | inr j =>
      simp only [coverEncodeMatrix, blockMatrix, rationalCoverCross, cover_table_decode]
      exact_mod_cast hA (coverDecode C (.inl a)) (coverDecode C (.inr j))
  | inr i =>
    cases b <;> simp only [coverEncodeMatrix, blockMatrix,
      rationalCoverCross, rationalCoverResidual, cover_table_decode]

theorem rational_cover_input_mass {n : ℕ} (C : Finset (Fin n)) (x : Fin n → ℚ)
    (hm : ∑ v, x v=1) :
    (∑ a, rationalCoverAnchors (coverIndexTable C) x a)+
      (∑ i, rationalCoverWeights (coverIndexTable C) x i)=1 := by
  have h := (Equiv.sum_comp (coverExecutableEquiv C) x).trans hm
  change (∑ a : Fin C.card ⊕ Fin Cᶜ.card, x (coverDecode C a))=1 at h
  simpa only [Fintype.sum_sum_type, rationalCoverAnchors,
    rationalCoverWeights, cover_table_decode] using h

theorem rational_cover_residual_mass {n : ℕ} (C : Finset (Fin n)) (x : Fin n → ℚ) :
    (∑ i, rationalCoverWeights (coverIndexTable C) x i)=
      ∑ v : {v : Fin n // v ∈ Cᶜ}, x v.val := by
  simpa only [rationalCoverWeights, cover_table_decode, coverDecode, Sum.elim_inr] using
    Equiv.sum_comp (coverResidualIndex C) (fun v => x v.val)

theorem rational_cover_input_rows {n : ℕ} (C : Finset (Fin n))
    (A : Fin n → Fin n → ℚ) (x : Fin n → ℚ) (ρ : ℚ)
    (hA : ∀ u v, A u v= -A v u)
    (hrows : ∀ v, response (fun u v => (A u v : ℝ)) (fun v => (x v : ℝ)) v ≤ (ρ : ℝ)) :
    ∀ a, response
      (blockMatrix (fun a b => (rationalCoverCore (coverIndexTable C) A a b : ℝ))
        (fun i a => (rationalCoverCross (coverIndexTable C) A i a : ℝ))
        (fun i j => (rationalCoverResidual (coverIndexTable C) A i j : ℝ)))
      (blockWeights (fun a => (rationalCoverAnchors (coverIndexTable C) x a : ℝ))
        (fun i => (rationalCoverWeights (coverIndexTable C) x i : ℝ))) a ≤ (ρ : ℝ) := by
  intro a
  rw [← rational_cover_split_matrix C A hA, ← rational_cover_split_weights C x]
  have h := relabel_response (coverExecutableEquiv C).symm
    (fun u v => (A u v : ℝ)) (fun v => (x v : ℝ)) a
  exact h.trans_le (hrows _)

theorem rational_cover_assemble_real {n : ℕ} (C : Finset (Fin n))
    (A : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (pair : Gaussian.QVec Cᶜ.card × RationalFlowTable Cᶜ.card) :
    (fun v => ((rationalCoverAssemble (coverIndexTable C) A x pair).1.get v : ℝ))=
      coverDecodeWeights C (blockWeights
        (fun a => (rationalCoverAnchors (coverIndexTable C) x a : ℝ))
        (fun i => (pair.1.get i : ℝ))) ∧
    (fun u v => (Gaussian.entry (rationalCoverAssemble (coverIndexTable C) A x pair).2 u v : ℝ))=
      coverDecodeMatrix C (blockMatrix
        (fun a b => (rationalCoverCore (coverIndexTable C) A a b : ℝ))
        (fun i a => (rationalCoverCross (coverIndexTable C) A i a : ℝ))
        (fun i j => (rationalFlowTableEntry pair.2 i j : ℝ))) := by
  constructor
  · funext v
    rw [rational_cover_assemble_weights, cover_table_encode]
    cases h : coverEncode C v <;>
      simp only [coverDecodeWeights, blockWeights, h, Sum.elim_inl, Sum.elim_inr]
  · funext u v
    rw [rational_cover_assemble_matrix, cover_table_encode, cover_table_encode,
      rational_cover_block_real]
    rfl

theorem rational_cover_assemble_unchanged_weights {n : ℕ} (C : Finset (Fin n))
    (A : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (pair : Gaussian.QVec Cᶜ.card × RationalFlowTable Cᶜ.card)
    (heq : pair.1.get=rationalCoverWeights (coverIndexTable C) x) :
    (rationalCoverAssemble (coverIndexTable C) A x pair).1.get=x := by
  have hw := (rational_cover_assemble_real C A x pair).1
  have hcast : (fun v => ((rationalCoverAssemble (coverIndexTable C) A x pair).1.get v : ℝ))=
      fun v => (x v : ℝ) := by
    rw [hw, heq, ← rational_cover_split_weights C x, cover_weights_roundtrip]
  funext v
  exact_mod_cast congrFun hcast v

/-- Proof adapter for the actual Gaussian pair contract. The final algorithms
below earn these hypotheses by invoking the existing executable solver theorem;
the algorithms accept only C,A,E,x,M,rho,eta and no desired witness. -/
theorem rational_cover_pair_transport {n d : ℕ} (C : Finset (Fin n))
    (A lo hi : Fin n → Fin n → ℚ) (E : Fin d → Fin n → ℚ) (x : Fin n → ℚ)
    (M ε : ℚ) (L : ℕ)
    (pair : Gaussian.QVec Cᶜ.card × RationalFlowTable Cᶜ.card)
    (hA : ∀ u v, A u v= -A v u)
    (hI : offDiagonalIntervals (fun u v => (lo u v : ℝ))
      (fun u v => (hi u v : ℝ)) (fun u v => (A u v : ℝ)))
    (hcover : intervalVertexCover (C : Set (Fin n))
      (fun u v => (lo u v : ℝ)) (fun u v => (hi u v : ℝ)) (M : ℝ))
    (hm : ∑ i, pair.1.get i=∑ i, rationalCoverWeights (coverIndexTable C) x i)
    (hz : ∀ i, rationalCoverWeights (coverIndexTable C) x i=0 → pair.1.get i=0)
    (hc : (rationalWeightSupport pair.1.get).card ≤
      min (rationalWeightSupport (rationalCoverWeights (coverIndexTable C) x)).card L)
    (hD : ∀ a, (∑ i, pair.1.get i*rationalCoverCross (coverIndexTable C) A i a)=
      ∑ i, rationalCoverWeights (coverIndexTable C) x i*rationalCoverCross (coverIndexTable C) A i a)
    (hE : ∀ g, (∑ i, pair.1.get i*rationalCoverExtras (coverIndexTable C) E g i)=
      ∑ i, rationalCoverWeights (coverIndexTable C) x i*rationalCoverExtras (coverIndexTable C) E g i)
    (hg : RationalGaussianPaperGame (rationalCoverCore (coverIndexTable C) A)
      (rationalCoverCross (coverIndexTable C) A) (rationalCoverAnchors (coverIndexTable C) x)
      pair M ε) :
    RationalCoveredGaussianWitness C A lo hi E x
      (rationalCoverAssemble (coverIndexTable C) A x pair) M ε L := by
  classical
  let table := coverIndexTable C
  let p := rationalCoverAnchors table x
  let q := rationalCoverWeights table x
  let K := rationalCoverCore table A
  let D := rationalCoverCross table A
  let B := rationalCoverResidual table A
  let B' := rationalFlowTableEntry pair.2
  let y := blockWeights (fun a => (p a : ℝ)) (fun i => (pair.1.get i : ℝ))
  let G := blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
    (fun i j => (B' i j : ℝ))
  let y₀ := blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))
  let G₀ := blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
    (fun i j => (B i j : ℝ))
  let xR := fun v => (x v : ℝ)
  let AR := fun u v => (A u v : ℝ)
  have hysplit : coverEncodeWeights C xR=y₀ := rational_cover_split_weights C x
  have hGsplit : coverEncodeMatrix C AR=G₀ := rational_cover_split_matrix C A hA
  obtain ⟨hyn, hym, hya, hGsk, hGb, hGrows⟩ := hg
  have hfree := cover_executable_free_residual C
    (fun u v => (lo u v : ℝ)) (fun u v => (hi u v : ℝ)) (M : ℝ) hcover
  have hI₀ : offDiagonalIntervals (coverEncodeMatrix C (fun u v => (lo u v : ℝ)))
      (coverEncodeMatrix C (fun u v => (hi u v : ℝ))) G₀ := by
    rw [← hGsplit]
    exact (relabel_intervals (coverExecutableEquiv C).symm _ _ _).mpr hI
  have hI' := cover_intervals_preserved
    (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
    (fun i j => (B i j : ℝ)) (fun i j => (B' i j : ℝ)) _ _ (M : ℝ)
    hfree hI₀ (fun i j => hGb (.inr i) (.inr j))
  have hzR : ∀ i, xR (coverDecode C (.inr i))=0 → y (.inr i)=0 := by
    intro i hi
    have hiQ : q i=0 := by
      have : (q i : ℝ)=0 := by
        simpa only [q, table, rationalCoverWeights, cover_table_decode, xR] using hi
      exact_mod_cast this
    change (pair.1.get i : ℝ)=0
    exact_mod_cast hz i hiQ
  have hcs : (Finset.univ.filter fun i : Fin Cᶜ.card => y (.inr i) ≠ 0).card ≤
      min (rationalWeightSupport q).card L := by
    simpa only [y, blockWeights, Sum.elim_inr, rational_cover_cast_support] using hc
  have hts : (Finset.univ.filter fun a => y a ≠ 0).card ≤ min n (C.card+L) := by
    apply le_min
    · have hcard : (Finset.univ : Finset (Fin C.card ⊕ Fin Cᶜ.card)).card=n := by
        simpa only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] using cover_partition_card C
      exact (Finset.card_filter_le _ _).trans (le_of_eq hcard)
    · rw [block_support_card]
      have hp : (Finset.univ.filter fun a => (p a : ℝ) ≠ 0).card ≤ C.card :=
        (Finset.card_filter_le _ _).trans (by simp)
      have hqL := hcs.trans (min_le_right _ _)
      exact Nat.add_le_add hp hqL
  have hentries : ∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
      G a b=coverEncodeMatrix C AR a b := by
    intro a b hab
    rw [hGsplit]
    exact anchor_incident_entries_preserved _ _ _ _ a b hab
  have hDreal : ∀ a, (∑ i, (pair.1.get i : ℝ)*(D i a : ℝ))=
      ∑ i, (q i : ℝ)*(D i a : ℝ) := by
    intro a
    exact_mod_cast hD a
  have hanchors : ∀ a, response G y (.inl a)=response AR xR (coverDecode C (.inl a)) := by
    intro a
    have ha : response G y (.inl a)=response G₀ y₀ (.inl a) := by
      rw [block_response_anchor, block_response_anchor]
      exact anchor_response_of_moments C.card (fun a b => (K a b : ℝ))
        (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))
        (fun i => (q i : ℝ)) (fun i => (pair.1.get i : ℝ)) hDreal a
    rw [← hGsplit, ← hysplit] at ha
    exact ha.trans (relabel_response (coverExecutableEquiv C).symm AR xR (.inl a))
  have hFreal : ∀ g, (∑ i : Fin Cᶜ.card, y (.inr i)*(E g (coverDecode C (.inr i)) : ℝ))=
      ∑ i : Fin Cᶜ.card, xR (coverDecode C (.inr i))*(E g (coverDecode C (.inr i)) : ℝ) := by
    intro g
    have he : (∑ i, (pair.1.get i : ℝ)*(rationalCoverExtras table E g i : ℝ))=
        ∑ i, (q i : ℝ)*(rationalCoverExtras table E g i : ℝ) := by exact_mod_cast hE g
    simpa only [y, blockWeights, Sum.elim_inr, rationalCoverExtras, q,
      rationalCoverWeights, table, cover_table_decode, xR] using he
  have hfull := cover_executable_full_witness C AR
    (fun u v => (lo u v : ℝ)) (fun u v => (hi u v : ℝ)) xR
    (fun v g => (E g v : ℝ)) y G (M : ℝ) (ε : ℝ)
    (min (rationalWeightSupport q).card L) (min n (C.card+L))
    hyn hym hGsk hGb hI' hGrows
    (fun a => by simp only [y, blockWeights, Sum.elim_inl, p, rationalCoverAnchors,
      table, cover_table_decode, xR]) hzR hcs hts hentries hanchors hFreal
  have holdcard : (Finset.univ.filter fun v : {v : Fin n // v ∈ Cᶜ} => xR v.val ≠ 0).card=
      (rationalWeightSupport q).card := by
    calc
      _ = (Finset.univ.filter fun v : {v : Fin n // v ∈ Cᶜ} =>
          coverDecodeWeights C (coverEncodeWeights C xR) v.val ≠ 0).card := by
        congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, cover_weights_roundtrip]
      _ = (Finset.univ.filter fun i : Fin Cᶜ.card =>
          coverEncodeWeights C xR (.inr i) ≠ 0).card :=
        cover_residual_support C (coverEncodeWeights C xR)
      _ = (Finset.univ.filter fun i => (q i : ℝ) ≠ 0).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro i _
        have heq : coverEncodeWeights C xR (.inr i)=(q i : ℝ) := by
          simp only [coverEncodeWeights, xR, q, rationalCoverWeights, table, cover_table_decode]
        rw [heq]
      _ = _ := rational_cover_cast_support q
  have hresmass : (∑ v : {v : Fin n // v ∈ Cᶜ}, coverDecodeWeights C y v.val)=
      ∑ v : {v : Fin n // v ∈ Cᶜ}, xR v.val := by
    rw [cover_residual_sum C, cover_residual_sum C]
    simp only [coverDecodeWeights, cover_encode_decode, y, blockWeights, Sum.elim_inr]
    have hmR : (∑ i, (pair.1.get i : ℝ))=∑ i, (q i : ℝ) := by exact_mod_cast hm
    simpa only [q, table, rationalCoverWeights, cover_table_decode, xR] using hmR
  obtain ⟨hw, hmat⟩ := rational_cover_assemble_real C A x pair
  unfold RationalCoveredGaussianWitness
  rw [hw, hmat]
  dsimp only
  change (Finset.univ.filter fun v : {v : Fin n // v ∈ Cᶜ} => (x v.val : ℝ) ≠ 0).card=
    (rationalWeightSupport q).card at holdcard
  rw [holdcard]
  obtain ⟨hn', hm', hsk', hb', hI'', hrows', ha', hz', hc', ht', he', hr', hF'⟩ := hfull
  exact ⟨hn', hm', hsk', hb', hI'', hrows', ha', hz', hc', ht', he', hr', hF', hresmass⟩

/-- The caller supplies only a rational feasible original game and a finite
cover of its constrained observation edges. Both the split witness and inverse
index properties are earned; the conclusion concerns the actual materialized
original-label program output. -/
theorem rational_covered_gaussian_general {n d : ℕ} (C : Finset (Fin n))
    (A lo hi : Fin n → Fin n → ℚ) (E : Fin d → Fin n → ℚ) (x : Fin n → ℚ)
    (M ρ η : ℚ) (hM : 0 < M) (hη : 0 < η)
    (hx : ∀ v, 0 ≤ x v) (hmass : ∑ v, x v=1)
    (hA : ∀ u v, A u v= -A v u) (hb : ∀ u v, -M ≤ A u v ∧ A u v ≤ M)
    (hI : offDiagonalIntervals (fun u v => (lo u v : ℝ))
      (fun u v => (hi u v : ℝ)) (fun u v => (A u v : ℝ)))
    (hcover : intervalVertexCover (C : Set (Fin n))
      (fun u v => (lo u v : ℝ)) (fun u v => (hi u v : ℝ)) (M : ℝ))
    (hrows : ∀ v, response (fun u v => (A u v : ℝ)) (fun v => (x v : ℝ)) v ≤ (ρ : ℝ)) :
    RationalCoveredGaussianWitness C A lo hi E x
      (rationalCoveredGaussianGeneral C A E x M ρ η) M (ρ+η)
      (C.card+d+1+gridSize (M : ℝ)
        ((∑ v : {v : Fin n // v ∈ Cᶜ}, x v.val : ℚ) : ℝ) (η : ℝ)) := by
  let table := coverIndexTable C
  let K := rationalCoverCore table A
  let D := rationalCoverCross table A
  let B := rationalCoverResidual table A
  let p := rationalCoverAnchors table x
  let q := rationalCoverWeights table x
  let E' := rationalCoverExtras table E
  let r := ∑ i, q i
  have hp : ∀ a, 0 ≤ p a := fun a => hx _
  have hq : ∀ i, 0 ≤ q i := fun i => hx _
  have hnorm : (∑ a, p a)+r=1 := rational_cover_input_mass C x hmass
  have hK : ∀ a b, K a b= -K b a := fun a b => hA _ _
  have hB : ∀ i j, B i j= -B j i := fun i j => hA _ _
  have hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M := fun a b => hb _ _
  have hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M := fun i a => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun i j => hb _ _
  obtain ⟨_, hm, hz, hc, hD, hE, _, hg⟩ :=
    rational_gaussian_paper_general_algorithm K D E' B p q M r ρ η hM hη hp hq rfl
      hnorm hK hB hKb hDb hBb (rational_cover_input_rows C A x ρ hA hrows)
  have h := rational_cover_pair_transport C A lo hi E x M (ρ+η)
    (C.card+d+1+gridSize (M : ℝ) (r : ℝ) (η : ℝ))
    (rationalGaussianPaperGeneralFlow D E' p q M r ρ η)
    hA hI hcover hm hz hc hD hE hg
  simpa only [rationalCoveredGaussianGeneral, r, q, table,
    rational_cover_residual_mass] using h

/-- Exact-input sharpening uses H-1 hinges and the same original observations.
Positive residual mass and the zero-mass case are stated separately. -/
theorem rational_covered_gaussian_exact {n d : ℕ} (C : Finset (Fin n))
    (A lo hi : Fin n → Fin n → ℚ) (E : Fin d → Fin n → ℚ) (x : Fin n → ℚ)
    (M η : ℚ) (hM : 0 < M) (hη : 0 < η)
    (hr : 0 < ∑ v : {v : Fin n // v ∈ Cᶜ}, x v.val)
    (hx : ∀ v, 0 ≤ x v) (hmass : ∑ v, x v=1)
    (hA : ∀ u v, A u v= -A v u) (hb : ∀ u v, -M ≤ A u v ∧ A u v ≤ M)
    (hI : offDiagonalIntervals (fun u v => (lo u v : ℝ))
      (fun u v => (hi u v : ℝ)) (fun u v => (A u v : ℝ)))
    (hcover : intervalVertexCover (C : Set (Fin n))
      (fun u v => (lo u v : ℝ)) (fun u v => (hi u v : ℝ)) (M : ℝ))
    (hrows : ∀ v, response (fun u v => (A u v : ℝ)) (fun v => (x v : ℝ)) v ≤ 0) :
    RationalCoveredGaussianWitness C A lo hi E x
      (rationalCoveredGaussianExact C A E x M η) M η
      (C.card+d+gridSize (M : ℝ)
        ((∑ v : {v : Fin n // v ∈ Cᶜ}, x v.val : ℚ) : ℝ) (η : ℝ)) := by
  let table := coverIndexTable C
  let K := rationalCoverCore table A
  let D := rationalCoverCross table A
  let B := rationalCoverResidual table A
  let p := rationalCoverAnchors table x
  let q := rationalCoverWeights table x
  let E' := rationalCoverExtras table E
  let r := ∑ i, q i
  have hp : ∀ a, 0 ≤ p a := fun a => hx _
  have hq : ∀ i, 0 ≤ q i := fun i => hx _
  have hr' : 0 < r := by simpa only [r, q, table, rational_cover_residual_mass] using hr
  have hnorm : (∑ a, p a)+r=1 := rational_cover_input_mass C x hmass
  have hK : ∀ a b, K a b= -K b a := fun a b => hA _ _
  have hB : ∀ i j, B i j= -B j i := fun i j => hA _ _
  have hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M := fun a b => hb _ _
  have hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M := fun i a => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun i j => hb _ _
  obtain ⟨_, hm, hz, hc, hD, hE, _, hg⟩ :=
    rational_gaussian_paper_exact_algorithm K D E' B p q M r η hM hr' hη hp hq rfl
      hnorm hK hB hKb hDb hBb (by simpa only [Rat.cast_zero] using rational_cover_input_rows C A x 0 hA (by simpa only [Rat.cast_zero] using hrows))
  have h := rational_cover_pair_transport C A lo hi E x M η
    (C.card+d+gridSize (M : ℝ) (r : ℝ) (η : ℝ))
    (rationalGaussianPaperExactFlow D E' p q M r η)
    hA hI hcover hm hz hc hD hE hg
  simpa only [rationalCoveredGaussianExact, r, q, table,
    rational_cover_residual_mass] using h

theorem rational_covered_gaussian_zero {n d : ℕ} (C : Finset (Fin n))
    (A lo hi : Fin n → Fin n → ℚ) (E : Fin d → Fin n → ℚ) (x : Fin n → ℚ)
    (M η : ℚ) (hM : 0 < M) (hη : 0 < η)
    (hr : (∑ v : {v : Fin n // v ∈ Cᶜ}, x v.val)=0)
    (hx : ∀ v, 0 ≤ x v) (hmass : ∑ v, x v=1)
    (hA : ∀ u v, A u v= -A v u) (hb : ∀ u v, -M ≤ A u v ∧ A u v ≤ M)
    (hI : offDiagonalIntervals (fun u v => (lo u v : ℝ))
      (fun u v => (hi u v : ℝ)) (fun u v => (A u v : ℝ)))
    (hcover : intervalVertexCover (C : Set (Fin n))
      (fun u v => (lo u v : ℝ)) (fun u v => (hi u v : ℝ)) (M : ℝ))
    (hrows : ∀ v, response (fun u v => (A u v : ℝ)) (fun v => (x v : ℝ)) v ≤ 0) :
    (rationalCoveredGaussianExact C A E x M η).1.get=x ∧
    RationalCoveredGaussianWitness C A lo hi E x
      (rationalCoveredGaussianExact C A E x M η) M η
      (C.card+d+gridSize (M : ℝ) 0 (η : ℝ)) := by
  let table := coverIndexTable C
  let K := rationalCoverCore table A
  let D := rationalCoverCross table A
  let B := rationalCoverResidual table A
  let p := rationalCoverAnchors table x
  let q := rationalCoverWeights table x
  let E' := rationalCoverExtras table E
  have hp : ∀ a, 0 ≤ p a := fun a => hx _
  have hq : ∀ i, 0 ≤ q i := fun i => hx _
  have hm₀ : (∑ i, q i)=0 := by
    simpa only [q, table, rational_cover_residual_mass] using hr
  have hnorm : (∑ a, p a)+0=1 := by
    have h := rational_cover_input_mass C x hmass
    change (∑ a, p a)+(∑ i, q i)=1 at h
    rwa [hm₀] at h
  have hK : ∀ a b, K a b= -K b a := fun a b => hA _ _
  have hB : ∀ i j, B i j= -B j i := fun i j => hA _ _
  have hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M := fun a b => hb _ _
  have hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M := fun i a => hb _ _
  have hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M := fun i j => hb _ _
  let pair := rationalGaussianPaperExactFlow D E' p q M 0 η
  obtain ⟨heq, hcard, _, hg⟩ := rational_gaussian_paper_zero_algorithm K D E' B p q M η
    hM hη hp hq hm₀ hnorm hK hB hKb hDb hBb (by simpa only [Rat.cast_zero] using rational_cover_input_rows C A x 0 hA (by simpa only [Rat.cast_zero] using hrows))
  have hm : (∑ i, pair.1.get i)=∑ i, q i := by rw [heq]
  have hz : ∀ i, q i=0 → pair.1.get i=0 := by rw [heq]; exact fun _ h => h
  have hc : (rationalWeightSupport pair.1.get).card ≤
      min (rationalWeightSupport q).card (C.card+d+gridSize (M : ℝ) 0 (η : ℝ)) := by
    rw [hcard]
    exact Nat.zero_le _
  have hD : ∀ a, (∑ i, pair.1.get i*D i a)=∑ i, q i*D i a := by
    rw [heq]; exact fun _ => rfl
  have hE : ∀ g, (∑ i, pair.1.get i*E' g i)=∑ i, q i*E' g i := by
    rw [heq]; exact fun _ => rfl
  have h := rational_cover_pair_transport C A lo hi E x M η
    (C.card+d+gridSize (M : ℝ) 0 (η : ℝ)) pair
    hA hI hcover hm hz hc hD hE hg
  have hsame := rational_cover_assemble_unchanged_weights C A x pair heq
  have hmC : (∑ i, rationalCoverWeights (coverIndexTable C) x i)=0 := hm₀
  constructor
  · simpa only [rationalCoveredGaussianExact, pair, D, E', p, q, table, hmC] using hsame
  · simpa only [rationalCoveredGaussianExact, pair, D, E', p, q, table, hmC] using h

end SparseCompletion
