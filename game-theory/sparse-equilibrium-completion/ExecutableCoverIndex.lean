/- AI-assisted formalization under the repository Apache-2.0 license.
Source-only draft. Deterministic finite cover indexing on the original Fin n
labels. Enumeration uses sorted-list get/idxOf, with no choice-based equivFin. -/
module
public import CoverRelabel
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Vector.Basic
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def coverAnchorIndex {n : ℕ} (C : Finset (Fin n)) :
    Fin C.card ≃ {v : Fin n // v ∈ C} :=
  (C.orderIsoOfFin rfl).toEquiv

def coverResidualIndex {n : ℕ} (C : Finset (Fin n)) :
    Fin Cᶜ.card ≃ {v : Fin n // v ∈ Cᶜ} :=
  ((Cᶜ).orderIsoOfFin rfl).toEquiv

def coverDecode {n : ℕ} (C : Finset (Fin n)) :
    (Fin C.card ⊕ Fin Cᶜ.card) → Fin n :=
  Sum.elim (fun h => (coverAnchorIndex C h).val)
    (fun i => (coverResidualIndex C i).val)

def coverEncode {n : ℕ} (C : Finset (Fin n)) (v : Fin n) :
    Fin C.card ⊕ Fin Cᶜ.card :=
  if hv : v ∈ C then .inl ((coverAnchorIndex C).symm ⟨v, hv⟩)
  else .inr ((coverResidualIndex C).symm ⟨v, Finset.mem_compl.mpr hv⟩)

theorem cover_decode_anchor_mem {n : ℕ} (C : Finset (Fin n)) (h : Fin C.card) :
    coverDecode C (.inl h) ∈ C :=
  (coverAnchorIndex C h).property

theorem cover_decode_residual_not_mem {n : ℕ} (C : Finset (Fin n)) (i : Fin Cᶜ.card) :
    coverDecode C (.inr i) ∉ C :=
  Finset.mem_compl.mp (coverResidualIndex C i).property

theorem cover_encode_decode {n : ℕ} (C : Finset (Fin n))
    (a : Fin C.card ⊕ Fin Cᶜ.card) : coverEncode C (coverDecode C a)=a := by
  cases a with
  | inl h =>
    unfold coverEncode
    rw [dite_eq_left (cover_decode_anchor_mem C h)]
    congr 1
    exact (coverAnchorIndex C).symm_apply_apply h
  | inr i =>
    unfold coverEncode
    rw [dite_eq_right (cover_decode_residual_not_mem C i)]
    congr 1
    exact (coverResidualIndex C).symm_apply_apply i

theorem cover_decode_encode {n : ℕ} (C : Finset (Fin n)) (v : Fin n) :
    coverDecode C (coverEncode C v)=v := by
  by_cases hv : v ∈ C
  · rw [coverEncode, dite_eq_left hv]
    exact congrArg Subtype.val ((coverAnchorIndex C).apply_symm_apply ⟨v, hv⟩)
  · rw [coverEncode, dite_eq_right hv]
    exact congrArg Subtype.val
      ((coverResidualIndex C).apply_symm_apply ⟨v, Finset.mem_compl.mpr hv⟩)

/-- The equivalence is earned from the actual branch-based encoder and the
sorted enumerations; callers do not supply an inverse or equivalence oracle. -/
def coverExecutableEquiv {n : ℕ} (C : Finset (Fin n)) :
    (Fin C.card ⊕ Fin Cᶜ.card) ≃ Fin n where
  toFun := coverDecode C
  invFun := coverEncode C
  left_inv := cover_encode_decode C
  right_inv := cover_decode_encode C

theorem cover_partition_card {n : ℕ} (C : Finset (Fin n)) : C.card+Cᶜ.card=n := by
  have h := Fintype.card_congr (coverExecutableEquiv C)
  simpa only [Fintype.card_sum, Fintype.card_fin] using h

theorem cover_encode_anchor {n : ℕ} (C : Finset (Fin n)) (v : Fin n) (hv : v ∈ C) :
    coverEncode C v=.inl ((coverAnchorIndex C).symm ⟨v, hv⟩) := by
  exact dite_eq_left hv

theorem cover_encode_residual {n : ℕ} (C : Finset (Fin n)) (v : Fin n) (hv : v ∉ C) :
    coverEncode C v=.inr ((coverResidualIndex C).symm ⟨v, Finset.mem_compl.mpr hv⟩) := by
  exact dite_eq_right hv

def coverEncodeWeights {n : ℕ} {R : Type*} (C : Finset (Fin n)) (x : Fin n → R) :
    (Fin C.card ⊕ Fin Cᶜ.card) → R := fun a => x (coverDecode C a)

def coverDecodeWeights {n : ℕ} {R : Type*} (C : Finset (Fin n))
    (x : (Fin C.card ⊕ Fin Cᶜ.card) → R) : Fin n → R := fun v => x (coverEncode C v)

def coverEncodeMatrix {n : ℕ} {R : Type*} (C : Finset (Fin n)) (A : Fin n → Fin n → R) :
    (Fin C.card ⊕ Fin Cᶜ.card) → (Fin C.card ⊕ Fin Cᶜ.card) → R :=
  fun a b => A (coverDecode C a) (coverDecode C b)

def coverDecodeMatrix {n : ℕ} {R : Type*} (C : Finset (Fin n))
    (A : (Fin C.card ⊕ Fin Cᶜ.card) → (Fin C.card ⊕ Fin Cᶜ.card) → R) :
    Fin n → Fin n → R := fun u v => A (coverEncode C u) (coverEncode C v)

theorem cover_weights_roundtrip {n : ℕ} {R : Type*} (C : Finset (Fin n)) (x : Fin n → R) :
    coverDecodeWeights C (coverEncodeWeights C x)=x := by
  funext v
  simp only [coverDecodeWeights, coverEncodeWeights, cover_decode_encode]

theorem cover_matrix_roundtrip {n : ℕ} {R : Type*} (C : Finset (Fin n))
    (A : Fin n → Fin n → R) : coverDecodeMatrix C (coverEncodeMatrix C A)=A := by
  funext u v
  simp only [coverDecodeMatrix, coverEncodeMatrix, cover_decode_encode]

theorem cover_weights_encode_roundtrip {n : ℕ} {R : Type*} (C : Finset (Fin n))
    (x : (Fin C.card ⊕ Fin Cᶜ.card) → R) :
    coverEncodeWeights C (coverDecodeWeights C x)=x := by
  funext a
  simp only [coverDecodeWeights, coverEncodeWeights, cover_encode_decode]

theorem cover_matrix_encode_roundtrip {n : ℕ} {R : Type*} (C : Finset (Fin n))
    (A : (Fin C.card ⊕ Fin Cᶜ.card) → (Fin C.card ⊕ Fin Cᶜ.card) → R) :
    coverEncodeMatrix C (coverDecodeMatrix C A)=A := by
  funext a b
  simp only [coverDecodeMatrix, coverEncodeMatrix, cover_encode_decode]

/-- Runtime data only. Inverse and partition proofs are earned below, rather
than accepted as fields of a caller-supplied equivalence. -/
structure CoverIndexTable (n k m : ℕ) where
  anchors : List.Vector (Fin n) k
  residuals : List.Vector (Fin n) m
  codes : List.Vector (Fin k ⊕ Fin m) n

def coverIndexTable {n : ℕ} (C : Finset (Fin n)) : CoverIndexTable n C.card Cᶜ.card where
  anchors := List.Vector.ofFn (fun h => coverDecode C (.inl h))
  residuals := List.Vector.ofFn (fun i => coverDecode C (.inr i))
  codes := List.Vector.ofFn (coverEncode C)

def coverTableDecode {n k m : ℕ} (table : CoverIndexTable n k m) :
    (Fin k ⊕ Fin m) → Fin n := Sum.elim table.anchors.get table.residuals.get

def coverTableEncode {n k m : ℕ} (table : CoverIndexTable n k m) :
    Fin n → (Fin k ⊕ Fin m) := table.codes.get

theorem cover_table_decode {n : ℕ} (C : Finset (Fin n))
    (a : Fin C.card ⊕ Fin Cᶜ.card) :
    coverTableDecode (coverIndexTable C) a=coverDecode C a := by
  cases a <;> simp only [coverTableDecode, coverIndexTable, Sum.elim_inl, Sum.elim_inr,
    List.Vector.get_ofFn]

theorem cover_table_encode {n : ℕ} (C : Finset (Fin n)) (v : Fin n) :
    coverTableEncode (coverIndexTable C) v=coverEncode C v := by
  simp only [coverTableEncode, coverIndexTable, List.Vector.get_ofFn]

theorem cover_table_encode_decode {n : ℕ} (C : Finset (Fin n))
    (a : Fin C.card ⊕ Fin Cᶜ.card) :
    coverTableEncode (coverIndexTable C) (coverTableDecode (coverIndexTable C) a)=a := by
  rw [cover_table_decode, cover_table_encode, cover_encode_decode]

theorem cover_table_decode_encode {n : ℕ} (C : Finset (Fin n)) (v : Fin n) :
    coverTableDecode (coverIndexTable C) (coverTableEncode (coverIndexTable C) v)=v := by
  rw [cover_table_encode, cover_table_decode, cover_decode_encode]

end SparseCompletion
