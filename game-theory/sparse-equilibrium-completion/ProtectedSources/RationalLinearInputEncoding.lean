/- AI-assisted formalization under repository Apache-2.0.
Compositional input heights for literal linear forms, finite repertoire
append, and explicit coordinate-tagged dense LP value encodings. -/
module
public import ProtectedSources.RationalGapInputHeight
public import ProtectedSources.RationalIntervalRepertoire
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_form_add_input_height {n A B : ℕ} (c d : Fin n → ℚ)
    (hc : ∀ u, RationalInputHeight (c u) A) (hd : ∀ u, RationalInputHeight (d u) B) :
    ∀ u, RationalInputHeight (rationalFormAdd c d u) (2*(A+B)+1) :=
  fun u => rational_input_height_add (hc u) (hd u)

theorem rational_form_scale_input_height {n A B : ℕ} (a : ℚ) (c : Fin n → ℚ)
    (ha : RationalInputHeight a A) (hc : ∀ u, RationalInputHeight (c u) B) :
    ∀ u, RationalInputHeight (rationalFormScale a c u) (2*(A+B)) :=
  fun u => rational_input_height_mul ha (hc u)

theorem rational_form_fin_sum_input_height {n t B : ℕ} (c : Fin t → Fin n → ℚ)
    (hc : ∀ j u, RationalInputHeight (c j u) B) :
    ∀ u, RationalInputHeight (rationalFormSum c u) (t+B*(t+1)) :=
  fun u => rational_input_height_fin_sum (fun j => c j u) (fun j => hc j u)

theorem rational_interval_basis_input_height {k m H : ℕ}
    (v : RationalIntervalVariable k m H) (u : Fin (m+(m*k+(k*k+H*m)))) :
    RationalInputHeight (intervalBasis v u) 0 := by
  unfold intervalBasis
  split
  · exact rational_input_height_one 0
  · exact rational_input_height_zero 0

/-- A canonical binary width for an enumerated finite coordinate. The zero
dimension has width one; its absence of coordinate entries is counted below. -/
def rationalLPIndexWidth (n : ℕ) : ℕ := Nat.log2 n+1

theorem rational_lp_actual_index_bits_le {n : ℕ} (i : Fin n) :
    Nat.log2 i.val+1 ≤ rationalLPIndexWidth n := by
  unfold rationalLPIndexWidth
  by_cases hi : i.val=0
  · simp only [hi, Nat.log2_zero, zero_add]
    omega
  · have hlt := (Nat.log2_lt hi).mpr (i.isLt.trans (Nat.lt_log2_self))
    omega

/-- Declared dense serialization: every rational scalar has a fixed-width
row and column coordinate tag. RHS scalars use column n in Fin(n+1).
This counts these explicit tags, not Lean heap objects or arithmetic cost. -/
def rationalIndexedLinearSystemEncodingBits {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) : ℕ :=
  rationalLinearSystemEncodingBits S + Fintype.card I*(n+1)*
    (rationalLPIndexWidth (Fintype.card I)+rationalLPIndexWidth (n+1))

theorem rational_indexed_system_encoding_bits_of_entry_bound {I : Type*} [Fintype I]
    {n H : ℕ} (S : RationalLinearSystem I n)
    (hc : ∀ row i, RationalInputHeight (S.coefficient row i) H)
    (hr : ∀ row, RationalInputHeight (S.rightSide row) H) :
    rationalIndexedLinearSystemEncodingBits S ≤ Fintype.card I*(n+1)*
      (2*H+3+rationalLPIndexWidth (Fintype.card I)+rationalLPIndexWidth (n+1)) := by
  have hh := rational_linear_system_encoding_bits_of_entry_bound S hc hr
  unfold rationalIndexedLinearSystemEncodingBits
  calc
    _ ≤ Fintype.card I*(n+1)*(2*H+3) + Fintype.card I*(n+1)*
        (rationalLPIndexWidth (Fintype.card I)+rationalLPIndexWidth (n+1)) :=
      Nat.add_le_add_right hh _
    _ = _ := by ring

theorem rational_index_width_dimension_bound (n : ℕ) : rationalLPIndexWidth n ≤ n+1 := by
  unfold rationalLPIndexWidth
  exact Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem rational_indexed_system_polynomial_encoding_bits_of_entry_bound
    {I : Type*} [Fintype I] {n H : ℕ} (S : RationalLinearSystem I n)
    (hc : ∀ row i, RationalInputHeight (S.coefficient row i) H)
    (hr : ∀ row, RationalInputHeight (S.rightSide row) H) :
    rationalIndexedLinearSystemEncodingBits S ≤
      Fintype.card I*(n+1)*(2*H+Fintype.card I+n+6) := by
  have hh := rational_indexed_system_encoding_bits_of_entry_bound S hc hr
  have hrow := rational_index_width_dimension_bound (Fintype.card I)
  have hcol := rational_index_width_dimension_bound (n+1)
  exact hh.trans (Nat.mul_le_mul_left (Fintype.card I*(n+1)) (by omega))

theorem rational_linear_append_input_height {I J : Type*} {n A B : ℕ}
    (S : RationalLinearSystem I n) (R : RationalLinearSystem J n)
    (hc : ∀ row i, RationalInputHeight (S.coefficient row i) A)
    (hs : ∀ row, RationalInputHeight (S.rightSide row) A)
    (hR : ∀ row i, RationalInputHeight (R.coefficient row i) B)
    (hb : ∀ row, RationalInputHeight (R.rightSide row) B) :
    (∀ row i, RationalInputHeight ((S.append R).coefficient row i) (A+B)) ∧
      ∀ row, RationalInputHeight ((S.append R).rightSide row) (A+B) := by
  constructor
  · rintro (row | row) i
    · exact rational_input_height_mono (hc row i) (by omega)
    · exact rational_input_height_mono (hR row i) (by omega)
  · rintro (row | row)
    · exact rational_input_height_mono (hs row) (by omega)
    · exact rational_input_height_mono (hb row) (by omega)

theorem rational_linear_append_value_encoding_bits {I J : Type*} [Fintype I] [Fintype J]
    {n : ℕ} (S : RationalLinearSystem I n) (R : RationalLinearSystem J n) :
    rationalLinearSystemEncodingBits (S.append R) =
      rationalLinearSystemEncodingBits S+rationalLinearSystemEncodingBits R := by
  simp only [rationalLinearSystemEncodingBits, Fintype.sum_sum_type,
    RationalLinearSystem.append, Sum.elim_inl, Sum.elim_inr]

end SparseCompletion
