/- AI-assisted formalization under repository Apache-2.0.
Input-derived bounds for all actual interval LP rows: physical bounds,
anchor rows, global guards, and perspective epigraph constraints. -/
module
public import ProtectedSources.RationalLinearInputEncoding
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalIntervalInputHeight (k m B : ℕ) : ℕ := 65536*(k+m+1)*(B+1)
def rationalIntervalVariableCount (k m H : ℕ) : ℕ := m+(m*k+(k*k+H*m))
def rationalIntervalRowCount (k m H : ℕ) : ℕ := 3*m+2+2*m*k+4*k*k+k+2*H*m+H

theorem rational_interval_variable_count (k m H : ℕ) :
    Fintype.card (Fin (m+(m*k+(k*k+H*m)))) = rationalIntervalVariableCount k m H := by
  simp only [Fintype.card_fin, rationalIntervalVariableCount]

theorem rational_interval_rows_exact_count (k m H : ℕ) :
    Fintype.card (RationalIntervalRows k m H) = rationalIntervalRowCount k m H :=
  rational_interval_row_count k m H

theorem rational_interval_coefficient_input_height {k m B : ℕ}
    (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (hlo : ∀ i a, RationalInputHeight (lo i a) B)
    (hhi : ∀ i a, RationalInputHeight (hi i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (row : RationalIntervalRows k m (rationalGridSize M r η))
    (u : Fin (m+(m*k+(k*k+rationalGridSize M r η*m)))) :
    RationalInputHeight (rationalIntervalCoefficient (rationalGridSize M r η) lo hi p M r ρ η row u)
      (rationalIntervalInputHeight k m B) := by
  let H := rationalGridSize M r η
  have hQ : ∀ i v, RationalInputHeight (intervalQForm k m H i v) 0 :=
    fun i v => rational_interval_basis_input_height (.inl i) v
  have hV : ∀ i a v, RationalInputHeight (intervalVForm k m H i a v) 0 :=
    fun i a v => rational_interval_basis_input_height (.inr (.inl (i,a))) v
  have hK : ∀ a b v, RationalInputHeight (intervalKForm k m H a b v) 0 :=
    fun a b v => rational_interval_basis_input_height (.inr (.inr (.inl (a,b)))) v
  have hA : ∀ l i v, RationalInputHeight (intervalAuxForm k m H l i v) 0 :=
    fun l i v => rational_interval_basis_input_height (.inr (.inr (.inr (l,i)))) v
  have hneg := rational_input_height_neg (rational_input_height_one 0)
  have hscore (i : Fin m) : RationalInputHeight
      (rationalFormSum (fun a => rationalFormScale (p a) (intervalVForm k m H i a)) u)
      (k+2*B*(k+1)) := by
    apply rational_input_height_fin_sum
    intro a
    simpa only [Nat.add_zero, rationalFormScale] using rational_input_height_mul (hp a) (hV i a u)
  have hcore (a : Fin k) : RationalInputHeight
      (rationalFormSum (fun b => rationalFormScale (p b) (intervalKForm k m H a b)) u)
      (k+2*B*(k+1)) := by
    apply rational_input_height_fin_sum
    intro b
    simpa only [Nat.add_zero, rationalFormScale] using rational_input_height_mul (hp b) (hK a b u)
  have hQsum : RationalInputHeight (rationalFormSum (intervalQForm k m H) u) m := by
    simpa using rational_form_fin_sum_input_height (intervalQForm k m H) hQ u
  have hVsum (a : Fin k) : RationalInputHeight
      (rationalFormSum (fun i => intervalVForm k m H i a) u) m := by
    simpa using rational_form_fin_sum_input_height (fun i => intervalVForm k m H i a)
      (fun i v => hV i a v) u
  have hAsum (l : Fin H) : RationalInputHeight
      (rationalFormSum (intervalAuxForm k m H l) u) m := by
    simpa using rational_form_fin_sum_input_height (intervalAuxForm k m H l)
      (fun i v => hA l i v) u
  have hb0 : 0 ≤ rationalIntervalInputHeight k m B := Nat.zero_le _
  rcases row with i | row
  · exact rational_input_height_mono (rational_input_height_mul hneg (hQ i u)) hb0
  · rcases row with s | row
    · have hsign : RationalInputHeight (if s.val=0 then (1 : ℚ) else -1) 0 := by
        split
        · exact rational_input_height_one 0
        · exact hneg
      apply rational_input_height_mono (rational_input_height_mul hsign hQsum)
      unfold rationalIntervalInputHeight
      nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
    · rcases row with row | rows
      · simp only [rationalIntervalCoefficient, Sum.elim_inr, Sum.elim_inl]
        split
        · apply rational_input_height_mono
            (rational_input_height_add (rational_input_height_mul (hlo row.2.1 row.2.2) (hQ row.2.1 u))
              (rational_input_height_mul hneg (hV row.2.1 row.2.2 u)))
          unfold rationalIntervalInputHeight
          nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
        · apply rational_input_height_mono
            (rational_input_height_add (hV row.2.1 row.2.2 u)
              (rational_input_height_mul (rational_input_height_neg (hhi row.2.1 row.2.2)) (hQ row.2.1 u)))
          unfold rationalIntervalInputHeight
          nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
      · rcases rows with row | rows
        · simp only [rationalIntervalCoefficient, Sum.elim_inr, Sum.elim_inl]
          split
          · exact rational_input_height_mono (rational_input_height_add (hK row.2.1 row.2.2 u)
              (hK row.2.2 row.2.1 u)) (by unfold rationalIntervalInputHeight; nlinarith)
          · split
            · exact rational_input_height_mono
                (rational_input_height_mul hneg (rational_input_height_add
                  (hK row.2.1 row.2.2 u) (hK row.2.2 row.2.1 u)))
                (by unfold rationalIntervalInputHeight; nlinarith)
            · split
              · exact rational_input_height_mono (rational_input_height_mul hneg (hK row.2.1 row.2.2 u)) hb0
              · exact rational_input_height_mono (hK row.2.1 row.2.2 u) hb0
        · rcases rows with a | rows
          · apply rational_input_height_mono
              (rational_input_height_add (hcore a) (rational_input_height_mul hneg (hVsum a)))
            unfold rationalIntervalInputHeight
            nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
          · rcases rows with i | rows
            · exact rational_input_height_zero _
            · rcases rows with i | rows
              · apply rational_input_height_mono (rational_input_height_add (hscore i)
                  (rational_input_height_mul (rational_input_height_neg
                    (rational_input_height_add hρ (rational_input_height_mul hM hr))) (hQ i u)))
                unfold rationalIntervalInputHeight
                nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
              · rcases rows with row | l
                · simp only [rationalIntervalCoefficient, Sum.elim_inr, Sum.elim_inl]
                  split
                  · exact rational_input_height_mono (rational_input_height_mul hneg (hA row.2.1 row.2.2 u)) hb0
                  · have hthreshold := rational_grid_threshold_input_height M r η B (10*B+1)
                      (row.2.1.val+1) hM hr hη (rational_grid_row_endpoint_input_bound hM hr hη row.2.1)
                    apply rational_input_height_mono
                      (rational_input_height_add (rational_input_height_add (hscore row.2.2)
                        (rational_input_height_mul (rational_input_height_neg
                          (rational_input_height_add hρ hthreshold)) (hQ row.2.2 u)))
                        (rational_input_height_mul hneg (hA row.2.1 row.2.2 u)))
                    unfold rationalGridThresholdInputHeight rationalGridNodeInputHeight rationalIntervalInputHeight
                    nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
                · exact rational_input_height_mono (hAsum l)
                    (by unfold rationalIntervalInputHeight; nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)])

theorem rational_interval_right_side_input_height {k m B : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ)
    (hlK : ∀ a b, RationalInputHeight (loK a b) B)
    (hhK : ∀ a b, RationalInputHeight (hiK a b) B)
    (hlo : ∀ i a, RationalInputHeight (lo i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (row : RationalIntervalRows k m (rationalGridSize M r η)) :
    RationalInputHeight (rationalIntervalRightSide (rationalGridSize M r η) loK hiK lo p M r ρ η row)
      (rationalIntervalInputHeight k m B) := by
  have hbase : B ≤ rationalIntervalInputHeight k m B := by
    unfold rationalIntervalInputHeight
    nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
  have hz := rational_input_height_zero (rationalIntervalInputHeight k m B)
  rcases row with i | row
  · exact hz
  · rcases row with s | row
    · simp only [rationalIntervalRightSide, Sum.elim_inr, Sum.elim_inl]
      split
      · exact rational_input_height_mono hr hbase
      · exact rational_input_height_mono (rational_input_height_neg hr) hbase
    · rcases row with row | rows
      · exact hz
      · rcases rows with row | rows
        · simp only [rationalIntervalRightSide, Sum.elim_inr, Sum.elim_inl]
          split
          · exact hz
          · split
            · exact hz
            · split
              · exact rational_input_height_mono (rational_input_height_neg (hlK row.2.1 row.2.2)) hbase
              · exact rational_input_height_mono (hhK row.2.1 row.2.2) hbase
        · rcases rows with a | rows
          · exact rational_input_height_mono hρ hbase
          · rcases rows with i | rows
            · apply rational_input_height_mono (rational_input_height_sub
                (rational_input_height_add hρ (rational_input_height_mul hM hr))
                (rational_score_input_height lo p hlo hp i))
              unfold rationalScoreInputHeight rationalIntervalInputHeight
              nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]
            · rcases rows with i | rows
              · exact hz
              · rcases rows with row | l
                · exact hz
                · apply rational_input_height_mono
                    (rational_envelope_grid_input_height M r η B (10*B+1) (l.val+1)
                      hM hr hη (rational_grid_row_endpoint_input_bound hM hr hη l))
                  unfold rationalEnvelopeInputHeight rationalGridNodeInputHeight rationalIntervalInputHeight
                  nlinarith [Nat.zero_le (k*B), Nat.zero_le (m*B)]

theorem rational_interval_system_input_height {k m B : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ)
    (hlK : ∀ a b, RationalInputHeight (loK a b) B)
    (hhK : ∀ a b, RationalInputHeight (hiK a b) B)
    (hlo : ∀ i a, RationalInputHeight (lo i a) B)
    (hhi : ∀ i a, RationalInputHeight (hi i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B) :
    (∀ row u, RationalInputHeight ((rationalIntervalSystem loK hiK lo hi p M r ρ η).coefficient row u)
      (rationalIntervalInputHeight k m B)) ∧
      ∀ row, RationalInputHeight ((rationalIntervalSystem loK hiK lo hi p M r ρ η).rightSide row)
        (rationalIntervalInputHeight k m B) :=
  ⟨rational_interval_coefficient_input_height lo hi p M r ρ η hlo hhi hp hM hr hρ hη,
    rational_interval_right_side_input_height loK hiK lo p M r ρ η hlK hhK hlo hp hM hr hρ hη⟩

theorem rational_interval_system_indexed_encoding_bits {k m B : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ)
    (hlK : ∀ a b, RationalInputHeight (loK a b) B)
    (hhK : ∀ a b, RationalInputHeight (hiK a b) B)
    (hlo : ∀ i a, RationalInputHeight (lo i a) B)
    (hhi : ∀ i a, RationalInputHeight (hi i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B) :
    let H := rationalGridSize M r η
    let rows := rationalIntervalRowCount k m H
    let vars := rationalIntervalVariableCount k m H
    rationalIndexedLinearSystemEncodingBits (rationalIntervalSystem loK hiK lo hi p M r ρ η) ≤
      rows*(vars+1)*(2*rationalIntervalInputHeight k m B+rows+vars+6) := by
  obtain ⟨hc, hs⟩ := rational_interval_system_input_height loK hiK lo hi p M r ρ η hlK hhK hlo hhi hp hM hr hρ hη
  have hh := rational_indexed_system_polynomial_encoding_bits_of_entry_bound
    (rationalIntervalSystem loK hiK lo hi p M r ρ η) hc hs
  simpa only [rational_interval_rows_exact_count, rationalIntervalVariableCount] using hh

end SparseCompletion
