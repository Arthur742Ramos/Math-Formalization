module

public import RegularPairs
public import RegularSelection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition

open Finset Finpartition SzemerediRegularity
open scoped Classical

/-- Extract a prescribed number of mutually regular parts of a uniform partition. -/
private theorem regular_parts {V : Type} [Fintype V] (G : SimpleGraph V)
    (P : Finpartition (univ : Finset V)) (e : ℝ) (k : ℕ)
    (he : 0 ≤ e) (htiny : e * (32*((k:ℝ)+1)) ≤ 1)
    (many : 32*(k+1) ≤ P.parts.card) (uniform : P.IsUniform G e) :
    ∃ T ⊆ P.parts, T.card = k ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → G.IsUniform e A B := by
  classical
  let S := P.parts
  let F := P.nonUniforms G e
  let bad := fun A B : Finset V => A = B ∨ ¬G.IsUniform e A B
  let (A B : Finset V) : Decidable (bad A B) := Classical.propDecidable _
  have count : (∑ A ∈ S, ((S.filter (bad A)).card : ℝ)) ≤ S.card + (F.card : ℝ) := by
    let B := (S ×ˢ S).filter fun ab => bad ab.1 ab.2
    have eqn : (∑ A ∈ S, ((S.filter (bad A)).card : ℝ)) = B.card := by
      have aux (A : Finset V) : ((S.filter (bad A)).card : ℝ) =
          ∑ C ∈ S, if bad A C then (1:ℝ) else 0 := by rw [← sum_filter]; simp
      simp_rw [aux]
      rw [← sum_product']
      rw [← sum_filter]; simp [B]
    have sub : B ⊆ S.diag ∪ F := by
      rintro ⟨A,C⟩ hab
      obtain ⟨hh,hbad⟩ := mem_filter.mp hab
      obtain ⟨ha,hc⟩ := mem_product.mp hh
      change A = C ∨ ¬G.IsUniform e A C at hbad
      rcases hbad with h | h
      · subst C; exact mem_union_left _ (by simp [ha])
      · by_cases hh : A = C
        · subst C; exact mem_union_left _ (by simp [ha])
        · exact mem_union_right _ ((P.mk_mem_nonUniforms G).mpr ⟨ha,hc,hh,h⟩)
    rw [eqn]
    exact_mod_cast (card_le_card sub).trans ((card_union_le ..).trans_eq (by rw [diag_card]))
  let m := (S.card : ℝ)
  have mpos : 0 < m := by dsimp [m,S]; exact_mod_cast (show 0 < P.parts.card by omega)
  have hmany : 32*((k:ℝ)+1) ≤ m := by dsimp [m,S]; exact_mod_cast many
  have smallF : (F.card : ℝ) ≤ m^2 * e := by
    apply uniform.trans
    apply mul_le_mul_of_nonneg_right _ he
    change (((S.card*(S.card-1) : ℕ) : ℝ)) ≤ m^2
    rw [sq]
    dsimp [m]
    exact_mod_cast Nat.mul_le_mul_left S.card (Nat.sub_le S.card 1)
  have few : (∑ A ∈ S, ((S.filter (bad A)).card : ℝ)) * (8*((k:ℝ)+1)) ≤ m^2 := by
    have h : (F.card : ℝ) * (32*((k:ℝ)+1)) ≤ m^2 := by
      calc
        _ ≤ m^2 * e * (32*((k:ℝ)+1)) := mul_le_mul_of_nonneg_right smallF (by positivity)
        _ ≤ _ := by rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left htiny (sq_nonneg _)).trans_eq (mul_one _)
    have h' := mul_le_mul_of_nonneg_left hmany mpos.le
    have := mul_le_mul_of_nonneg_right count (by positivity : 0 ≤ 8*((k:ℝ)+1))
    change _ ≤ (m + F.card) * _ at this
    nlinarith
  obtain ⟨T,hT,hk,hh⟩ := select_avoiding_sparse S bad k (card_pos.mp (by
    dsimp [m] at mpos
    exact_mod_cast mpos)) (fun _ _ => Or.inl rfl) (fun A B h => by
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr fun hb => h hb.symm) few
  exact ⟨T,hT,hk,fun A ha B hb hne => by
    by_contra h; exact hh A ha B hb hne (Or.inr h)⟩

/-- Qualitative self-pair lemma of Conlon and Fox in normalized cut discrepancy form.
For accuracy 4/t the set occupies at least 1/D of all vertices. D and the required
host order depend only on t. -/
theorem large_self_pair (t : ℕ) (ht : 0 < t) :
    ∃ D N₀ : ℕ, 0 < D ∧ ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      N₀ ≤ Fintype.card V → ∃ (U : Finset V) (p : ℝ), U.Nonempty ∧
        Fintype.card V ≤ D * U.card ∧ 0 ≤ p ∧ p ≤ 1 ∧
        CutDiscrepancy G U p ((4/(t:ℝ)) * (U.card : ℝ)^2) := by
  classical
  obtain ⟨R,ram⟩ := palette_ramsey (univ : Finset (Fin (t+1))) t
  let l := 32*(R+1)
  let e := min (1/(t:ℝ)) (1/(32*((R:ℝ)+1)))
  have tp : 0 < (t:ℝ) := Nat.cast_pos.mpr ht
  have ep : 0 < e := lt_min (by positivity) (by positivity)
  have tiny : e * (32*((R:ℝ)+1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  let b := bound e l
  refine ⟨2*(b+1),l,by positivity,?_⟩
  intro V _ G hl
  obtain ⟨P,eqp,hlo,hhi,uniform⟩ := szemeredi_regularity G ep hl
  obtain ⟨T,hTP,hT,hreg⟩ := regular_parts G P e R ep.le tiny hlo uniform
  let density := fun A B : Finset V => (G.edgeDensity A B : ℝ)
  have nonneg (A B : Finset V) : 0 ≤ density A B := by dsimp [density]; exact_mod_cast G.edgeDensity_nonneg A B
  have unit (A B : Finset V) : density A B ≤ 1 := by dsimp [density]; exact_mod_cast G.edgeDensity_le_one A B
  let col (A B : Finset V) : Fin (t+1) := ⟨⌊density A B * t⌋₊, by
    have := Nat.floor_le (mul_nonneg (nonneg A B) tp.le)
    have le : density A B*t ≤ (t:ℝ) := (mul_le_mul_of_nonneg_right (unit A B) tp.le).trans_eq (one_mul _)
    have h : ⌊density A B*t⌋₊ ≤ t := by exact_mod_cast this.trans le
    omega⟩
  have symm (A B : Finset V) : col A B = col B A := by
    apply Fin.ext
    simp only [col,density,G.edgeDensity_comm A B]
  obtain ⟨Q,k,hQT,hQ,hcol⟩ := ram T col hT.ge symm (by simp)
  let p := (k.val:ℝ)/t
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp' : p ≤ 1 := (div_le_iff₀ tp).mpr (by rw [one_mul]; exact_mod_cast (show k.val ≤ t by omega))
  have close (A) (ha : A ∈ Q) (B) (hb : B ∈ Q) (hn : A ≠ B) : |density A B - p| ≤ 1/t := by
    have hh := congrArg Fin.val (hcol A ha B hb hn)
    change ⌊density A B*t⌋₊ = k.val at hh
    have lo := Nat.floor_le (mul_nonneg (nonneg A B) tp.le)
    have hi := Nat.lt_floor_add_one (density A B*t)
    rw [hh] at lo hi
    rw [abs_le]
    constructor <;> dsimp [p] <;> field_simp <;> nlinarith
  have sub := hQT.trans hTP
  have dj := P.disjoint.subset (show (Q : Set (Finset V)) ⊆ P.parts from sub)
  let U := Q.biUnion id
  let a := Fintype.card V / P.parts.card
  have low (A) (hA : A ∈ P.parts) : a ≤ A.card := by simpa [a] using eqp.average_le_card_part hA
  have high (A) (hA : A ∈ P.parts) : A.card ≤ a+1 := by simpa [a] using eqp.card_part_le_average_add_one hA
  have sumU : U.card = ∑ A ∈ Q, A.card := card_biUnion dj
  have sumV : Fintype.card V = ∑ A ∈ P.parts, A.card := by simpa using P.sum_card_parts.symm
  have lb : t*a ≤ U.card := by
    rw [sumU, ← hQ, ← Nat.nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun A hA => low A (sub hA)
  have ub : Fintype.card V ≤ P.parts.card * (a+1) := by
    rw [sumV, ← Nat.nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun A hA => high A hA
  have partsLe : P.parts.card ≤ Fintype.card V := by
    rw [sumV, card_eq_sum_ones]
    exact sum_le_sum fun A hA => card_pos.mpr (nonempty_iff_ne_empty.mpr (P.ne_bot hA))
  have pp : 0 < P.parts.card := by dsimp [l] at hlo; omega
  have ap : 1 ≤ a := (Nat.le_div_iff_mul_le pp).mpr (by simpa using partsLe)
  have hU : U.Nonempty := card_pos.mp (lt_of_lt_of_le (Nat.mul_pos ht ap) lb)
  have disc := discrepancy_of_parts G Q dj p (1/(t:ℝ)) ((a+1:ℕ):ℝ) hp hp' (by positivity)
    (fun A hA => by exact_mod_cast high A (sub hA))
    (fun A ha B hb hn => ⟨(hreg A (hQT ha) B (hQT hb) hn).mono (min_le_left ..),close A ha B hb hn⟩)
  refine ⟨U,p,hU,?_,hp,hp',?_⟩
  · have au : a ≤ U.card := (Nat.le_mul_of_pos_left _ ht).trans lb
    apply ub.trans
    exact (Nat.mul_le_mul hhi (show a+1 ≤ 2*U.card by omega)).trans (by
      change b*(2*U.card) ≤ 2*(b+1)*U.card
      nlinarith)
  · have ratio : (((a+1:ℕ):ℝ) * (t:ℝ)) ≤ 2*U.card := by
      have hl' : (t:ℝ)*a ≤ U.card := by exact_mod_cast lb
      have ha' : (1:ℝ) ≤ a := by exact_mod_cast ap
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left ha' tp.le]
    intro X hX Y hY
    apply (disc X hX Y hY).trans
    change 2*(1/(t:ℝ))*(U.card : ℝ)^2 + _ ≤ _
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right ratio (Nat.cast_nonneg U.card)]

end InducedDegreeRepetition
