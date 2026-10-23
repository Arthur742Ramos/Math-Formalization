/- AI-assisted formalization under the repository Apache-2.0 license.
Explicit rational coefficients for the paper's fixed-tolerance cone rows.
Separate source draft; verification status is recorded externally.
-/
module
public import RationalLinearForms
public import ConicCompletion
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- A three-dimensional rotated-cone row with rational affine coefficients.
There is no feasibility or correctness field. -/
structure RationalConeRow (n : ℕ) where
  u : Fin n → ℚ
  v : Fin n → ℚ
  w : Fin n → ℚ
  u0 : ℚ
  v0 : ℚ
  w0 : ℚ

def RationalConeRow.RealSatisfied {n : ℕ} (c : RationalConeRow n)
    (x : Fin n → ℝ) : Prop :=
  rotatedLorentz ((c.u0 : ℝ)+rationalFormRealEval c.u x)
    ((c.v0 : ℝ)+rationalFormRealEval c.v x)
    ((c.w0 : ℝ)+rationalFormRealEval c.w x)

def RationalConeRow.RationalSatisfied {n : ℕ} (c : RationalConeRow n)
    (x : Fin n → ℚ) : Prop :=
  0 ≤ c.u0+rationalFormEval c.u x ∧
    0 ≤ c.v0+rationalFormEval c.v x ∧
    (c.w0+rationalFormEval c.w x)^2 ≤
      2*(c.u0+rationalFormEval c.u x)*(c.v0+rationalFormEval c.v x)

instance rationalConeRowSatisfiesDecidable {n : ℕ} (c : RationalConeRow n)
    (x : Fin n → ℚ) : Decidable (c.RationalSatisfied x) := by
  unfold RationalConeRow.RationalSatisfied
  infer_instance

theorem rational_cone_row_cast_iff {n : ℕ} (c : RationalConeRow n)
    (x : Fin n → ℚ) :
    c.RealSatisfied (fun i => (x i : ℝ)) ↔ c.RationalSatisfied x := by
  have he (a : Fin n → ℚ) :
      rationalFormRealEval a (fun i => (x i : ℝ)) = (rationalFormEval a x : ℝ) := by
    simp only [rationalFormRealEval, rationalFormEval, Rat.cast_sum, Rat.cast_mul]
  simp only [RationalConeRow.RealSatisfied, he, rotatedLorentz,
    RationalConeRow.RationalSatisfied]
  norm_cast

/-- Encodes M Q(x)^2 - M r Q(x) + a(x) ≤ 0 using only rational
coefficients. Its correctness theorem requires M>0, as in the paper. -/
def rationalQuadraticConeRow {n : ℕ} (Q a : Fin n → ℚ) (M r : ℚ) :
    RationalConeRow n where
  u := rationalFormAdd (rationalFormScale r Q) (rationalFormScale (-1/M) a)
  v := fun _ => 0
  w := Q
  u0 := 0
  v0 := 1/2
  w0 := 0

theorem rational_quadratic_cone_row_iff {n : ℕ} (Q a : Fin n → ℚ)
    (M r : ℚ) (hM : 0 < M) (x : Fin n → ℝ) :
    (rationalQuadraticConeRow Q a M r).RealSatisfied x ↔
      (M : ℝ)*(rationalFormRealEval Q x)^2-
        (M : ℝ)*(r : ℝ)*rationalFormRealEval Q x+rationalFormRealEval a x ≤ 0 := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [quadratic_rotated_cone (M : ℝ) (r : ℝ)
    (rationalFormRealEval Q x) (rationalFormRealEval a x) hMR]
  have hu : rationalFormRealEval
      (rationalFormAdd (rationalFormScale r Q) (rationalFormScale (-1/M) a)) x =
      (r : ℝ)*rationalFormRealEval Q x-rationalFormRealEval a x/(M : ℝ) := by
    rw [rational_form_real_eval_add, rational_form_real_eval_scale,
      rational_form_real_eval_scale]
    push_cast
    ring
  have hz : rationalFormRealEval (fun _ : Fin n => (0 : ℚ)) x = 0 := by
    simp [rationalFormRealEval]
  dsimp only [RationalConeRow.RealSatisfied, rationalQuadraticConeRow]
  rw [hu, hz]
  norm_num

def rationalPrefixMassForm (m l : ℕ) : Fin m → ℚ :=
  fun i => if i.val < l then 1 else 0

def rationalPrefixScoreForm {m : ℕ} (t : Fin m → ℚ) (ε : ℚ) (l : ℕ) :
    Fin m → ℚ := fun i => if i.val < l then t i-ε else 0

def rationalPrefixConeRows {m : ℕ} (t : Fin m → ℚ) (M r ε : ℚ) :
    Fin m → RationalConeRow m := fun l =>
  rationalQuadraticConeRow (rationalPrefixMassForm m (l.val+1))
    (rationalPrefixScoreForm t ε (l.val+1)) M r

theorem rational_prefix_mass_form_eval {m : ℕ} (q : Fin m → ℝ) (l : ℕ) :
    rationalFormRealEval (rationalPrefixMassForm m l) q = mass (scorePrefix m l) q := by
  unfold rationalFormRealEval rationalPrefixMassForm mass scorePrefix
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < l <;> simp [hi]

theorem rational_prefix_score_form_eval {m : ℕ} (t : Fin m → ℚ) (ε : ℚ)
    (q : Fin m → ℝ) (l : ℕ) :
    rationalFormRealEval (rationalPrefixScoreForm t ε l) q =
      ∑ i ∈ scorePrefix m l, q i*((t i : ℝ)-(ε : ℝ)) := by
  unfold rationalFormRealEval rationalPrefixScoreForm scorePrefix
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < l <;> simp [hi, mul_comm]

theorem rational_prefix_cone_row_iff {m : ℕ} (t : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 < M) (q : Fin m → ℝ) (l : Fin m) :
    (rationalPrefixConeRows t M r ε l).RealSatisfied q ↔
      (M : ℝ)*(mass (scorePrefix m (l.val+1)) q)^2-
        (M : ℝ)*(r : ℝ)*mass (scorePrefix m (l.val+1)) q+
        (∑ i ∈ scorePrefix m (l.val+1), q i*((t i : ℝ)-(ε : ℝ))) ≤ 0 := by
  unfold rationalPrefixConeRows
  rw [rational_quadratic_cone_row_iff _ _ M r hM q,
    rational_prefix_mass_form_eval, rational_prefix_score_form_eval]

/-- There are exactly m actual cone rows; the omitted empty prefix is 0≤0.
This is an exact coefficient representation, not an exact-conic solver. -/
theorem rational_prefix_cone_rows_iff {m : ℕ} (t : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 < M) (q : Fin m → ℝ) :
    (∀ l, (rationalPrefixConeRows t M r ε l).RealSatisfied q) ↔
      ∀ l : ℕ, l ≤ m →
        (M : ℝ)*(mass (scorePrefix m l) q)^2-
          (M : ℝ)*(r : ℝ)*mass (scorePrefix m l) q+
          (∑ i ∈ scorePrefix m l, q i*((t i : ℝ)-(ε : ℝ))) ≤ 0 := by
  constructor
  · intro h l hl
    cases l with
    | zero => simp [scorePrefix, mass]
    | succ l => exact (rational_prefix_cone_row_iff t M r ε hM q ⟨l, by omega⟩).mp (h _)
  · intro h l
    exact (rational_prefix_cone_row_iff t M r ε hM q l).mpr (h _ (by omega))

theorem rational_prefix_cone_completion_iff {m : ℕ} (t : Fin m → ℚ)
    (M r ε : ℚ) (hM : 0 < M) (q : Fin m → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (ht : Antitone (fun i => (t i : ℝ))) :
    (∃ B, IsSkew B ∧ (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
      ∀ i, (t i : ℝ)+response B q i ≤ (ε : ℝ)) ↔
    (∀ i, (t i : ℝ) ≤ (ε : ℝ)+(M : ℝ)*(r : ℝ)) ∧
      ∀ l, (rationalPrefixConeRows t M r ε l).RealSatisfied q := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [weighted_completion_prefix_quadratic_iff q (fun i => (t i : ℝ))
    (M : ℝ) (r : ℝ) (ε : ℝ) hMR hq hr ht,
    rational_prefix_cone_rows_iff t M r ε hM q]

/-- Dense rational scalar coordinates, including all three affine constants.
No byte serializer, coefficient-height, or runtime claim is implicit. -/
def rationalConeSystemCoordinateCount (rows n : ℕ) : ℕ := rows*(3*n+3)

theorem rational_prefix_cone_coordinate_count (m : ℕ) :
    rationalConeSystemCoordinateCount (Fintype.card (Fin m)) m = 3*m*(m+1) := by
  simp only [rationalConeSystemCoordinateCount, Fintype.card_fin]
  ring

end SparseCompletion
