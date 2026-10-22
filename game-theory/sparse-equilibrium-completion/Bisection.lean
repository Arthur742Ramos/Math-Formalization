/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GameModel
@[expose] public section
namespace SparseCompletion
namespace RationalBisection

/-- Conditional rational bisection: the caller supplies genuine decidable
    feasibility. This definition does not implement an LP feasibility oracle. -/
def run (P : ℚ → Prop) [DecidablePred P] : ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, lo, hi => (lo,hi)
  | n+1, lo, hi =>
    let z := run P n lo hi
    let mid := (z.1+z.2)/((2 : ℕ) : ℚ)
    if P mid then (z.1,mid) else (mid,z.2)

/-- A feasible upper endpoint and infeasible lower endpoint are retained. -/
theorem endpoint_invariant (P : ℚ → Prop) [DecidablePred P]
    (lo hi : ℚ) (hn : ¬P lo) (hy : P hi) (n : ℕ) :
    ¬P (run P n lo hi).1 ∧ P (run P n lo hi).2 := by
  induction n with
  | zero => exact ⟨hn,hy⟩
  | succ n ih =>
    simp only [run]
    split_ifs with hm
    · exact ⟨ih.1,hm⟩
    · exact ⟨hm,ih.2⟩

theorem nested_bracket (P : ℚ → Prop) [DecidablePred P]
    (lo hi : ℚ) (hlh : lo ≤ hi) (n : ℕ) :
    lo ≤ (run P n lo hi).1 ∧ (run P n lo hi).1 ≤ (run P n lo hi).2 ∧
      (run P n lo hi).2 ≤ hi := by
  induction n with
  | zero => exact ⟨le_refl _,hlh,le_refl _⟩
  | succ n ih =>
    simp only [run]
    split_ifs <;> dsimp only
    · exact ⟨ih.1,by linarith [ih.2.1],by linarith [ih.2.1,ih.2.2]⟩
    · exact ⟨by linarith [ih.1,ih.2.1],by linarith [ih.2.1],ih.2.2⟩

theorem width_exact (P : ℚ → Prop) [DecidablePred P]
    (lo hi : ℚ) (n : ℕ) :
    (run P n lo hi).2-(run P n lo hi).1=(hi-lo)/((2 : ℕ) : ℚ)^n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hh : ((run P n lo hi).2-(run P n lo hi).1)/((2 : ℕ) : ℚ)=
        (hi-lo)/((2 : ℕ) : ℚ)^(n+1) := by
      rw [ih,pow_succ,div_div]
    simp only [run]
    split_ifs <;> dsimp only <;> linarith

/-- Monotonicity turns an infeasible endpoint into an excluded lower region. -/
theorem excludes_below (P : ℚ → Prop) [DecidablePred P] (hmono : Monotone P)
    (lo hi : ℚ) (hn : ¬P lo) (hy : P hi) (n : ℕ) (ρ : ℚ)
    (hρ : ρ ≤ (run P n lo hi).1) : ¬P ρ := by
  intro hp
  exact (endpoint_invariant P lo hi hn hy n).1 (hmono hρ hp)

/-- Finite iteration certificate: once the explicit halved width is at most ζ,
    the returned upper endpoint is feasible and the bracket has width at most ζ. -/
theorem certified_bracket (P : ℚ → Prop) [DecidablePred P]
    (lo hi ζ : ℚ) (hlh : lo ≤ hi) (hn : ¬P lo) (hy : P hi)
    (n : ℕ) (hwidth : (hi-lo)/((2 : ℕ) : ℚ)^n ≤ ζ) :
    let z := run P n lo hi
    lo ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ hi ∧ ¬P z.1 ∧ P z.2 ∧ z.2-z.1 ≤ ζ := by
  obtain ⟨hlo,horder,hhi⟩ := nested_bracket P lo hi hlh n
  obtain ⟨hl,hu⟩ := endpoint_invariant P lo hi hn hy n
  exact ⟨hlo,horder,hhi,hl,hu,(width_exact P lo hi n).symm ▸ hwidth⟩

theorem nat_le_two_pow (n : ℕ) : (n : ℚ) ≤ ((2 : ℕ) : ℚ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    have hp : (1 : ℚ) ≤ ((2 : ℕ) : ℚ)^n := one_le_pow₀ (by norm_num)
    norm_num only [Nat.cast_ofNat] at *
    linarith

/-- Positive requested width is reached after a finite number of iterations.
    This is an existence theorem, not an operation-count or bit-cost claim. -/
theorem exists_finite_width (P : ℚ → Prop) [DecidablePred P]
    (lo hi ζ : ℚ) (hζ : 0 < ζ) :
    ∃ n : ℕ, (run P n lo hi).2-(run P n lo hi).1 ≤ ζ := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((hi-lo)/ζ)
  refine ⟨n,?_⟩
  rw [width_exact]
  have hh : (hi-lo)/ζ < ((2 : ℕ) : ℚ)^n := lt_of_lt_of_le hn (nat_le_two_pow n)
  have hb := (div_lt_iff₀ hζ).mp hh
  norm_num only [Nat.cast_ofNat] at *
  exact (div_le_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) n)).mpr (by linarith)

/-- The lower endpoint may already be feasible; return it immediately in that
    case. This permits the paper's initial nonnegative bracket [0,M]. -/
def search (P : ℚ → Prop) [DecidablePred P] (n : ℕ) (lo hi : ℚ) : ℚ × ℚ :=
  if P lo then (lo,lo) else run P n lo hi

theorem search_spec (P : ℚ → Prop) [DecidablePred P] (n : ℕ)
    (lo hi : ℚ) (hlh : lo ≤ hi) (hy : P hi) :
    let z := search P n lo hi
    lo ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ hi ∧ P z.2 ∧
      (z.1=lo ∨ ¬P z.1) ∧ z.2-z.1 ≤ (hi-lo)/((2 : ℕ) : ℚ)^n := by
  unfold search
  split_ifs with hn
  · refine ⟨le_refl _,le_refl _,hlh,hn,Or.inl rfl,?_⟩
    dsimp only
    exact sub_self lo ▸ div_nonneg (sub_nonneg.mpr hlh) (le_of_lt (pow_pos (by norm_num) n))
  · obtain ⟨hl,ho,hu⟩ := nested_bracket P lo hi hlh n
    obtain ⟨hno,hyes⟩ := endpoint_invariant P lo hi hn hy n
    exact ⟨hl,ho,hu,hyes,Or.inr hno,(width_exact P lo hi n).le⟩

/-- Conditional extraction of a feasible upper-end witness and a real value
    interval. The caller supplies feasibility soundness and lower exclusion;
    neither a rational LP oracle nor a reconstruction algorithm is invented. -/
theorem value_certificate {β : Type*} (P : ℚ → Prop) [DecidablePred P]
    (Witness : ℚ → β → Prop) (V η : ℝ) (M ζ : ℚ) (n : ℕ)
    (hM : 0 ≤ M) (hupper : P M) (hV : 0 ≤ V)
    (hlower : ∀ ρ : ℚ, ¬P ρ → (ρ : ℝ) ≤ V)
    (hsound : ∀ ρ : ℚ, P ρ → ∃ w, Witness ρ w ∧ V ≤ (ρ : ℝ)+η)
    (hwidth : M/((2 : ℕ) : ℚ)^n ≤ ζ) :
    let z := search P n 0 M
    (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+η ∧
      (z.2 : ℝ)+η-(z.1 : ℝ) ≤ η+(ζ : ℝ) ∧ ∃ w, Witness z.2 w := by
  obtain ⟨_,_,_,hu,hl,hw⟩ := search_spec P n 0 M hM hupper
  obtain ⟨w,hW,hv⟩ := hsound _ hu
  have hlow : ((search P n 0 M).1 : ℝ) ≤ V := by
    rcases hl with he | hn
    · rw [he]; exact_mod_cast hV
    · exact hlower _ hn
  have hh : (search P n 0 M).2-(search P n 0 M).1 ≤ ζ := by
    exact le_trans hw (by simpa only [sub_zero] using hwidth)
  have hhR : ((search P n 0 M).2 : ℝ)-((search P n 0 M).1 : ℝ) ≤ (ζ : ℝ) := by
    exact_mod_cast hh
  exact ⟨hlow,hv,by linarith,w,hW⟩

end RationalBisection
end SparseCompletion
