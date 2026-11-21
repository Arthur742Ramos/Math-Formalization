module

public import RemainingStatements
public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V : Type*}

@[expose] noncomputable def centered (G : SimpleGraph V) (p : ℝ) (x y : V) : ℝ :=
  (if G.Adj x y then 1 else 0)-p

theorem centered_symm (G : SimpleGraph V) (p : ℝ) (x y : V) :
    centered G p x y = centered G p y x := by simp only [centered,G.adj_comm x y]

theorem centered_sq_le_one (G : SimpleGraph V) (p : ℝ) (lo : 0 ≤ p) (hi : p ≤ 1) (x y : V) :
    centered G p x y ^2 ≤ 1 := by
  unfold centered
  split <;> nlinarith [mul_nonneg lo (sub_nonneg.mpr hi)]

@[expose] noncomputable def gram (A : V → V → ℝ) (T : Finset V) (x y : V) :=
  ∑ k ∈ T, A k x * A k y

@[expose] noncomputable def fourthMoment (A : V → V → ℝ) (T : Finset V) :=
  ∑ x ∈ T, ∑ y ∈ T, (gram A T x y)^2

/-- The fourth moment controls every retained subset at once. -/
theorem adaptive_subset (A : V → V → ℝ) (T E : Finset V) (sub : E ⊆ T) :
    (∑ x ∈ T, (∑ y ∈ E, A x y)^2)^2 ≤ (E.card:ℝ)^2*fourthMoment A T := by
  classical
  have identity : (∑ k ∈ T, (∑ x ∈ E, A k x)^2) =
      ∑ z ∈ E ×ˢ E, gram A T z.1 z.2 := by
    rw [sum_product]
    simp only [gram,pow_two,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [sum_comm]
    simp only [mul_comm]
  rw [identity]
  have cs := sq_sum_le_card_mul_sum_sq (s := E ×ˢ E) (f := fun z => gram A T z.1 z.2)
  rw [card_product,Nat.cast_mul,← pow_two] at cs
  apply cs.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  unfold fourthMoment
  rw [← sum_product']
  exact sum_le_sum_of_subset_of_nonneg (product_subset_product sub sub) fun _ _ _ => sq_nonneg _

/-- Compressing the host bound to the tester population bounds its fourth moment. -/
theorem host_fourth (G : SimpleGraph V) (p ε : ℝ) (B T : Finset V) (sub : T ⊆ B)
    (hp : 0 ≤ p) (h1 : p ≤ 1) (op : SpectralBound G B p ε) :
    fourthMoment (centered G p) T ≤ (ε*B.card)^2*(T.card:ℝ)^2 := by
  classical
  let A := centered G p
  have one (x : V) : ∑ y ∈ T, (gram A T x y)^2 ≤ (ε*B.card)^2*T.card := by
    let v (k : V) := if k ∈ T then A k x else 0
    have eq (y : V) : ∑ k ∈ B, (centered G p y k)*v k = gram A T x y := by
      simp only [v,mul_ite,mul_zero,←sum_filter]
      rw [show B.filter (· ∈ T) = T by ext k; simp; exact fun h => sub h]
      apply sum_congr rfl
      intro k _
      dsimp [A]
      rw [centered_symm G p y k,mul_comm]
    have norm : ∑ k ∈ B, v k^2 ≤ T.card := by
      simp only [v,ite_pow,zero_pow (by decide : 2 ≠ 0),←sum_filter]
      rw [show B.filter (· ∈ T) = T by ext k; simp; exact fun h => sub h]
      exact (sum_le_sum (fun k _ => centered_sq_le_one G p hp h1 k x)).trans_eq (by simp)
    have spec := op v
    change (∑ y ∈ B, (∑ k ∈ B, (centered G p y k)*v k)^2) ≤ _ at spec
    simp only [eq] at spec
    exact (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => sq_nonneg _)).trans
      (spec.trans (mul_le_mul_of_nonneg_left norm (sq_nonneg _)))
  have total := sum_le_sum (s:=T) fun x _ => one x
  unfold fourthMoment
  apply total.trans_eq
  simp
  ring

end InducedDegreeRepetition.Sampling
