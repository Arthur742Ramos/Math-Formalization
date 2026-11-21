module

public import RemainingStatements
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition

open Finset OpenProblems
open scoped Classical

variable {V : Type*}

/-- Centered adjacency kernel, including the diagonal. -/
@[expose] noncomputable def centered (G : SimpleGraph V) (p : ℝ) (x y : V) : ℝ :=
  (if G.Adj x y then 1 else 0) - p

/-- Unnormalized discrepancy on all rectangles. The two test sets can overlap. -/
@[expose] def CutDiscrepancy (G : SimpleGraph V) (B : Finset V) (p bound : ℝ) : Prop :=
  ∀ X ⊆ B, ∀ Y ⊆ B, |∑ x ∈ X, ∑ y ∈ Y, centered G p x y| ≤ bound

private theorem centered_symm (G : SimpleGraph V) (p : ℝ) (x y : V) :
    centered G p x y = centered G p y x := by simp only [centered, G.adj_comm x y]

/-- The absolute row sum of a finite vector is bounded by its positive and negative cuts. -/
private theorem sum_abs_of_subsums (B : Finset V) (f : V → ℝ) (d : ℝ)
    (h : ∀ S ⊆ B, |∑ x ∈ S, f x| ≤ d) : ∑ x ∈ B, |f x| ≤ 2*d := by
  classical
  let P := B.filter fun x => 0 ≤ f x
  let N := B.filter fun x => ¬ 0 ≤ f x
  have hp := (abs_le.mp (h P (filter_subset ..))).2
  have hn := (abs_le.mp (h N (filter_subset ..))).1
  have spl := sum_filter_add_sum_filter_not B (fun x => 0 ≤ f x) (fun x => |f x|)
  have ap : ∑ x ∈ P, |f x| = ∑ x ∈ P, f x :=
    sum_congr rfl fun x hx => abs_of_nonneg (mem_filter.mp (show x ∈ P from hx)).2
  have an : ∑ x ∈ N, |f x| = -(∑ x ∈ N, f x) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x hx => abs_of_neg (lt_of_not_ge (mem_filter.mp (show x ∈ N from hx)).2)
  change (∑ x ∈ P, |f x|) + (∑ x ∈ N, |f x|) = _ at spl
  linarith

/-- A self-pair cut discrepancy bound controls the squared Euclidean operator norm.
For centered adjacency the row of the squared kernel is a difference of two
rectangle sums, one on the neighborhood of the row and one on the whole set. -/
theorem cut_to_spectral (G : SimpleGraph V) (B : Finset V) (p d ε : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hd : CutDiscrepancy G B p d)
    (hε : 4*d ≤ (ε * B.card)^2) : SpectralBound G B p ε := by
  classical
  let C := centered G p
  let T := fun x z => ∑ y ∈ B, C x y * C y z
  have cs (x y : V) : C x y = C y x := centered_symm G p x y
  have ts (x z : V) : T x z = T z x := by
    apply sum_congr rfl
    intro y _
    rw [cs x y,cs y z,mul_comm]
  have row (x : V) : ∑ z ∈ B, |T x z| ≤ 4*d := by
    apply (sum_abs_of_subsums B (T x) (2*d) ?_).trans (by linarith)
    intro Z hZ
    let N := B.filter (G.Adj x)
    let f := fun y => ∑ z ∈ Z, C y z
    have e : ∑ z ∈ Z, T x z = (∑ y ∈ N, f y) - p * ∑ y ∈ B, f y := by
      simp only [T]
      rw [sum_comm]
      simp only [← mul_sum]
      change ∑ y ∈ B, ((if G.Adj x y then (1:ℝ) else 0) - p) * f y = _
      simp only [sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite,
        sum_const_zero, add_zero, ← mul_sum, N]
    have n := hd N (filter_subset ..) Z hZ
    have b := hd B (Subset.rfl) Z hZ
    rw [e]
    calc
      _ ≤ |∑ y ∈ N, f y| + |p * ∑ y ∈ B, f y| := abs_sub ..
      _ ≤ d + d := by
        rw [abs_mul, abs_of_nonneg hp]
        exact add_le_add n ((mul_le_mul_of_nonneg_right hp' (abs_nonneg _)).trans (by simpa using b))
      _ = 2*d := by ring
  intro v
  change (∑ x ∈ B, (∑ y ∈ B, C x y * v y)^2) ≤ _
  have expand : (∑ x ∈ B, (∑ y ∈ B, C x y * v y)^2) =
      ∑ y ∈ B, ∑ z ∈ B, T y z * (v y * v z) := by
    simp only [pow_two, sum_mul, mul_sum, T]
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro x _
    rw [cs y x]
    ring
  have point (x z : V) : 2*(T x z * (v x * v z)) ≤ |T x z| *(v x^2 + v z^2) := by
    have h₁ := sq_nonneg (v x - v z)
    have h₂ := sq_nonneg (v x + v z)
    rcases le_total 0 (T x z) with ht | ht
    · rw [abs_of_nonneg ht]
      nlinarith [mul_nonneg ht h₁]
    · rw [abs_of_nonpos ht]
      nlinarith [mul_nonneg (neg_nonneg.mpr ht) h₂]
  have weight : (∑ x ∈ B, ∑ z ∈ B, |T x z| * v x^2) ≤ (4*d)*∑ x ∈ B, v x^2 := by
    simp only [← sum_mul, mul_sum]
    exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (row x) (sq_nonneg _)
  have transpose : (∑ x ∈ B, ∑ z ∈ B, |T x z| * v z^2) = ∑ x ∈ B, ∑ z ∈ B, |T x z| * v x^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    exact sum_congr rfl fun z _ => by rw [ts z x]
  have bound := sum_le_sum (s := B) fun x _ => sum_le_sum (s := B) fun z _ => point x z
  simp only [← mul_sum, mul_add, sum_add_distrib, transpose] at bound
  rw [expand]
  exact (show _ ≤ (4*d) * ∑ x ∈ B, v x^2 by linarith).trans
    (mul_le_mul_of_nonneg_right hε (sum_nonneg fun _ _ => sq_nonneg _))

private theorem sum_centered (G : SimpleGraph V) (p : ℝ) (S : Finset V) (x : V) :
    (∑ y ∈ S, centered G p x y) = (degreeOn G S x : ℝ) - p*S.card := by
  classical
  simp [centered, degreeOn, sum_sub_distrib, mul_comm]

private theorem centered_le_one (G : SimpleGraph V) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (x y : V) : |centered G p x y| ≤ 1 := by
  apply abs_le.mpr
  by_cases h : G.Adj x y <;> simp only [centered, h, ite_true, ite_false] <;> constructor <;> linarith

/-- Pruning a self-pair of absolute discrepancy a²|U|² yields uniform degrees and
spectral error on a set of at least half its vertices. Both conclusions use the
same density p as the original pair. -/
theorem prune_self_pair (G : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    (p a : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (ha : 0 < a) (ha' : a ≤ 1/4)
    (hcut : CutDiscrepancy G U p (a^2 * (U.card : ℝ)^2)) :
    ∃ B ⊆ U, (U.card : ℝ) ≤ 2 * B.card ∧
      (∀ x ∈ B, |(degreeOn G B x : ℝ) - p * B.card| ≤ 6*a*B.card) ∧
      SpectralBound G B p (4*a) := by
  classical
  let M := (U.card : ℝ)
  let f := fun x => ∑ y ∈ U, centered G p x y
  let B := U.filter fun x => |f x| ≤ a*M
  let E := U \ B
  have sub : B ⊆ U := filter_subset ..
  have subE : E ⊆ U := sdiff_subset
  have hM : 0 < M := by dsimp [M]; exact_mod_cast card_pos.mpr hU
  have hf : (∑ x ∈ U, |f x|) ≤ 2*(a^2*M^2) :=
    sum_abs_of_subsums U f _ (fun X hX => hcut X hX U Subset.rfl)
  have small : (E.card : ℝ) ≤ 2*a*M := by
    apply le_of_mul_le_mul_right (a := a*M) _ (by positivity)
    calc
      (E.card : ℝ) * (a*M) = ∑ _ ∈ E, a*M := by simp
      _ ≤ ∑ x ∈ E, |f x| := by
        apply sum_le_sum
        intro x hx
        have h := mem_sdiff.mp hx
        exact (lt_of_not_ge fun hn => h.2 (mem_filter.mpr ⟨h.1,hn⟩)).le
      _ ≤ ∑ x ∈ U, |f x| := sum_le_sum_of_subset_of_nonneg subE fun _ _ _ => abs_nonneg _
      _ ≤ 2*(a^2*M^2) := hf
      _ = _ := by ring
  have size : (E.card : ℝ) + B.card = M := by
    dsimp [E,M]
    exact_mod_cast (card_sdiff_add_card_eq_card sub)
  have half : M ≤ 2 * B.card := by nlinarith [mul_le_mul_of_nonneg_right ha' hM.le]
  refine ⟨B,sub,half,?_,?_⟩
  · intro x hx
    have good := (mem_filter.mp (show x ∈ B from hx)).2
    have split : (∑ y ∈ E, centered G p x y) + (∑ y ∈ B, centered G p x y) = f x :=
      sum_sdiff sub
    have drop : |∑ y ∈ E, centered G p x y| ≤ E.card := by
      calc
        _ ≤ ∑ y ∈ E, |centered G p x y| := abs_sum_le_sum_abs ..
        _ ≤ ∑ _ ∈ E, (1:ℝ) := sum_le_sum fun y _ => centered_le_one G p hp hp' x y
        _ = _ := by simp
    rw [← sum_centered, show (∑ y ∈ B, centered G p x y) =
      f x - ∑ y ∈ E, centered G p x y by linarith]
    exact (abs_sub ..).trans (by nlinarith [mul_le_mul_of_nonneg_left half ha.le])
  · apply cut_to_spectral G B p _ _ hp hp' (fun X hX Y hY => hcut X (hX.trans sub) Y (hY.trans sub))
    have h : 2*(a*M) ≤ 4*a*B.card := by nlinarith [mul_le_mul_of_nonneg_left half ha.le]
    have sq := mul_self_le_mul_self (show 0 ≤ 2*(a*M) by positivity) h
    dsimp [M] at *
    nlinarith

end InducedDegreeRepetition
