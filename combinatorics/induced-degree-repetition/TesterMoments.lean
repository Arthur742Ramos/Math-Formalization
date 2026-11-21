module

public import SampleFourth
public import MeanMarginals
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V I : Type*}

theorem fourth_on_pool (A : V → V → ℝ) (T : Finset V) :
    fourthMoment (fun i j : T => A i j) univ = fourthMoment A T := by
  have gram_eq (i j : T) : gram (fun i j : T => A i j) univ i j = gram A T i j := by
    exact (sum_subtype T (fun _ => Iff.rfl) (fun k => A k i*A k j)).symm
  unfold fourthMoment
  simp only [gram_eq]
  have inner (x : T) : ∑ y : T, gram A T x y^2 = ∑ y ∈ T, gram A T x y^2 :=
    (sum_subtype T (fun _ => Iff.rfl) (fun y => gram A T x y^2)).symm
  simp only [inner]
  exact (sum_subtype T (fun _ => Iff.rfl) (fun x => ∑ y ∈ T, gram A T x y^2)).symm

theorem tester_moment [Fintype I] [DecidableEq I] (G : SimpleGraph V) (B T : Finset V) (p ε : ℝ)
    (sub : T ⊆ B) (hp : 0 ≤ p) (h1 : p ≤ 1) (op : SpectralBound G B p ε) (tn : T.Nonempty)
    (size : (B.card:ℝ) ≤ 3*T.card) :
    mean (fun ys : I → T => fourthMoment (fun i j => centered G p (ys i) (ys j)) univ) ≤
      (Fintype.card I:ℝ)^4*(9*ε^2) + 6*(Fintype.card I:ℝ)^3 := by
  classical
  let : Nonempty T := tn.to_subtype
  have bound := sampled_fourth (I:=I) (fun x y : T => centered G p x y) (fun x y => by
    have a := centered_sq_le_one G p hp h1 x y
    exact (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp (by simpa using a))
  rw [fourth_on_pool,Fintype.card_coe] at bound
  apply bound.trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_iff₀ (by exact pow_pos (by exact_mod_cast card_pos.mpr tn : (0:ℝ)<T.card) 4)]
  have h := host_fourth G p ε B T sub hp h1 op
  have sz := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr size
  have prod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sz (sq_nonneg ε)) (sq_nonneg (T.card:ℝ))
  nlinarith only [h,prod]

end InducedDegreeRepetition.Sampling
