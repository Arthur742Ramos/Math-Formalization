module

public import UniformMean
public import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {I X : Type*}

theorem mean_smul [Fintype X] (a : ℝ) (f : X → ℝ) :
    mean (fun x => a*f x) = a*mean f := by simp only [mean,← mul_sum]; ring

theorem mean_sub [Fintype X] (f g : X → ℝ) :
    mean (fun x => f x-g x) = mean f-mean g := by simp only [mean,sum_sub_distrib,sub_div]

variable [Fintype I] [DecidableEq I] (P : I → Type*) [∀ i, Fintype (P i)] [∀ i, Nonempty (P i)]

theorem mean_coordinate (i : I) (f : P i → ℝ) :
    mean (fun x : ∀ i, P i => f (x i)) = mean f := by
  classical
  have eq := mean_equiv (Equiv.piSplitAt i P) (fun x => f (x i)) (fun z => f z.1) (fun _ => rfl)
  rw [eq,mean_prod (fun x (_ : ∀ j : {j // j ≠ i}, P j) => f x)]
  simp only [mean_const]

theorem mean_cross (i j : I) (ne : j ≠ i) (f : P i → ℝ) (g : P j → ℝ) :
    mean (fun x : ∀ i, P i => f (x i)*g (x j)) = mean f*mean g := by
  classical
  let O := {j : I // j ≠ i}
  let k : O := ⟨j,ne⟩
  let other := fun (x : ∀ t : O, P t) => g (x k)
  have h := mean_equiv (Equiv.piSplitAt i P) (fun x => f (x i)*g (x j))
    (fun p => f p.1*other p.2) (fun _ => rfl)
  rw [h,mean_prod (fun a b => f a*other b)]
  simp_rw [mean_smul]
  have eq := mean_coordinate (fun t : O => P t) k g
  change mean other = mean g at eq
  rw [eq]
  simp only [mean,← sum_mul]
  ring

theorem variance_bound (S : Finset I) (f : (i : I) → P i → ℝ) (L : ℝ)
    (bound : ∀ i ∈ S, ∀ x, 0 ≤ f i x ∧ f i x ≤ L) :
    mean (fun x : ∀ i, P i => (∑ i ∈ S, (f i (x i)-mean (f i)))^2) ≤ S.card*L^2 := by
  classical
  let z (i : I) (x : P i) := f i x - mean (f i)
  have centered (i) : mean (z i) = 0 := by simp [z,mean_sub,mean_const]
  have per (i) (hi : i ∈ S) (j) : mean (fun x : ∀ i, P i => z i (x i)*z j (x j)) ≤
      (if i=j then L^2 else 0) := by
    by_cases eq : i=j
    · subst j
      rw [ite_eq_left rfl,mean_coordinate P i (fun x => z i x*z i x)]
      have lo : 0 ≤ mean (f i) := (mean_const (X:=P i) 0) ▸ mean_le _ _ (fun x => (bound i hi x).1)
      have up : mean (f i) ≤ L := (mean_le _ _ (fun x => (bound i hi x).2)).trans_eq (mean_const _)
      rw [← mean_const (X:=P i) (L^2)]
      apply mean_le
      intro x
      have a := bound i hi x
      dsimp [z]
      nlinarith [mul_nonneg (show 0 ≤ L-(f i x-mean (f i)) by linarith) (show 0 ≤ L+(f i x-mean (f i)) by linarith)]
    · rw [mean_cross P i j (Ne.symm eq),centered,zero_mul,ite_eq_right eq]
  change mean (fun x : ∀ i, P i => (∑ i ∈ S, z i (x i))^2) ≤ _
  simp_rw [pow_two,sum_mul,mul_sum,mean_sum]
  apply (sum_le_sum (s:=S) fun i hi => sum_le_sum (s:=S) fun j _ => per i hi j).trans_eq
  simp [pow_two]

end InducedDegreeRepetition.Sampling
