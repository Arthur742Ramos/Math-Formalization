module

public import SampleCompression
public import HeavyChance
public import DesignatedLabels
public import ModelAgreement
public import AgreementMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Restriction

open Finset Filter Submodule Matrix OpenProblems Approximation
open scoped Classical Topology
variable {q : ℕ} [NeZero q]

set_option maxHeartbeats 3000000 in
/-- The joint small-image event for independent sampled rows and columns. -/
theorem small_sample_probability (hq : 3 ≤ q) (u τ c D : ℝ) (hu : 0<u) (hτ : 0<τ)
    (hc : 0<c) (hd : 0<D) : ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ r : ℕ in atTop,
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B X Y : Finset (Fin N)), Core G B r u τ c →
      Disjoint X Y → Large B X r u 8 → Large B Y r u 8 →
      let n := ⌈C*r⌉₊
      let A := fun (x : X) (y : Y) => adjMod q G x y
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y, if smallSample A xs ys (q*Real.exp (D*r)) then (1:ℝ) else 0) ≤
        Real.exp (-u*r*n/64) * Fintype.card (Fin n → X) * Fintype.card (Fin n → Y) := by
  classical
  obtain ⟨γ,hg,hg',sparse⟩ := few_agreeing_rows q hq τ hτ
  let H := generatorRate q D
  let C := sampleRate q D u γ
  have rate := rate_positive q hq D u γ hd hu hg
  have lq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1<q))
  refine ⟨C,rate.2,?_⟩
  filter_upwards [sparse (H*Real.log q) u c (mul_pos rate.1 lq) hu hc, moment_rate u hu,
    union_rate u hu,eventually_ge_atTop 1] with r few decay union hr
  intro N G B X Y core dis lx ly
  let n := ⌈C*r⌉₊
  let A (x:X) (y:Y) := adjMod q G x y
  let S0 := (B.card:ℝ)*Real.exp (-u*r/4)
  let p := Real.exp (-u*r/8)
  have cut (s : ℕ) (h : (B.card:ℝ)*Real.exp (-u*r/8) ≤ s) : S0 ≤ p*s := by
    apply le_trans _ (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le)
    dsimp [S0,p]
    rw [mul_left_comm,← Real.exp_add]
    apply le_of_eq; ring_nf
  let T := fun (R C' : Finset (Fin n)) => (R.card:ℝ) ≤ H*r ∧ (C'.card:ℝ) ≤ H*r
  let ok := fun (R C' : Finset (Fin n)) (xs : R → X) (ys : C' → Y) (x : X) (y : Y) =>
    model (adjMod q G) (fun i => (xs i).val) (fun j => (ys j).val) x y = A x y
  let P := fun (xs : Fin n → X) (ys : Fin n → Y) => smallSample A xs ys (q*Real.exp (D*r))
  have witness (xs : Fin n → X) (ys : Fin n → Y) (hp : P xs ys) :
      ∃ R C', T R C' ∧ ∀ (i : {i : Fin n // i ∉ R}) (j : {j : Fin n // j ∉ C'}),
        ok R C' (fun i => xs i) (fun j => ys j) (xs i) (ys j) := by
    let M : Matrix (Fin n) (Fin n) (ZMod q) := fun i j => A (xs i) (ys j)
    obtain ⟨R,C',gr,gc,sr,sc⟩ := generating_positions M
    have budget {s : ℕ} (h : 2^s ≤ Nat.card (span (ZMod q) (Set.range M.row))) :
        (s:ℝ) ≤ H*r := generator_budget q hq D r s hr ((by exact_mod_cast h : (2:ℝ)^s ≤
          (Nat.card (span (ZMod q) (Set.range M.row)):ℝ)).trans hp)
    have exact' := sampled_model_exact (adjMod q G) (fun i => (xs i).val) (fun j => (ys j).val)
      R C' M (fun _ _ => rfl) gr gc
    exact ⟨R,C',⟨budget sr,budget sc⟩,fun i j => exact' i j⟩
  let F := 2*Real.exp (-u*r*n/32)
  have fit (R C' : Finset (Fin n)) (sizes : T R C') (xs : R → X) (ys : C' → Y) :
      samples {i : Fin n // i ∉ R} {j : Fin n // j ∉ C'} (ok R C' xs ys) ≤
        F*Fintype.card ({i : Fin n // i ∉ R} → X)*Fintype.card ({j : Fin n // j ∉ C'} → Y) := by
    let M := model (adjMod q G) (fun i => (xs i).val) (fun j => (ys j).val)
    have low (s : Finset (Fin N)) (_ : s ⊆ X) (v : Finset (Fin N)) (_ : v ⊆ Y) :
        complexity M s v ≤ (H*Real.log q)*r := by
      apply (model_complexity ..).trans
      rw [Fintype.card_coe]
      nlinarith [mul_le_mul_of_nonneg_right sizes.1 lq.le]
    have sparse' (V : Finset (Fin N)) (hV : V ⊆ Y) (h : S0 ≤ V.card) :=
      few N G B X Y M core dis lx.1 ly.1 low V hV h
    have est := agreement_moment (X := X) (Y := Y) (fun x y => M x y = adjMod q G x y) S0 p (1-γ)
      (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le (by linarith only [hg'])
      (cut _ lx.2) (cut _ ly.2) (by
        intro V hV hh
        convert sparse' V hV hh using 1
        apply congrArg Nat.cast
        apply congrArg Finset.card
        ext x
        simp only [mem_filter]
        apply and_congr_right
        intro _
        apply Iff.of_eq
        apply congrArg (fun n : ℕ => (1-γ)*V.card < (n:ℝ))
        apply congrArg Finset.card
        ext y
        simp) {i : Fin n // i ∉ R} {j : Fin n // j ∉ C'}
    apply est.trans
    simp only [Fintype.card_fun,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have kr := free_budget q hq D u γ hd hu hg r _ sizes.1
    have mc := free_budget q hq D u γ hd hu hg r _ sizes.2
    simpa [p,F,Fintype.card_subtype_compl] using decay n (n-R.card) (n-C'.card) γ hg hg' kr.1 mc.1 mc.2
  have cmp := compression_count P T ok witness F (by dsimp [F]; positivity) fit
  have nr : (1:ℝ) ≤ n := (show (1:ℝ) ≤ C*r from (show (1:ℝ) ≤ r by exact_mod_cast hr).trans (le_mul_of_one_le_left (Nat.cast_nonneg _) rate.2)).trans (Nat.le_ceil _)
  apply cmp.trans
  simp only [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (union n (by exact_mod_cast nr))
    (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end InducedDegreeRepetition.Restriction
