module

public import SampleCompression
public import LabelSamples
public import RemainingStatements
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Restriction

open Finset Filter Submodule Matrix OpenProblems
open scoped Classical Topology
variable {q : ℕ} [NeZero q]

@[expose] def smallSample {I X Y : Type} (A : X → Y → ZMod q) (xs : I → X) (ys : I → Y) (d : ℝ) : Prop :=
  let M : Matrix I I (ZMod q) := fun i j => A (xs i) (ys j)
  (Nat.card (span (ZMod q) (Set.range M.row)) : ℝ) ≤ d

/-- A heavy coset on the fixed testers gives a lower bound on the probability that
an independent row sample has small image. -/
theorem heavy_chance {N n r : ℕ} (G : SimpleGraph (Fin N)) (X Y : Finset (Fin N))
    (D a : ℝ) (ys : Fin n → Y) (heavy : HeavyRestriction q G X (forget ys) r D a) :
    Real.exp (-a*r*n) * Fintype.card (Fin n → X) ≤ ∑ xs : Fin n → X,
      if smallSample (fun (x:X) (y:Y) => adjMod q G x y) xs ys (q*Real.exp (D*r)) then (1:ℝ) else 0 := by
  classical
  obtain ⟨H,z,hsize,hm⟩ := heavy
  let row (x : Fin N) (j : Fin n) := adjMod q G x (ys j)
  let P (x : Fin N) := row x-z ∈ H
  let S := (univ : Finset X).filter fun x : X => P x
  have e : labels S = X.filter P := by rw [show S = univ.filter (fun x : X => P x) from rfl,labels_filter,labels_univ]
  have mass : Real.exp (-a*r)*X.card ≤ S.card := by
    rw [← card_labels S,e]
    exact hm.le
  let test := Fintype.piFinset (fun _ : Fin n => S)
  have ok (xs : Fin n → X) (hx : xs ∈ test) :
      smallSample (fun (x:X) (y:Y) => adjMod q G x y) xs ys (q*Real.exp (D*r)) := by
    let M : Matrix (Fin n) (Fin n) (ZMod q) := fun i j => row (xs i) j
    have h (i : Fin n) : M.row i - z ∈ H := (mem_filter.mp ((Fintype.mem_piFinset.mp hx) i)).2
    have b := coset_row_span M H z h
    exact (show (Nat.card (span (ZMod q) (Set.range M.row)):ℝ) ≤ q*Nat.card H by exact_mod_cast b).trans
      (mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg _))
  have p := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) mass n
  have cnt : (test.card:ℝ) ≤ ∑ xs : Fin n → X,
      if smallSample (fun (x:X) (y:Y) => adjMod q G x y) xs ys (q*Real.exp (D*r)) then (1:ℝ) else 0 := by
    rw [sum_boole]
    exact_mod_cast card_le_card (fun xs hx => mem_filter.mpr ⟨mem_univ xs,ok xs hx⟩)
  apply le_trans _ cnt
  simp only [test,Fintype.card_piFinset,prod_const,card_univ,Fintype.card_fin,Nat.cast_pow,
    Fintype.card_fun,Fintype.card_coe]
  rw [mul_pow,← Real.exp_nat_mul] at p
  simpa [mul_comm] using p

end InducedDegreeRepetition.Restriction
