module

public import IndependentVariance
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical

/-- For a fixed group, exterior labels only involve the other groups. Integrate
the uniform estimate conditional on those labels over the full product draw. -/
theorem mean_group {I : Type*} [Fintype I] [DecidableEq I] (R T : I → Type*)
    [∀ i, Fintype (R i)] [∀ i, Fintype (T i)] [∀ i, Nonempty (R i)] [∀ i, Nonempty (T i)]
    (i : I) (f : (∀ j : {j // j ≠ i}, T j) → R i → T i → ℝ) (ε : ℝ)
    (h : ∀ other, mean (fun z : R i × T i => f other z.1 z.2) ≤ ε) :
    mean (fun p : (∀ j, R j) × (∀ j, T j) => f (fun j => p.2 j) (p.1 i) (p.2 i)) ≤ ε := by
  classical
  let O := {j : I // j ≠ i}
  let e : ((∀ j, R j) × (∀ j, T j)) ≃ (∀ j : O, T j) × ((R i × T i) × (∀ j : O, R j)) :=
    (Equiv.prodCongr (Equiv.piSplitAt i R) (Equiv.piSplitAt i T)).trans
      ⟨fun p => (p.2.2,((p.1.1,p.2.1),p.1.2)),fun p => ((p.2.1.1,p.2.2),(p.2.1.2,p.1)),
        fun _ => rfl,fun _ => rfl⟩
  let g (o : ∀ j : O, T j) (z : R i × T i) (_ : ∀ j : O, R j) := f o z.1 z.2
  have eq := mean_equiv e
    (fun p : (∀ j, R j) × (∀ j, T j) => f (fun j => p.2 j) (p.1 i) (p.2 i))
    (fun p => g p.1 p.2.1 p.2.2) (fun _ => rfl)
  rw [eq,mean_prod (fun o (p : (R i × T i) × (∀ j : O, R j)) => g o p.1 p.2),← mean_const (X:=∀ j : O,T j) ε]
  apply mean_le
  intro o
  rw [mean_prod (g o)]
  simpa only [g,mean_const] using h o

end InducedDegreeRepetition.Sampling
