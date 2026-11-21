module

public import SimultaneousAdjustment
public import AuxiliaryVertices
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V : Type*}

@[expose] noncomputable def contribution {n : ℕ} (G : SimpleGraph V) (P : Fin n → List V) (y : V) : ℕ :=
  ∑ i, tupleDegree (adj G) y (P i)

/-- Each selected tester receives its own group change. The registered exterior
profiles preserve its original count from every other group. -/
theorem edit_groups {g n s : ℕ} (G : SimpleGraph V) (θ : ℝ)
    (Xs : Fin g → Fin n → List (Finset V)) (ex ref : Fin g → Fin n → List V)
    (ys : Fin g → Fin s → V) (selected : Fin g → Finset (Fin s)) (target : Fin g → Fin s → ℕ)
    (edits : ∀ j, Adjustable G θ (Xs j) (ex j) (ref j) (ys j))
    (external : ∀ j i k t, k ≠ j → ys k t ∈ ex j i)
    (admissible : ∀ j t, t ∈ selected j →
      θ*(∑ i, (Xs j i).length) ≤ target j t ∧
      (target j t:ℝ) ≤ (1-θ)*(∑ i, (Xs j i).length) ∧
      Even ((target j t:ℤ)-contribution G (ref j) (ys j t))) :
    ∃ repl : Fin g → Fin n → List V, (∀ j i, repl j i ∈ tupleSpace (Xs j i)) ∧
      ∀ j t, t ∈ selected j →
        (∑ k, (contribution G (repl k) (ys j t):ℤ)) =
          (∑ k, (contribution G (ref k) (ys j t):ℤ)) +
          ((target j t:ℤ)-contribution G (ref j) (ys j t)) := by
  classical
  choose repl valid keep hit _ using fun j => edits j (selected j) (target j) (admissible j)
  refine ⟨repl,valid,?_⟩
  intro j t ht
  let y := ys j t
  have same (k : Fin g) (hk : k ≠ j) : contribution G (repl k) y = contribution G (ref k) y := by
    exact sum_congr rfl fun i _ => keep k i y (external k i j t hk.symm)
  have atj : contribution G (repl j) y = target j t := hit j t ht
  change (∑ k, (contribution G (repl k) y:ℤ)) = (∑ k, (contribution G (ref k) y:ℤ)) + _
  rw [← add_sum_erase (univ : Finset (Fin g)) _ (mem_univ j),
    ← add_sum_erase (univ : Finset (Fin g)) (fun k => (contribution G (ref k) y:ℤ)) (mem_univ j),atj]
  have eq := sum_congr (s₁:=(univ:Finset (Fin g)).erase j) rfl (fun k hk => congrArg (fun v : ℕ => (v:ℤ)) (same k (mem_erase.mp hk).1))
  change (_:ℤ)+_ = _+_+((target j t:ℤ)-contribution G (ref j) y)
  rw [eq]
  ring

end InducedDegreeRepetition.Sampling
