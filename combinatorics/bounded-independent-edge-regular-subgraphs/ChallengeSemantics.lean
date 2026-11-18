module

public import Challenge

open MeasureTheory ProbabilityTheory BoundedEdgeRegularSubgraphs
open scoped BigOperators

-- BEGIN material-imported-definition audit

section

variable {V : Type} [Fintype V] [LinearOrder V]

example (p : Edge V → Set.Icc (0 : ℝ) 1) (s : Edge V → Set ℝ) :
    graphLaw p (Set.pi Set.univ s) =
      ∏ e : Edge V, bernoulliMeasure (1 : ℝ) 0 (p e) (s e) := by
  exact Measure.pi_pi _ _

example (p : Set.Icc (0 : ℝ) 1) :
    (bernoulliMeasure (1 : ℝ) 0 p).real {(1 : ℝ)} = (p : ℝ) := by
  exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton 1)
    (by simp) (by simp)

example (p : Set.Icc (0 : ℝ) 1) :
    (bernoulliMeasure (1 : ℝ) 0 p).real {(0 : ℝ)} = 1 - (p : ℝ) := by
  exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton 0)
    (by simp) (by simp)

example (p : Edge V → Set.Icc (0 : ℝ) 1) (s : Set (Edge V → ℝ)) :
    (graphLaw p).real s = (graphLaw p s).toReal :=
  measureReal_def (graphLaw p) s

example (s : Set (Edge V → ℝ)) :
    sᶜ = {g | g ∉ s} := rfl

example (ι : Type) (s : ι → Set (Edge V → ℝ)) (g : Edge V → ℝ) :
    g ∈ ⋃ i, s i ↔ ∃ i, g ∈ s i := Set.mem_iUnion

example (S : Finset V) (s : Set (Edge S → ℝ)) (g : Edge V → ℝ) :
    g ∈ induce S ⁻¹' s ↔ induce S g ∈ s := Iff.rfl

example (x : ℝ) :
    x ∈ Set.Icc (0 : ℝ) 1 ↔ 0 ≤ x ∧ x ≤ 1 := Iff.rfl

example {x : ℝ} {n : ℕ} : ⌈x⌉₊ ≤ n ↔ x ≤ (n : ℝ) := Nat.ceil_le

example (s : Finset V) : s.card = s.val.card := rfl

example (n : ℕ) : (Finset.univ : Finset (Fin n)).card = n := by
  rw [Finset.card_univ, Fintype.card_fin]

example (x y : ℝ) (hx : 0 < x) :
    x ^ y = Real.exp (Real.log x * y) := Real.rpow_def_of_pos hx y

example (x : ℝ) : Real.exp x = (Complex.exp (x : ℂ)).re := rfl

example (x : ℝ) : Real.log (Real.exp x) = x := Real.log_exp x

example (x : ℝ) : Real.sqrt x = x ^ (1 / (2 : ℝ)) := Real.sqrt_eq_rpow x

example (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    A.rank = Module.finrank ℝ (LinearMap.range A.mulVecLin) := rfl

end

-- END material-imported-definition audit
