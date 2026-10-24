module
public import EZero.Definitions
public import EZero.Category

@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology
namespace EZero

/-- Finite changes of binary values connect any two nonempty open cylinders.
No orbit-density or mixing premise is supplied. -/
theorem finite_flip_mixing (U V : Set CantorSpace) (_hU : IsOpen U) (hneU : U.Nonempty)
    (hV : IsOpen V) (hneV : V.Nonempty) :
    ∃ s : Finset ℕ, (U ∩ flip s ⁻¹' V).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := hneU
  obtain ⟨y, hy⟩ := hneV
  obtain ⟨S, v, hv, hsub⟩ := isOpen_pi_iff.mp hV y hy
  let s := S.filter (fun n => x n ≠ y n)
  have hm (n : ℕ) (hn : n ∈ S) : flip s x n = y n := by
    cases hx' : x n <;> cases hy' : y n <;> simp [flip, s, hn, hx', hy']
  refine ⟨s, x, hx, hsub ?_⟩
  intro n hn
  rw [hm n hn]
  exact (hv n hn).2

/-- E₀'s category zero-one law for its actual finite-value-change relation. -/
theorem zero_one {A : Set CantorSpace} (hA : BaireMeasurableSet A)
    (hinv : ∀ x y, E0 x y → (x ∈ A ↔ y ∈ A)) : IsMeagre A ∨ IsMeagre Aᶜ := by
  apply zero_one_of_mixing (fun s : Finset ℕ => flip s) finite_flip_mixing hA
  exact fun s x => hinv x (flip s x) (e0_flip s x)

end EZero
