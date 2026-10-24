module
public import CantorDynamics.OrbitEmbedding
public import Mathlib.Topology.Baire.LocallyCompactRegular

public section
namespace CantorDynamics
open Set TopologicalSpace

@[simp] theorem shift_pow_apply (n : ℕ) (x : ShiftSpace) (i : ℤ) :
    (shift ^ n) x i = x (i + n) := by
  induction n generalizing x i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Homeomorph.mul_apply, ih]
    rw [shift_apply]
    congr 1
    omega

/-- Finite-coordinate cylinders can be joined by a sufficiently long forward
shift. No point of a prescribed closed set is used in this construction. -/
theorem shift_open_transitive {U V : Set ShiftSpace}
    (hU : IsOpen U) (hneU : U.Nonempty) (hV : IsOpen V) (hneV : V.Nonempty) :
    ∃ n : ℕ, ∃ x ∈ U, (shift ^ n) x ∈ V := by
  classical
  obtain ⟨u, hu⟩ := hneU
  obtain ⟨v, hv⟩ := hneV
  obtain ⟨I, a, ha, hsubU⟩ := isOpen_pi_iff.mp hU u hu
  obtain ⟨J, b, hb, hsubV⟩ := isOpen_pi_iff.mp hV v hv
  let n := I.sup Int.natAbs + J.sup Int.natAbs + 1
  have hsep : ∀ j ∈ J, j + (n : ℤ) ∉ I := by
    intro j hj hi
    have hi' := Finset.le_sup (f := Int.natAbs) hi
    have hj' := Finset.le_sup (f := Int.natAbs) hj
    have habs1 : j + (n : ℤ) ≤ ((j + (n : ℤ)).natAbs : ℤ) := Int.le_natAbs
    have habs2 : -j ≤ ((-j).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at habs2
    dsimp [n] at *
    omega
  let x : ShiftSpace := fun i => if i ∈ I then u i else v (i - n)
  refine ⟨n, x, hsubU ?_, hsubV ?_⟩
  · intro i hi
    change i ∈ I at hi
    simpa [x, hi] using (ha i hi).2
  · intro j hj
    change j ∈ J at hj
    rw [shift_pow_apply]
    simpa [x, hsep j hj] using (hb j hj).2

/-- Points whose forward orbit visits a given open set form an open set. -/
def visiting (U : Set ShiftSpace) : Set ShiftSpace :=
  ⋃ n : ℕ, (shift ^ n) ⁻¹' U

theorem visiting_open {U : Set ShiftSpace} (hU : IsOpen U) : IsOpen (visiting U) :=
  isOpen_iUnion fun n => hU.preimage (shift ^ n).continuous

theorem visiting_dense {U : Set ShiftSpace} (hU : IsOpen U) (hne : U.Nonempty) :
    Dense (visiting U) := by
  apply dense_iff_inter_open.mpr
  intro V hV hneV
  obtain ⟨n, x, hx, hn⟩ := shift_open_transitive hV hneV hU hne
  exact ⟨x, hx, Set.mem_iUnion.mpr ⟨n, hn⟩⟩

/-- The full two-sided Cantor shift has a dense forward orbit. Baire is applied
only after proving every nonempty basic open set has a dense open visiting set. -/
theorem shift_exists_dense_forward_orbit :
    ∃ x : ShiftSpace, Dense (Set.range (fun n : ℕ => (shift ^ n) x)) := by
  let B : Set (Set ShiftSpace) :=
    {U | U ∈ countableBasis ShiftSpace ∧ U.Nonempty}
  have : Countable B :=
    ((countable_countableBasis ShiftSpace).mono (fun _ h => h.1)).to_subtype
  have hd : Dense (⋂ U : B, visiting U.val) :=
    dense_iInter_of_isOpen
      (fun U => visiting_open ((isBasis_countableBasis ShiftSpace).isOpen U.property.1))
      (fun U => visiting_dense ((isBasis_countableBasis ShiftSpace).isOpen U.property.1)
        U.property.2)
  obtain ⟨x, hx⟩ := hd.nonempty
  refine ⟨x, dense_iff_inter_open.mpr ?_⟩
  intro U hU hneU
  obtain ⟨y, hy⟩ := hneU
  obtain ⟨W, hW, hyW, hWU⟩ :=
    (isBasis_countableBasis ShiftSpace).exists_subset_of_mem_open hy hU
  have hv := Set.mem_iInter.mp hx (⟨W, hW, ⟨y, hyW⟩⟩ : B)
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
  exact ⟨(shift ^ n) x, hWU hn, Set.mem_range_self n⟩

end CantorDynamics
