module
public import CantorDynamics.DenseOrbit

public section
namespace CantorDynamics

/-- Conjugation direction: transport the shift back to Cantor space. -/
def conjugatedShift (E : CantorSpace ≃ₜ ShiftSpace) : CantorSpace ≃ₜ CantorSpace :=
  (E.trans shift).trans E.symm

theorem conjugatedShift_pow (E : CantorSpace ≃ₜ ShiftSpace) (n : ℕ) (x : ShiftSpace) :
    (conjugatedShift E ^ n) (E.symm x) = E.symm ((shift ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Homeomorph.mul_apply]
    change (conjugatedShift E ^ n) (E.symm (shift (E (E.symm x)))) = _
    rw [E.apply_symm_apply, ih, pow_succ, Homeomorph.mul_apply]

/-- **Cantor dynamical extension, invariant-subset case.** Every homeomorphism
of a closed nowhere-dense Cantor subset extends to an ambient homeomorphism
with a dense forward orbit. Empty prescribed subsets are included. -/
theorem exists_extension_dense_forward_orbit {A : Set CantorSpace}
    (hA : IsClosed A) (hnA : IsNowhereDense A) (f : A ≃ₜ A) :
    ∃ H : CantorSpace ≃ₜ CantorSpace,
      (∀ p : A, H p.val = (f p).val) ∧
      ∃ x : CantorSpace, Dense (Set.range (fun n : ℕ => (H ^ n) x)) := by
  obtain ⟨E, hE⟩ := exists_ambient_orbitEmbedding hA hnA f
  obtain ⟨x, hx⟩ := shift_exists_dense_forward_orbit
  refine ⟨conjugatedShift E, ?_, E.symm x, ?_⟩
  · intro p
    change E.symm (shift (E p.val)) = (f p).val
    rw [hE p, shift_orbitEmbedding, ← hE (f p), E.symm_apply_apply]
  · have hr : (fun n : ℕ => (conjugatedShift E ^ n) (E.symm x)) =
        (fun n : ℕ => E.symm ((shift ^ n) x)) :=
      funext (fun n => conjugatedShift_pow E n x)
    rw [hr]
    exact E.symm.surjective.denseRange.comp hx E.symm.continuous

end CantorDynamics
