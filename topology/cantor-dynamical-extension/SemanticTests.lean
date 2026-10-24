module
public import DynamicsSolution
public section
#check CantorDynamics.exists_extension_dense_forward_orbit
example {A : Set (ℕ → Bool)} (hA : IsClosed A) (hnA : IsNowhereDense A) (f : A ≃ₜ A) :
    ∃ H : (ℕ → Bool) ≃ₜ (ℕ → Bool),
      (∀ p : A, H p.val = (f p).val) ∧
      ∃ x : ℕ → Bool, Dense (Set.range (fun n : ℕ => (H ^ n) x)) :=
  CantorDynamics.exists_extension_dense_forward_orbit hA hnA f

-- BEGIN material-imported-definition audit
example {A : Set (ℕ → Bool)} : IsNowhereDense A ↔ interior (closure A) = ∅ := Iff.rfl
example (s : Set (ℕ → Bool)) : Dense s ↔ ∀ x, x ∈ closure s := Iff.rfl
example (f : ℕ → (ℕ → Bool)) (x : ℕ → Bool) : x ∈ Set.range f ↔ ∃ n, f n = x := Iff.rfl
example (H : (ℕ → Bool) ≃ₜ (ℕ → Bool)) (x : ℕ → Bool) : (H ^ 0) x = x := by simp
example (H : (ℕ → Bool) ≃ₜ (ℕ → Bool)) (x : ℕ → Bool) (n : ℕ) :
    (H ^ (n + 1)) x = H ((H ^ n) x) := by rw [pow_succ', Homeomorph.mul_apply]
example (H : (ℕ → Bool) ≃ₜ (ℕ → Bool)) : Function.LeftInverse H.symm H := H.symm_apply_apply
example (n : ℕ) : Continuous (fun x : ℕ → Bool => x n) := continuous_apply n
-- END material-imported-definition audit
