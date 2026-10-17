module
import HMPSolution
open HMP TopologicalSpace
open scoped Cardinal
-- The continuum-sized cube is separable (not just countable-index products).
example : SeparableSpace ((ℕ → Bool) → Bool) := by
 apply separable_product
 simp
-- Increasing the number of nontrivial coordinates past continuum fails.
example : ¬ SeparableSpace ((Set (ℕ → Bool)) → Bool) := by
 rw [boolean_cube_separable_iff]
 have h : #(ℕ → Bool) < #(Set (ℕ → Bool)) := by
   simpa only [Cardinal.mk_set] using Cardinal.cantor #(ℕ → Bool)
 have heq : #(ℕ → Bool) = 𝔠 := by simp
 rw [← heq]
 exact not_le_of_gt h
-- Empty factors and singleton factors show that the upper bound is sufficient,
-- not necessary for arbitrary families; the Boolean sharpness has exact scope.
example : SeparableSpace ((Set (ℕ → Bool)) → Empty) := inferInstance
example : SeparableSpace ((Set (ℕ → Bool)) → Unit) := inferInstance
-- The empty-index product has one point even when the nominal factor is empty.
example : SeparableSpace (Empty → Empty) := inferInstance

-- Invoke HMP itself on the empty-factor and empty-index branches.
example : SeparableSpace (Fin 1 → Empty) :=
  separable_product (by simpa using (Cardinal.nat_lt_continuum 1).le)
example : SeparableSpace (Empty → Empty) :=
  separable_product (by simp)

-- The cardinal bridge is universe-polymorphic, not a Type-0-only shortcut.
example : SeparableSpace (ULift.{1} (ℕ → Bool) → Bool) :=
  separable_product (by simp)

example : Countable RowCode := inferInstance
example (e : ℕ ↪ (ℕ → Bool)) (d : ℕ → ℕ → Bool) (c : RowCode) (i : ℕ) :
 row e d c i = d i (c.2 (fun k => e i k)) := rfl
