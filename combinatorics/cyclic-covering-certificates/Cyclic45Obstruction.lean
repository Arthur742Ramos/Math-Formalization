module
/- Kernel-checked components of the cyclic Z45 relative-difference-set
   obstruction. These prove the projection-count arithmetic and the actual
   no-lift three-cycle statement. The general combinatorial counting bridge
   from an arbitrary relative difference set to those fiber equations is
   supplied in the written proof, and is not claimed formalized here. -/
public import Std
public section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace CoveringCyclic45

@[expose] def diff (a b : Fin 45) : Nat := (b.val + 45 - a.val) % 45

/-- The only way five fibers of capacity three can have the projected
    (15,7,3) difference-set counts is for some fiber to be full.
    The displayed nonzero cyclic correlations and square sum are exact. -/
theorem full_fiber_from_counts : ∀ a b c d e : Fin 4,
    a.val + b.val + c.val + d.val + e.val = 7 →
    a.val*a.val + b.val*b.val + c.val*c.val + d.val*d.val + e.val*e.val = 13 →
    a.val*b.val + b.val*c.val + c.val*d.val + d.val*e.val + e.val*a.val = 9 →
    a.val*c.val + b.val*d.val + c.val*e.val + d.val*a.val + e.val*b.val = 9 →
    a.val = 3 ∨ b.val = 3 ∨ c.val = 3 ∨ d.val = 3 ∨ e.val = 3 := by decide

/-- Three directed differences above the quotient residue five cannot
    all be distinct: their complete target list would sum to fifteen
    modulo forty-five, while a cycle telescopes to zero. -/
theorem no_distinct_lifted_three_cycle (a b c : Fin 45)
    (h1 : diff a b % 15 = 5)
    (h2 : diff b c % 15 = 5)
    (h3 : diff c a % 15 = 5)
    (hne1 : diff a b ≠ diff b c)
    (hne2 : diff b c ≠ diff c a)
    (hne3 : diff c a ≠ diff a b) : False := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [diff] at *
  omega

/-- Uniqueness of ordered nontrivial differences is part of the original
    relative-difference-set definition, independent of the hole condition. -/
@[expose] def UniqueOrderedDifferences {n : Nat} (B : Fin n → Fin 45) : Prop :=
  ∀ i j r s, i ≠ j → r ≠ s → diff (B i) (B j) = diff (B r) (B s) →
    i = r ∧ j = s

/-- A set with unique ordered differences cannot contain three projected
    points forming a full order-three coset modulo fifteen. -/
theorem unique_differences_exclude_projected_cycle {n : Nat}
    (B : Fin n → Fin 45) (hu : UniqueOrderedDifferences B)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (h1 : diff (B i) (B j) % 15 = 5)
    (h2 : diff (B j) (B k) % 15 = 5)
    (h3 : diff (B k) (B i) % 15 = 5) : False := by
  apply no_distinct_lifted_three_cycle (B i) (B j) (B k) h1 h2 h3
  · intro he
    exact hij (hu i j j k hij hjk he).1
  · intro he
    exact hjk (hu j k k i hjk hki he).1
  · intro he
    exact hki (hu k i i j hki hij he).1

#print axioms full_fiber_from_counts
#print axioms no_distinct_lifted_three_cycle
#print axioms unique_differences_exclude_projected_cycle
end CoveringCyclic45
