module

public import Witness
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical

theorem nearby_parity (x : ℝ) (hx : 0 ≤ x) (e : ℕ) (he : e < 2) :
    ∃ d : ℕ, d%2=e ∧ |(d:ℝ)-x| ≤ 2 := by
  refine ⟨2*⌊x/2⌋₊+e,by omega,?_⟩
  have lo := Nat.floor_le (show 0 ≤ x/2 by positivity)
  have hi := Nat.lt_floor_add_one (x/2)
  have ep : (e:ℝ) ≤ 1 := by exact_mod_cast (by omega : e ≤ 1)
  rw [abs_le]
  push_cast
  constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) e]

/-- The exact nonnegative edit count for a good row. Its parity is the original
group parity and its total after the change is the common degree. -/
theorem adjustment_target (g m k E total own d : ℕ) (p θ v : ℝ)
    (hθ : 0 < θ) (hp : 2*θ ≤ p) (hp' : p ≤ 1-2*θ)
    (margin : 2+((g:ℝ)+2)*v ≤ θ*m)
    (near : |(d:ℝ)-p*(E+g*m)| ≤ 2)
    (base : |(k:ℝ)-p*E| ≤ v) (group : |(own:ℝ)-p*m| ≤ v)
    (all : |(total:ℝ)-p*(g*m)| ≤ g*v)
    (parity : (k+total)%2=d%2) :
    ∃ c : ℕ, θ*m ≤ c ∧ (c:ℝ) ≤ (1-θ)*m ∧ Even ((c:ℤ)-own) ∧
      (c:ℤ) = (own:ℤ)+d-k-total := by
  let z : ℤ := (own:ℤ)+d-k-total
  rw [abs_le] at near base group all
  have bounds : θ*m ≤ (z:ℝ) ∧ (z:ℝ) ≤ (1-θ)*m := by
    dsimp [z]
    push_cast at *
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg m : (0:ℝ) ≤ m),
      mul_le_mul_of_nonneg_right hp' (Nat.cast_nonneg m : (0:ℝ)≤m)]
  have zn : 0 ≤ z := by exact_mod_cast (mul_nonneg hθ.le (Nat.cast_nonneg _)).trans bounds.1
  have ez := Int.toNat_of_nonneg zn
  have cast : (z.toNat:ℝ) = (z:ℝ) := by exact_mod_cast ez
  refine ⟨z.toNat,cast ▸ bounds.1,cast ▸ bounds.2,?_,ez⟩
  rw [ez,Int.even_iff]
  dsimp [z]
  omega

end InducedDegreeRepetition.Sampling
