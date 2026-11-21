module

public import DualityFibers
public import DualityStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical
variable {G Y : Type*} [AddCommGroup G] [Fintype G] [Fintype Y] {q : ℕ} [NeZero q]

/-- The two lower bounds are a row probability and a column count. -/
@[expose] def Rectangle (f : Law G) (T : Y → G →+ ZMod q) (a b : ℝ) : Prop :=
  ∃ (S : Finset G) (U : Finset Y) (t : ZMod q), a ≤ ∑ x ∈ S, f x ∧
    b ≤ (U.card : ℝ) ∧ ∀ x ∈ S, ∀ y ∈ U, T y x = t

omit [Fintype Y] [NeZero q] in
theorem Rectangle.mono {f : Law G} {T : Y → G →+ ZMod q} {a b a' b' : ℝ}
    (r : Rectangle f T a b) (ha : a' ≤ a) (hb : b' ≤ b) : Rectangle f T a' b' := by
  obtain ⟨S,U,t,hs,hu,e⟩ := r
  exact ⟨S,U,t,ha.trans hs,hb.trans hu,e⟩

theorem largest_residue {X : Type*} (S : Finset X) (c : X → ZMod q) (w : X → ℝ) :
    ∃ t : ZMod q, (∑ x ∈ S, w x) / q ≤ ∑ x ∈ S.filter (fun x => c x = t), w x := by
  classical
  let m := fun t => ∑ x ∈ S.filter (fun x => c x = t), w x
  obtain ⟨t,_,h⟩ := exists_max_image (univ : Finset (ZMod q)) m univ_nonempty
  refine ⟨t,(div_le_iff₀ (by exact_mod_cast NeZero.pos q)).mpr ?_⟩
  have hm := sum_le_sum (s := (univ : Finset (ZMod q))) (fun j _ => h j (mem_univ j))
  simpa [m,sum_fiberwise,mul_comm] using hm

theorem largest_residue_card {X : Type*} (S : Finset X) (c : X → ZMod q) :
    ∃ t : ZMod q, (S.card : ℝ)/q ≤ ((S.filter (fun x => c x = t)).card : ℝ) := by
  simpa using largest_residue S c (fun _ => (1:ℝ))

omit [Fintype Y] in
/-- Fix the anchor value on a column fiber to lift a rectangle through a step of
spectral conditioning. -/
theorem lift_rectangle {f g : Law G} (T : Y → G →+ ZMod q) (δ a b : ℝ) (hd : 0 ≤ δ)
    (dom : ∀ z, δ * g z ≤ diff f z) (r : Rectangle g T a b) :
    Rectangle f T (δ*a) (b/q) := by
  classical
  obtain ⟨S,U,t,hs,hu,eq⟩ := r
  have total : δ*a ≤ ∑ x ∈ S, diff f x := by
    apply (mul_le_mul_of_nonneg_left hs hd).trans
    rw [mul_sum]
    exact sum_le_sum fun x _ => dom x
  obtain ⟨z,hz⟩ := lift_difference_set f S
  obtain ⟨v,hv⟩ := largest_residue_card U fun y => T y z
  refine ⟨univ.filter (fun x => x-z ∈ S), U.filter (fun y => T y z = v),t+v,
    total.trans hz,(div_le_div_of_nonneg_right hu (Nat.cast_nonneg _)).trans hv,?_⟩
  intro x hx y hy
  obtain ⟨hy,hv⟩ := mem_filter.mp hy
  have e := eq _ (mem_filter.mp hx).2 y hy
  rw [map_sub,hv] at e
  exact sub_eq_iff_eq_add.mp e

/-- Energy stability and spectral support give one constant rectangle by applying
coset concentration and grouping columns by their restrictions to the subgroup. -/
theorem rectangle_of_coset [Nonempty Y] (f : Law G) (T : Y → G →+ ZMod q)
    (H : AddSubgroup G) (z : G) (P δ : ℝ) (hP : 0 < P) (hd : 0 < δ)
    (size : (Fintype.card H : ℝ) * normSq f ≤ P)
    (mass : 1/P ≤ massOn f {x | x-z ∈ H})
    (support : ∀ x, 0 < f x → δ * Fintype.card Y ≤ (spectrum T x).re) :
    Rectangle f T (1/P/q) (δ^2 * Fintype.card Y / P^3 /q) := by
  classical
  let S := univ.filter (fun x : G => x-z ∈ H)
  have hm : 1/P ≤ ∑ x ∈ S, f x := by simpa [massOn,S,sum_filter] using mass
  obtain ⟨i,hi⟩ := large_trace_fiber f T H z P δ hP hd size ((coset_sum H z f.val) ▸ hm) support
  let U := univ.filter fun j => trace T H i = trace T H j
  obtain ⟨v,hv⟩ := largest_residue_card U fun y => T y z
  obtain ⟨t,ht⟩ := largest_residue S (fun x => T i (x-z)) f.val
  refine ⟨S.filter (fun x => T i (x-z) = t),U.filter (fun y => T y z = v), t+v,
    (div_le_div_of_nonneg_right hm (Nat.cast_nonneg _)).trans ht,?_,?_⟩
  · apply le_trans _ hv
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact (div_le_iff₀ (pow_pos hP 3)).mpr (by simpa [mul_comm] using hi)
  · intro x hx y hy
    obtain ⟨hx,ht⟩ := mem_filter.mp hx
    obtain ⟨hy,hv⟩ := mem_filter.mp hy
    have mem : x-z ∈ H := (mem_filter.mp hx).2
    have e := DFunLike.congr_fun (mem_filter.mp hy).2 (⟨x-z,mem⟩ : H)
    change T i (x-z) = T y (x-z) at e
    rw [ht,map_sub,hv] at e
    exact sub_eq_iff_eq_add.mp e.symm

end InducedDegreeRepetition.Duality
