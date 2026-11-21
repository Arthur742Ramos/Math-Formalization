module

public import ApproximateBias
public import ImageRectangle
public import ColumnSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Approximation

open Finset Filter
open scoped Classical Topology
variable {q : ℕ} [NeZero q]

theorem approximation_rectangle (hq : 3 ≤ q) (D η : ℝ) (hd : 0 < D) (he : 0 < η) :
    ∀ᶠ r : ℕ in atTop, ∀ (X Y : Type) (A B : X → Y → ZMod q) (S : Finset X) (U : Finset Y),
      S.Nonempty → U.Nonempty → (∀ x ∈ S, ∀ y ∈ U, B x y = 0 ∨ B x y = 1) →
      errors (fun x y => A x y ≠ B x y) S U ≤ (1/8:ℝ)*S.card*U.card →
      complexity A S U ≤ D*r →
      ∃ R ⊆ S, ∃ V ⊆ U, Real.exp (-η*r)*S.card ≤ R.card ∧ Real.exp (-η*r)*U.card ≤ V.card ∧
        (complexity A R U ≤ (complexity A S U + Real.log q)/2 ∨
          complexity A S V ≤ (complexity A S U + Real.log q)/2) := by
  classical
  filter_upwards [rectangle_of_image_size q hq D η hd he] with r rect
  intro X Y A B S U hs hu bin low size
  let : Nonempty S := hs.to_subtype
  let : Nonempty U := hu.to_subtype
  let G := colSpace A S U
  let v (y : U) : G := ⟨column A S y,col_mem A S y.2⟩
  let T (x : S) : G →+ ZMod q :=
    {toFun := fun u => u.val x, map_zero' := rfl, map_add' := by intros; rfl}
  have bias := bias_from_errors hq A B S U bin low
  have eq : (∑ x ∈ S, ∑ y ∈ U, ZMod.stdAddChar (A x y)) =
      ∑ y : U, ∑ x : S, ZMod.stdAddChar (T x (v y)) := by
    rw [sum_comm,sum_subtype U (fun _ => Iff.rfl)]
    exact sum_congr rfl fun y _ => sum_subtype S (fun _ => Iff.rfl) _
  rw [eq,mul_comm (S.card:ℝ)] at bias
  obtain ⟨V,R,t,hV,hR,constant⟩ := rect G U S (ZModModule.char_nsmul_eq_zero q)
    (by simpa [complexity,G,Nat.card_eq_fintype_card] using size) v T (by simpa using bias)
  let R' := R.image Subtype.val
  let V' := V.image Subtype.val
  have rsub : R' ⊆ S := by rintro _ h; obtain ⟨x,_,rfl⟩ := mem_image.mp h; exact x.2
  have vsub : V' ⊆ U := by rintro _ h; obtain ⟨y,_,rfl⟩ := mem_image.mp h; exact y.2
  refine ⟨R',rsub,V',vsub,?_,?_,strip_complexity A rsub vsub t ?_⟩
  · simpa [R',card_image_of_injective _ Subtype.val_injective] using hR
  · simpa [V',card_image_of_injective _ Subtype.val_injective] using hV
  · intro x hx y hy
    obtain ⟨i,hi,ex⟩ := (mem_image.mp hx : ∃ i ∈ R, (i:X) = x)
    obtain ⟨j,hj,ey⟩ := (mem_image.mp hy : ∃ i ∈ V, (i:Y) = y)
    rw [← ex,← ey]
    exact constant j hj i hi

end InducedDegreeRepetition.Approximation
