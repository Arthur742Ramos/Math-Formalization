module

public import ModularMatrices
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Approximation

open Finset Matrix Submodule
open scoped Classical
variable {X Y : Type*} {q : ℕ} [NeZero q]
abbrev column (A : X → Y → ZMod q) (S : Finset X) (y : Y) (x : S) := A x y

@[expose] noncomputable def colSpace (A : X → Y → ZMod q) (S : Finset X) (U : Finset Y) :
    Submodule (ZMod q) (S → ZMod q) := Submodule.span _ (column A S '' (U : Set Y))

@[expose] noncomputable def complexity (A : X → Y → ZMod q) (S : Finset X) (U : Finset Y) : ℝ :=
  Real.log (Nat.card (colSpace A S U))

omit [NeZero q] in
theorem col_mem (A : X → Y → ZMod q) (S : Finset X) {U : Finset Y} {y : Y} (hy : y ∈ U) :
    column A S y ∈ colSpace A S U := Submodule.subset_span ⟨y,hy,rfl⟩

omit [NeZero q] in
theorem colSpace_mono (A : X → Y → ZMod q) (S : Finset X) {U V : Finset Y} (h : V ⊆ U) :
    colSpace A S V ≤ colSpace A S U := Submodule.span_mono (Set.image_mono h)

@[expose] def restrictRows {S R : Finset X} (h : R ⊆ S) :
    (S → ZMod q) →ₗ[ZMod q] (R → ZMod q) :=
  LinearMap.funLeft _ _ (fun x => ⟨x.1,h x.2⟩)

omit [NeZero q] in
theorem map_colSpace (A : X → Y → ZMod q) {S R : Finset X} (h : R ⊆ S) (U : Finset Y) :
    (colSpace A S U).map (restrictRows h) = colSpace A R U := by
  rw [colSpace,LinearMap.map_span,Set.image_image]
  rfl

theorem complexity_mono (A : X → Y → ZMod q) {S R : Finset X} {U V : Finset Y}
    (h : R ⊆ S) (h' : V ⊆ U) : complexity A R V ≤ complexity A S U := by
  let I := colSpace A S V
  have sur : Function.Surjective (fun x : I => (⟨restrictRows h x,Submodule.mem_map_of_mem x.property⟩ :
      I.map (restrictRows h))) := by
    rintro ⟨v,u,hu,rfl⟩
    exact ⟨⟨u,hu⟩,rfl⟩
  have proj := Nat.card_le_card_of_surjective _ sur
  change Nat.card ((colSpace A S V).map (restrictRows h)) ≤ Nat.card (colSpace A S V) at proj
  rw [map_colSpace] at proj
  have incl := Nat.card_le_card_of_injective _ (Submodule.inclusion_injective (colSpace_mono A S h'))
  apply Real.log_le_log (by exact_mod_cast Nat.card_pos)
  exact_mod_cast proj.trans incl

theorem constant_card (A : X → Y → ZMod q) (S : Finset X) (U : Finset Y) (t : ZMod q)
    (h : ∀ x ∈ S, ∀ y ∈ U, A x y = t) : Nat.card (colSpace A S U) ≤ q := by
  let const : ZMod q →ₗ[ZMod q] (S → ZMod q) :=
    {toFun := fun a _ => a, map_add' := by intros; rfl, map_smul' := by intros; rfl}
  have le : colSpace A S U ≤ LinearMap.range const := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y,hy,rfl⟩
    exact ⟨t,funext fun x => (h x x.2 y hy).symm⟩
  have incl := Nat.card_le_card_of_injective _ (Submodule.inclusion_injective le)
  have sur := Nat.card_le_card_of_surjective const.rangeRestrict (show Function.Surjective const.rangeRestrict by
    rintro ⟨_,a,rfl⟩
    exact ⟨a,rfl⟩)
  simpa using incl.trans sur

theorem strip_product (A : X → Y → ZMod q) {S R : Finset X} {U V : Finset Y}
    (hr : R ⊆ S) (hv : V ⊆ U) (t : ZMod q) (eq : ∀ x ∈ R, ∀ y ∈ V, A x y = t) :
    Nat.card (colSpace A R U) * Nat.card (colSpace A S V) ≤ q*Nat.card (colSpace A S U) := by
  let I := colSpace A S U
  let J := colSpace A S V
  let f := restrictRows (q := q) hr
  let p := f.domRestrict I
  let T := J.comap I.subtype
  have e := Submodule.comapSubtypeEquivOfLe (colSpace_mono A S hv)
  have sizeT : Nat.card T = Nat.card J := Nat.card_congr e.toEquiv
  have ep : p.toAddMonoidHom.range = (I.map f).toAddSubgroup := by
    ext v
    exact ⟨fun ⟨⟨a,ha⟩,eq⟩ => ⟨a,ha,eq⟩,fun ⟨a,ha,eq⟩ => ⟨⟨a,ha⟩,eq⟩⟩
  have et : (p.toAddMonoidHom.comp T.toAddSubgroup.subtype).range = (J.map f).toAddSubgroup := by
    ext v
    exact ⟨fun ⟨⟨a,ha⟩,eq⟩ => ⟨a,ha,eq⟩,
      fun ⟨a,ha,eq⟩ => ⟨⟨⟨a,colSpace_mono A S hv ha⟩,ha⟩,eq⟩⟩
  have subcard : Nat.card (p.toAddMonoidHom.comp T.toAddSubgroup.subtype).range ≤ q := by
    rw [et]
    change Nat.card ((colSpace A S V).map (restrictRows hr)) ≤ q
    rw [map_colSpace]
    exact constant_card A R V t eq
  have b := strip_card_bound p.toAddMonoidHom T.toAddSubgroup q subcard
  rw [ep] at b
  change Nat.card ((colSpace A S U).map (restrictRows hr)) * Nat.card T ≤ q*Nat.card I at b
  rwa [map_colSpace,sizeT] at b

theorem strip_complexity (A : X → Y → ZMod q) {S R : Finset X} {U V : Finset Y}
    (hr : R ⊆ S) (hv : V ⊆ U) (t : ZMod q) (eq : ∀ x ∈ R, ∀ y ∈ V, A x y = t) :
    complexity A R U ≤ (complexity A S U + Real.log q)/2 ∨
    complexity A S V ≤ (complexity A S U + Real.log q)/2 := by
  have h := strip_product A hr hv t eq
  have pos (s : Finset X) (u : Finset Y) : (0:ℝ) < Nat.card (colSpace A s u) := by exact_mod_cast Nat.card_pos
  have qp : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hlog := Real.log_le_log (mul_pos (pos R U) (pos S V))
    (show (Nat.card (colSpace A R U):ℝ)*Nat.card (colSpace A S V) ≤ (q:ℝ)*Nat.card (colSpace A S U) by exact_mod_cast h)
  rw [Real.log_mul (pos R U).ne' (pos S V).ne',Real.log_mul qp.ne' (pos S U).ne'] at hlog
  unfold complexity
  by_contra! hn
  linarith

end InducedDegreeRepetition.Approximation
