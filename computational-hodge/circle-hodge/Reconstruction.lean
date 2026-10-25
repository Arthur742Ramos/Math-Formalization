module
public import CircleWinding
@[expose] public section

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

/-- Algebraic real characters, with the ordinary pointwise vector-space structure. -/
def Characters (S : ContinuousGeometricStepSystem A E) (a : A) :
    Submodule ℝ (representedGroup S a → ℝ) where
  carrier f := f 1 = 0 ∧ ∀ x y, f (x*y) = f x + f y
  zero_mem' := ⟨rfl,fun _ _ => (add_zero _).symm⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨by change f 1 + g 1 = 0; rw [hf.1,hg.1,add_zero],
      fun x y => by change f (x*y)+g (x*y) = (f x+g x)+(f y+g y)
                    rw [hf.2,hg.2]; ring⟩
  smul_mem' := by
    intro r f hf
    exact ⟨by change r*f 1=0; rw [hf.1,mul_zero],
      fun x y => by change r*f (x*y)=r*f x+r*f y; rw [hf.2,mul_add]⟩

/-- These are exactly the usual group homomorphisms to the additive reals. -/
def characterEquivHom (a : A) :
    Characters S a ≃ (representedGroup S a →* Multiplicative ℝ) where
  toFun χ := { toFun := fun g => Multiplicative.ofAdd (χ.val g)
               map_one' := χ.property.1
               map_mul' := χ.property.2 }
  invFun f := ⟨fun g => (f g).toAdd,f.map_one,f.map_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem character_inv {a : A} (χ : Characters S a) (g : representedGroup S a) :
    χ.val g⁻¹ = -χ.val g := by
  have h := χ.property.2 g g⁻¹
  rw [mul_inv_cancel,χ.property.1] at h
  linarith

end ComputationalHodge.LoopCharacters

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E} {a : A}

def basedTrace (T : Rooting S a) {x y : A}
    (p : GeometricTrace S.toGeometricStepSystem x y) (hx : Active S a x)
    (hy : Active S a y) : GeometricTrace S.toGeometricStepSystem a a :=
  .trans (.trans (T.trace x hx) p) (.symm (T.trace y hy))

theorem based_refl (T : Rooting S a) {x : A} (hx : Active S a x) :
    representedLoop (basedTrace T (.refl x) hx hx) = 1 := by
  apply Subtype.ext
  change traceClass (basedTrace T (.refl x) hx hx) = _root_.Path.Homotopic.Quotient.refl a
  simp only [basedTrace,traceClass_trans,traceClass_refl,traceClass_symm]
  simp only [_root_.Path.Homotopic.Quotient.trans_refl,
    _root_.Path.Homotopic.Quotient.trans_symm]

theorem based_trans (T : Rooting S a) {x y z : A}
    (p : GeometricTrace S.toGeometricStepSystem x y)
    (q : GeometricTrace S.toGeometricStepSystem y z)
    (hx : Active S a x) (hy : Active S a y) (hz : Active S a z) :
    representedLoop (basedTrace T (.trans p q) hx hz) =
      representedLoop (basedTrace T q hy hz) * representedLoop (basedTrace T p hx hy) := by
  apply Subtype.ext
  change traceClass _ = (traceClass _).trans (traceClass _)
  simp only [basedTrace,traceClass_trans,traceClass_symm,
    _root_.Path.Homotopic.Quotient.trans_assoc]
  rw [← _root_.Path.Homotopic.Quotient.trans_assoc
    (traceClass (T.trace y hy)).symm (traceClass (T.trace y hy))]
  simp only [_root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.refl_trans]

theorem based_symm (T : Rooting S a) {x y : A}
    (p : GeometricTrace S.toGeometricStepSystem x y)
    (hx : Active S a x) (hy : Active S a y) :
    representedLoop (basedTrace T (.symm p) hy hx) =
      (representedLoop (basedTrace T p hx hy))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← based_trans T p (.symm p) hx hy hx]
  apply Subtype.ext
  change traceClass (basedTrace T (.trans p (.symm p)) hx hx) =
    _root_.Path.Homotopic.Quotient.refl a
  simp only [basedTrace,traceClass_trans,traceClass_symm,
    _root_.Path.Homotopic.Quotient.trans_symm,
    _root_.Path.Homotopic.Quotient.trans_refl]

variable [Fintype E]

/-- Recover edge coefficients from the character of actual rooted edge loops. -/
noncomputable def characterCochain (T : Rooting S a) (χ : Characters S a) : Cochain E :=
  WithLp.toLp 2 (fun e => χ.val (representedLoop
    (basedTrace T (.single e) (Or.inr ⟨e,Or.inl rfl⟩) (Or.inr ⟨e,Or.inr rfl⟩))))

theorem characterCochain_period (T : Rooting S a) (χ : Characters S a) {x y : A}
    (p : GeometricTrace S.toGeometricStepSystem x y)
    (hx : Active S a x) (hy : Active S a y) :
    period p (characterCochain T χ) = χ.val (representedLoop (basedTrace T p hx hy)) := by
  induction p with
  | refl x => rw [based_refl,χ.property.1]; rfl
  | single e => rfl
  | @trans x y z p q hp hq =>
    have hm := (active_endpoints p).mp hx
    change period p (characterCochain T χ) + period q (characterCochain T χ) = _
    rw [hp hx hm,hq hm hy,based_trans T p q hx hm hy,χ.property.2,add_comm]
  | symm p hp =>
    change -period p (characterCochain T χ) = _
    rw [hp hy hx,based_symm,character_inv]

theorem characterCochain_closed (T : Rooting S a) (χ : Characters S a) :
    characterCochain T χ ∈ Closed (geometricPresentation S) := by
  classical
  funext c
  change period c.left (characterCochain T χ) - period c.right (characterCochain T χ) = 0
  by_cases hx : Active S a c.src
  · have hy := (active_endpoints c.left).mp hx
    rw [characterCochain_period T χ c.left hx hy,characterCochain_period T χ c.right hx hy]
    apply sub_eq_zero.mpr
    apply congrArg χ.val
    apply Subtype.ext
    change traceClass (basedTrace T c.left hx hy) = traceClass (basedTrace T c.right hx hy)
    simp only [basedTrace,traceClass_trans,traceClass_symm]
    have hc : traceClass c.left = traceClass c.right := _root_.Path.Homotopic.Quotient.eq.mpr c.rule
    rw [hc]
  · rw [inactive_period_zero c.left hx,inactive_period_zero c.right hx,sub_self]

theorem characterCochain_loop (T : Rooting S a) (χ : Characters S a)
    (p : GeometricTrace S.toGeometricStepSystem a a) :
    period p (characterCochain T χ) = χ.val (representedLoop p) := by
  rw [characterCochain_period T χ p (Or.inl rfl) (Or.inl rfl)]
  apply congrArg χ.val
  apply Subtype.ext
  change traceClass (basedTrace T p (Or.inl rfl) (Or.inl rfl)) = traceClass p
  simp only [basedTrace,T.at_root,traceClass_trans,traceClass_refl,traceClass_symm,
    _root_.Path.Homotopic.Quotient.refl_trans]
  change (traceClass p).trans (_root_.Path.Homotopic.Quotient.refl a) = _
  exact _root_.Path.Homotopic.Quotient.trans_refl _

end ComputationalHodge.LoopCharacters
