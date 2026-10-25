module
public import CircleWinding
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.Analysis.Convex.Contractible
@[expose] public section

namespace ComputationalHodge.TorusPeriods
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters

theorem circle_winding_injective : Function.Injective windingCharacter := by
  let hp := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  let e : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} := ⟨0,by simp⟩
  intro g h hh
  apply hp.monodromyPerm_injective
  apply Equiv.ext
  have hm : hp.isCoveringMap.monodromy g e = hp.isCoveringMap.monodromy h e := by
    apply Subtype.ext
    induction g using Quotient.inductionOn with | _ p =>
    induction h using Quotient.inductionOn with | _ q =>
    exact congrArg Multiplicative.toAdd hh
  exact congrFun ((hp.monodromy_ext_iff e).mp hm)

theorem circle_winding_integral (g : FundamentalGroup (AddCircle (1 : ℝ)) 0) :
    ∃ n : ℤ, (n : ℝ) = (windingCharacter g).toAdd := by
  induction g using Quotient.inductionOn with | _ p =>
  have h : ((winding p : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (congrFun (circleCover.liftPath_lifts p.toContinuousMap 0 (by simp)) 1).trans p.target
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h
  refine ⟨n,?_⟩
  change (n : ℝ) = winding p
  simpa using hn

abbrev Torus (E : Type) := E → AddCircle (1 : ℝ)

variable {E : Type} [finiteE : Fintype E] [topE : TopologicalSpace E]
  [discreteE : DiscreteTopology E] [decidableE : DecidableEq E]

noncomputable def coordinateLoop (e : E) : _root_.Path (0 : Torus E) 0 where
  toFun t j := if j=e then ((t : ℝ) : AddCircle (1 : ℝ)) else 0
  continuous_toFun := by
    exact continuous_pi (fun j => by
    by_cases h : j=e
    · simp only [h,ite_true]
      fun_prop
    · simpa only [h,ite_false] using (continuous_const : Continuous (fun _ : unitInterval => (0 : AddCircle (1 : ℝ)))))
  source' := by
    funext j
    simp
  target' := by
    funext j
    simp

noncomputable def torusSystem (E : Type) [Fintype E] [TopologicalSpace E] [DiscreteTopology E] [DecidableEq E] :
    ContinuousGeometricStepSystem (Torus E) E where
  src _ := 0
  tgt _ := 0
  realize := coordinateLoop
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

noncomputable def coordinateMap (e : E) :
    FundamentalGroup (Torus E) 0 →* FundamentalGroup (AddCircle (1 : ℝ)) 0 :=
  FundamentalGroup.map ⟨fun x : Torus E => x e,continuous_apply e⟩ (0 : Torus E)

noncomputable def windingVector (g : FundamentalGroup (Torus E) 0) (e : E) : ℝ :=
  (windingCharacter (coordinateMap e g)).toAdd

omit finiteE topE discreteE decidableE in
theorem windingVector_mul (g h : FundamentalGroup (Torus E) 0) (e : E) :
    windingVector (g*h) e = windingVector g e + windingVector h e := by
  unfold windingVector
  rw [map_mul,map_mul]
  rfl

omit finiteE topE discreteE decidableE in
theorem windingVector_inv (g : FundamentalGroup (Torus E) 0) (e : E) :
    windingVector g⁻¹ e = -windingVector g e := by
  unfold windingVector
  rw [map_inv,map_inv]
  rfl

omit finiteE topE discreteE decidableE in
theorem windingVector_one (e : E) : windingVector (1 : FundamentalGroup (Torus E) 0) e = 0 := by
  unfold windingVector
  rw [map_one,map_one]
  rfl

omit finiteE topE discreteE decidableE in
theorem windingVector_injective : Function.Injective (windingVector (E := E)) := by
  intro g h heq
  have hc : (fun e => _root_.Path.Homotopic.proj e g) = fun e => _root_.Path.Homotopic.proj e h := by
    funext e
    apply circle_winding_injective
    exact Multiplicative.toAdd.injective (congrFun heq e)
  exact (_root_.Path.Homotopic.pi_proj g).symm.trans
    ((congrArg _root_.Path.Homotopic.pi hc).trans (_root_.Path.Homotopic.pi_proj h))

theorem coordinate_winding (i j : E) :
    windingVector (traceClass (S := torusSystem E) (.single i)) j = if i=j then 1 else 0 := by
  classical
  have h : (coordinateLoop i).map (continuous_apply j) =
      (if i=j then onceAround else _root_.Path.refl 0) := by
    by_cases hij : i=j
    · subst j
      ext t
      simp [coordinateLoop,onceAround]
      rfl
    · ext t; simp [coordinateLoop,hij,Ne.symm hij]
  change (windingCharacter (_root_.Path.Homotopic.Quotient.mk
    ((coordinateLoop i).map (continuous_apply j)))).toAdd = _
  rw [h]
  split_ifs
  · exact winding_onceAround
  · exact winding_refl

end ComputationalHodge.TorusPeriods
