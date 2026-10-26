module
public import CircleData
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.MetricSpace.Lipschitz
@[expose] public section

namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open scoped NNReal Topology unitInterval

abbrev Trace (a b : CircleHodge.Circle) := GeometricTrace circleSystem.toGeometricStepSystem a b

def count {a b : CircleHodge.Circle} : Trace a b → ℤ
  | .refl _ => 0
  | .single _ => 1
  | .trans p q => count p+count q
  | .symm p => -count p

def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

/-- A finite piecewise-affine construction from the actual trace syntax.
Equality with the actual covering lift is proved separately. -/
noncomputable def rawLift {a b : CircleHodge.Circle} : Trace a b → ℝ → ℝ
  | .refl _ => fun _ => 0
  | .single _ => clamp
  | .trans p q => fun t => if t≤1/2 then rawLift p (2*t)
      else rawLift p 1+rawLift q (2*t-1)
  | .symm p => fun t => rawLift p (1-t)-rawLift p 1

theorem trace_endpoints {a b : CircleHodge.Circle} (p : Trace a b) : a=b := by induction p <;> aesop

theorem rawLift_zero {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 0=0 := by induction p <;> simp_all [rawLift,clamp]

theorem rawLift_one {a b : CircleHodge.Circle} (p : Trace a b) : rawLift p 1=(count p : ℝ) := by
  induction p <;> simp_all [rawLift,count,clamp,rawLift_zero]; norm_num; assumption

theorem cut_lipschitz {f g : ℝ → ℝ} {K L : ℝ≥0} {c : ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) (hc : f c=g c) :
    LipschitzWith (K+L) (fun x => if x≤c then f x else g x) := by
  have hh : LipschitzWith (K+L) (fun x => f (min c x)+g (max c x)-f c) := by
    simpa only [Function.comp_def,id_eq,mul_one,one_mul,sub_eq_add_neg] using (isometry_add_right (-f c)).lipschitzWith.comp
      ((hf.comp (LipschitzWith.id.const_min c)).add (hg.comp (LipschitzWith.id.const_max c)))
  convert hh using 1
  funext x
  split_ifs with hx
  · simp only [min_eq_right hx,max_eq_left hx,hc,add_sub_cancel_right]
  · simp only [min_eq_left (not_le.mp hx).le,max_eq_right (not_le.mp hx).le,add_sub_cancel_left]

theorem affine_lipschitz (a b : ℝ) : LipschitzWith ‖a‖₊ (fun x : ℝ => a*x+b) := by simpa only [Function.comp_def,smul_eq_mul,one_mul] using (isometry_add_right b).lipschitzWith.comp (lipschitzWith_smul a)

theorem shift_lipschitz {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (c : ℝ) :
    LipschitzWith K (fun x => c+f x) := by simpa only [Function.comp_def,one_mul] using (isometry_add_left c).lipschitzWith.comp hf

theorem rawLift_lipschitz {a b : CircleHodge.Circle} (p : Trace a b) :
    ∃ K : ℝ≥0,LipschitzWith K (rawLift p) := by
  induction p with
  | refl _ => exact ⟨0,LipschitzWith.const 0⟩
  | single _ => exact ⟨1,(LipschitzWith.id.const_min 1).const_max 0⟩
  | trans p q hp hq => exact hp.elim (fun K hK => hq.elim (fun L hL => ⟨K*‖(2:ℝ)‖₊+L*‖(2:ℝ)‖₊,
      cut_lipschitz (by simpa only [Function.comp_def,add_zero] using hK.comp (affine_lipschitz 2 0))
        (shift_lipschitz (by simpa only [Function.comp_def,sub_eq_add_neg] using hL.comp (affine_lipschitz 2 (-1))) (rawLift p 1)) (by norm_num [rawLift_zero])⟩))
  | symm p hp => exact hp.elim (fun K hK => ⟨K*‖(-1:ℝ)‖₊,by
      change LipschitzWith (K*‖(-1:ℝ)‖₊) (fun x => rawLift p (1-x)-rawLift p 1)
      simpa only [sub_eq_add_neg,add_comm,Function.comp_def,neg_one_mul] using
        shift_lipschitz (hK.comp (affine_lipschitz (-1) 1)) (-rawLift p 1)⟩)

theorem rawLift_continuous {a b : CircleHodge.Circle} (p : Trace a b) : Continuous (rawLift p) := (rawLift_lipschitz p).choose_spec.continuous

theorem rawLift_one_coe {a b : CircleHodge.Circle} (p : Trace a b) : ((rawLift p 1 : ℝ) : CircleHodge.Circle)=0 := (congrArg (fun x : ℝ => (x : CircleHodge.Circle)) (rawLift_one p)).trans
  ((AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨count p,by simp⟩)

theorem rawLift_projects {a b : CircleHodge.Circle} (p : Trace a b) (t : unitInterval) :
    ((rawLift p (t : ℝ) : ℝ) : CircleHodge.Circle)+a=GeometricTrace.realize p t := by
  induction p generalizing t with
  | refl a => simp [rawLift,GeometricTrace.realize]
  | single e =>
    change ((clamp (t : ℝ) : ℝ) : CircleHodge.Circle)+0=((t : ℝ) : CircleHodge.Circle)
    simp [clamp,min_eq_right t.2.2,max_eq_right t.2.1]
  | trans p q hp hq =>
    rw [GeometricTrace.realize,_root_.Path.trans_apply]
    simp only [rawLift]
    split_ifs with h
    · exact hp ⟨2*t,⟨by linarith [t.2.1],by linarith⟩⟩
    · simpa only [AddCircle.coe_add,rawLift_one_coe,zero_add,trace_endpoints p] using hq ⟨2*t-1,⟨by linarith [not_le.mp h],by linarith [t.2.2]⟩⟩
  | symm p hp =>
    simpa only [rawLift,GeometricTrace.realize,_root_.Path.symm_apply,Function.comp_apply,unitInterval.coe_symm_eq,AddCircle.coe_sub,rawLift_one_coe,sub_zero,trace_endpoints p] using hp (σ t)

theorem rawLift_outside {a b : CircleHodge.Circle} (p : Trace a b) :
    ∀ t : ℝ,(t≤0 → rawLift p t=0) ∧ (1≤t → rawLift p t=rawLift p 1) := by
  induction p <;> intro t <;> constructor <;> intro ht
  all_goals simp only [rawLift,clamp,min_def,max_def] at *
  all_goals grind [rawLift_zero]

theorem rawLift_clamp {a b : CircleHodge.Circle} (p : Trace a b) (t : ℝ) :
    rawLift p (Set.projIcc 0 1 zero_le_one t : ℝ)=rawLift p t := by
  by_cases h0 : t≤0
  · rw [Set.projIcc_of_le_left zero_le_one h0]
    exact (rawLift_zero p).trans ((rawLift_outside p t).1 h0).symm
  by_cases h1 : 1≤t
  · rw [Set.projIcc_of_right_le zero_le_one h1]
    exact ((rawLift_outside p t).2 h1).symm
  rw [Set.projIcc_of_mem zero_le_one ⟨(not_le.mp h0).le,(not_le.mp h1).le⟩]

/-- The actual covering lift of the actual path, extended by the interval projection. -/
noncomputable def actualLift (p : Trace 0 0) (t : ℝ) : ℝ :=
  circleLift (GeometricTrace.realize p) (Set.projIcc 0 1 zero_le_one t)

theorem rawLift_eq_cover (p : Trace 0 0) (t : unitInterval) :
    rawLift p (t : ℝ)=circleLift (GeometricTrace.realize p) t := congrArg (fun f : C(unitInterval,ℝ) => f t)
  (show (⟨fun t : unitInterval => rawLift p (t : ℝ),(rawLift_continuous p).comp continuous_subtype_val⟩ : C(unitInterval,ℝ))=circleLift (GeometricTrace.realize p) from
    (circleCover.eq_liftPath_iff' _).mpr ⟨funext (fun u => by simpa using rawLift_projects p u),rawLift_zero p⟩)

theorem actualLift_eq_rawLift (p : Trace 0 0) : actualLift p=rawLift p := funext fun t => (rawLift_eq_cover p (Set.projIcc 0 1 zero_le_one t)).symm.trans (rawLift_clamp p t)

end ComputationalHodge.TraceIntegrals
