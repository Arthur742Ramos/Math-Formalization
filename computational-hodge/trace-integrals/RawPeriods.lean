module
public import RawAnalysis
@[expose] public section

namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge

def unitCochain : Cochain Unit := WithLp.toLp 2 (fun _ => 1)
def unitTrace : Trace 0 0 := .single ()
noncomputable def meanCochain (α : Coefficient) : Cochain Unit := WithLp.toLp 2 (fun _ => mean α)

theorem period_mean_count (α : Coefficient) {a b : Circle} (p : Trace a b) :
    period p (meanCochain α)=mean α*(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change mean α=mean α*((1 : ℤ) : ℝ);rw [Int.cast_one,mul_one]
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add];ring
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg];ring

theorem period_unit_count {a b : Circle} (p : Trace a b) : period p unitCochain=(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change (1 : ℝ)=((1 : ℤ) : ℝ);norm_num
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add]
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg]

theorem count_zero_of_source_ne {a b : Circle} (p : Trace a b) : a≠0 → count p=0 := by
  induction p with
  | refl _ => exact fun _ => rfl
  | single _ => exact fun h => (h rfl).elim
  | trans p q hp hq =>
    intro h
    rw [count,hp h,hq (fun hb => h ((trace_endpoints p).trans hb)),zero_add]
  | symm p hp =>
    intro h
    rw [count,hp (fun ha => h ((trace_endpoints p).symm.trans ha)),neg_zero]

theorem count_homotopic {a b : Circle} (p q : Trace a b)
    (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) : count p=count q := by
  by_cases ha : a=0
  · subst a
    have hb := trace_endpoints p
    subst b
    have hw : (count p : ℝ)=(count q : ℝ) :=
      (winding_realize_count p).symm.trans ((winding_homotopic h).trans (winding_realize_count q))
    exact_mod_cast hw
  · rw [count_zero_of_source_ne p ha,count_zero_of_source_ne q ha]

theorem meanCochain_closed (α : Coefficient) : meanCochain α∈Closed (geometricPresentation circleSystem) := by
  change d1 (geometricPresentation circleSystem) (meanCochain α)=0
  funext c
  change period c.left (meanCochain α)-period c.right (meanCochain α)=0
  rw [period_mean_count,period_mean_count,count_homotopic c.left c.right c.rule,sub_self]

theorem circle_exact_eq_bot : Exact circleSystem=⊥ := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    change d0 circleSystem.toGeometricStepSystem f=0
    ext e
    exact sub_self (f 0)
  · exact bot_le

noncomputable def meanHarmonic (α : Coefficient) : Harmonic (geometricPresentation circleSystem) :=
  ⟨meanCochain α,meanCochain_closed α,
    by rw [circle_exact_eq_bot,Submodule.bot_orthogonal_eq_top];trivial⟩

theorem rawIntegral_period (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=mean α*period p unitCochain := by
  rw [rawIntegral_eq_mean_count,period_unit_count]

theorem rawIntegral_harmonic_period (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=period p (meanHarmonic α) := (rawIntegral_eq_mean_count α p).trans (period_mean_count α p).symm

theorem rawIntegral_unit (α : Coefficient) : rawIntegral α unitTrace=mean α := by
  rw [rawIntegral_eq_mean_count]
  simp only [unitTrace,count,Int.cast_one,mul_one]

theorem rawIntegral_refl (α : Coefficient) : rawIntegral α (.refl 0)=0 := by
  simp [rawIntegral_eq_mean_count,count]

theorem rawIntegral_trans (α : Coefficient) (p q : Trace 0 0) :
    rawIntegral α (p.trans q)=rawIntegral α p+rawIntegral α q := by
  simp only [rawIntegral_eq_mean_count,count,Int.cast_add];ring

theorem rawIntegral_symm (α : Coefficient) (p : Trace 0 0) : rawIntegral α p.symm= -rawIntegral α p := by
  simp only [rawIntegral_eq_mean_count,count,Int.cast_neg];ring

theorem rawIntegral_homotopic (α : Coefficient) {p q : Trace 0 0}
    (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) :
    rawIntegral α p=rawIntegral α q := by
  rw [rawIntegral_eq_mean_count,rawIntegral_eq_mean_count,count_homotopic p q h]

theorem rawIntegral_assoc (α : Coefficient) (p q r : Trace 0 0) :
    rawIntegral α ((p.trans q).trans r)=rawIntegral α (p.trans (q.trans r)) := by
  simp only [rawIntegral_trans];ring

theorem rawIntegral_cancel (α : Coefficient) (p : Trace 0 0) : rawIntegral α (p.trans p.symm)=0 := by
  rw [rawIntegral_trans,rawIntegral_symm,add_neg_cancel]

theorem all_raw_integrals_zero_iff_mean (α : Coefficient) :
    (∀ p : Trace 0 0,rawIntegral α p=0) ↔ mean α=0 := by
  constructor
  · intro h
    exact (rawIntegral_unit α).symm.trans (h unitTrace)
  · intro h p
    simp [rawIntegral_eq_mean_count,h]

theorem unique_harmonic_raw_periods (α : Coefficient) :
    ∃! h : Harmonic (geometricPresentation circleSystem),∀ p : Trace 0 0,rawIntegral α p=period p h := by
  refine ⟨meanHarmonic α,rawIntegral_harmonic_period α,?_⟩
  intro h hh
  apply Subtype.ext
  ext e
  cases e
  have hp := hh unitTrace
  have he : period unitTrace h=h.val () := rfl
  change h.val ()=mean α
  exact ((rawIntegral_unit α).symm.trans (hp.trans he)).symm

end ComputationalHodge.TraceIntegrals
