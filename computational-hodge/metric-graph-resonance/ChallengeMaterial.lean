module
public import Challenge

public section

-- BEGIN material-imported-definition audit
-- Partial draft only: these examples do not constitute the complete inventory.
namespace MetricGraphMaterialDraft
open MeasureTheory Set Filter Asymptotics ENNReal
open scoped Topology Interval

example (X : Type*) : Set X = (X → Prop) := rfl

example : unitInterval = Set.Icc (0 : ℝ) 1 := rfl

example {X : Type*} [TopologicalSpace X] : IsOpen (Set.univ : Set X) := isOpen_univ

example {X : Type*} [TopologicalSpace X] (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := hs.inter ht

example {X : Type*} [TopologicalSpace X] (S : Set (Set X))
    (h : ∀ s ∈ S, IsOpen s) : IsOpen (⋃₀ S) := isOpen_sUnion h

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (s : Set X) :
    ContinuousOn f s ↔ ∀ x ∈ s, ContinuousWithinAt f s x := Iff.rfl

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : Continuous f) (s : Set Y) (hs : IsOpen s) :
    IsOpen (f ⁻¹' s) := h.isOpen_preimage s hs

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (s : Set X) (x : X) :
    ContinuousWithinAt f s x ↔ Tendsto f (𝓝[s] x) (𝓝 (f x)) := Iff.rfl

example {X Y : Type*} (f g : X → Y) (s : Set X) :
    Set.EqOn f g s ↔ ∀ x ∈ s, f x = g x := Iff.rfl

example {f : ℝ → ℝ} {x v : ℝ} :
    HasDerivAt f v x ↔ HasDerivAtFilter f v (nhds x ×ˢ pure x) := Iff.rfl

example {f : ℝ → ℝ} {v : ℝ} {L : Filter (ℝ × ℝ)} :
    HasDerivAtFilter f v L ↔
      HasFDerivAtFilter f (ContinuousLinearMap.toSpanSingleton ℝ v) L := Iff.rfl

example (f : ℝ → ℝ) (f' : ℝ →L[ℝ] ℝ) (L : Filter (ℝ × ℝ))
    (h : HasFDerivAtFilter f f' L) :
    (fun p : ℝ × ℝ => f p.1 - f p.2 - f' (p.1 - p.2)) =o[ℝ; L]
      (fun p : ℝ × ℝ => p.1 - p.2) := h.isLittleOTVS

example {f : ℝ → ℝ} {a b : ℝ} :
    IntervalIntegrable f volume a b ↔
      IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl

example (f : ℝ → ℝ) (s : Set ℝ) (μ : Measure ℝ) :
    IntegrableOn f s μ ↔ Integrable f (μ.restrict s) := Iff.rfl

example (f : ℝ → ℝ) (μ : Measure ℝ) :
    Integrable f μ ↔ AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ := Iff.rfl

example (f : ℝ → ℝ) (a b : ℝ) :
    intervalIntegral f a b volume =
      (∫ x in Ioc a b, f x ∂volume) - ∫ x in Ioc b a, f x ∂volume := rfl

open Classical in
example (μ : Measure ℝ) (f : ℝ → ℝ) : MeasureTheory.integral μ f =
    if _ : CompleteSpace ℝ then
      if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
    else 0 := MeasureTheory.integral_def μ f

theorem real_volume_contract : (volume : Measure ℝ) = StieltjesFunction.id.measure :=
  Real.volume_eq_stieltjes_id

theorem ae_real_volume_contract (P : ℝ → Prop) :
    (∀ᵐ x : ℝ ∂volume, P x) ↔ volume {x | ¬ P x} = 0 := MeasureTheory.ae_iff

theorem derivative_normed_little_o_contract (f : ℝ → ℝ) (f' : ℝ →L[ℝ] ℝ)
    (L : Filter (ℝ × ℝ)) : HasFDerivAtFilter f f' L ↔
      (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[L] (fun p => p.1 - p.2) :=
  hasFDerivAtFilter_iff_isLittleO

theorem little_o_eventual_bound_contract (f g : ℝ → ℝ) (L : Filter ℝ) :
    f =o[L] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in L, ‖f x‖ ≤ c * ‖g x‖ :=
  isLittleO_iff

theorem ae_strongly_measurable_contract (f : ℝ → ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable f μ ↔ ∃ g : ℝ → ℝ, StronglyMeasurable g ∧ f =ᵐ[μ] g := Iff.rfl

theorem finite_integral_contract (f : ℝ → ℝ) (μ : Measure ℝ) :
    HasFiniteIntegral f μ ↔ (∫⁻ x, ‖f x‖ₑ ∂μ) < ∞ := Iff.rfl

theorem real_volume_ioc_contract (a b : ℝ) :
    volume (Ioc a b) = ENNReal.ofReal (b - a) := Real.volume_Ioc

example {α : Type*} (l : Filter α) (P : α → Prop) :
    (∀ᶠ x in l, P x) ↔ {x | P x} ∈ l := Iff.rfl

example : (volume : Measure ℝ) = (MeasureSpace.volume : Measure ℝ) := rfl

example (x : ℝ) : Irrational x ↔ x ∉ Set.range ((↑) : ℚ → ℝ) := Iff.rfl

example {a b x : ℝ} : x ∈ Ioo a b ↔ a < x ∧ x < b := Iff.rfl

example {a b x : ℝ} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl

example {a b x : ℝ} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := Iff.rfl

example {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (x : ℝ) (hx : x ≤ 1 / 2) :
    (p.trans q).extend x = p.extend (2 * x) :=
  Path.extend_trans_of_le_half p q hx

example {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (x : ℝ) (hx : 1 / 2 ≤ x) :
    (p.trans q).extend x = q.extend (2 * x - 1) :=
  Path.extend_trans_of_half_le p q hx

example {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (x : ℝ) :
    p.symm.extend x = p.extend (1 - x) := Path.extend_symm_apply p x

example {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    p.extend x = p ⟨x, hx⟩ := Path.extend_apply p hx

example {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (x : ℝ) (hx : x ≤ 0) : p.extend x = a :=
  Path.extend_of_le_zero p hx

example {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a b) (x : ℝ) (hx : 1 ≤ x) : p.extend x = b :=
  Path.extend_of_one_le p hx

example {X : Type*} [TopologicalSpace X] {a b : X} (p : Path a b) :
    p 0 = a ∧ p 1 = b := ⟨p.source, p.target⟩

example {X : Type*} [TopologicalSpace X] (a : X) (t : Set.Icc (0 : ℝ) 1) :
    (Path.refl a) t = a := rfl

theorem generated_sum_contract {α : Type*} (s : Finset α) (f : α → ℝ) :
    s.sum f = (s.val.map f).sum := rfl

example {α : Type*} [Fintype α] (a : α) : a ∈ (Finset.univ : Finset α) :=
  Finset.mem_univ a

theorem finite_univ_sum_contract {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ a : α, f a) = Finset.univ.sum f := rfl

-- Independently elaborate the named contracts at the intended types.
example {α : Type*} (s : Finset α) (f : α → ℝ) :
    s.sum f = (s.val.map f).sum := generated_sum_contract s f
example {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ a : α, f a) = Finset.univ.sum f := finite_univ_sum_contract f
example : (volume : Measure ℝ) = StieltjesFunction.id.measure := real_volume_contract
example (P : ℝ → Prop) : (∀ᵐ x : ℝ ∂volume, P x) ↔ volume {x | ¬ P x} = 0 :=
  ae_real_volume_contract P
#print axioms generated_sum_contract
#print axioms finite_univ_sum_contract
#print axioms real_volume_contract
#print axioms ae_real_volume_contract
#print axioms derivative_normed_little_o_contract
#print axioms little_o_eventual_bound_contract
#print axioms ae_strongly_measurable_contract
#print axioms finite_integral_contract
#print axioms real_volume_ioc_contract

example (f : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ)) (a b : ℝ → ℝ) :
    f (a + b) = f a + f b := map_add f a b

example (x : ℝ) : Real.sin x = (Complex.sin (x : ℂ)).re := rfl
example (x : ℝ) : Real.cos x = (Complex.cos (x : ℂ)).re := rfl
example : Real.pi = 2 * Classical.choose Real.exists_cos_eq_zero := rfl

example {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : MetricGraphResonanceIncidence.Network V E) (b : E → ℝ) (v : V) :
    MetricGraphResonanceIncidence.divergence G b v =
      (∑ e : E, if G.source e = v then b e else 0) -
      (∑ e : E, if G.target e = v then b e else 0) := rfl

example {V E : Type*} [TopologicalSpace V] [TopologicalSpace E]
    (source target : E → V) (e : E) :
    MetricGraphPathPrototype.edgePoint source target e 0 =
      MetricGraphPathPrototype.vertex source target (source e) :=
  MetricGraphPathPrototype.edgePoint_zero source target e

example {V E : Type*} [TopologicalSpace V] [TopologicalSpace E]
    (source target : E → V) (e : E) :
    MetricGraphPathPrototype.edgePoint source target e 1 =
      MetricGraphPathPrototype.vertex source target (target e) :=
  MetricGraphPathPrototype.edgePoint_one source target e

example {V E : Type*} [Fintype E] [DecidableEq V]
    (source target : E → V) (f : E → ℝ → ℝ) (k : ℝ) :
    MetricGraphResonancePrototype.intervalGraphSolution source target f k ↔
      ∃ u q : E → ℝ → ℝ, ∃ vertex : V → ℝ,
        (∀ e, ContinuousOn (u e) (Icc 0 1)) ∧
        (∀ e, ContinuousOn (q e) (Icc 0 1)) ∧
        (∀ e x, x ∈ Ioo 0 1 → HasDerivAt (u e) (q e x) x) ∧
        (∀ e x, x ∈ Ioo 0 1 → HasDerivAt (q e) (-(k ^ 2 * u e x + f e x)) x) ∧
        (∀ e, u e 0 = vertex (source e) ∧ u e 1 = vertex (target e)) ∧
        ∀ v, (∑ e, if source e = v then q e 0 else 0) -
          (∑ e, if target e = v then q e 1 else 0) = 0 := Iff.rfl

example {V E : Type*} [Fintype E] (source target : E → V) (f : E → ℝ → ℝ) (k : ℝ) :
    MetricGraphResonancePrototype.graphMomentConditions source target f k ↔
      ((∑ e, ∫ t in (0 : ℝ)..1, f e t * Real.cos (k * t)) = 0 ∧
        ∃ p : V → ℝ, ∀ e, (∫ t in (0 : ℝ)..1, f e t * Real.sin (k * t)) =
          p (target e) - p (source e)) := Iff.rfl

example {α : Type*} (r : α → α → Prop) (a b : α) (h : r a b) :
    Relation.EqvGen r a b := Relation.EqvGen.rel a b h

example {α : Type*} (r : α → α → Prop) (a : α) :
    Relation.EqvGen r a a := Relation.EqvGen.refl a

example {α : Type*} (r : α → α → Prop) (a b : α)
    (h : Relation.EqvGen r a b) : Relation.EqvGen r b a :=
  Relation.EqvGen.symm a b h

example {α : Type*} (r : α → α → Prop) (a b c : α)
    (h₁ : Relation.EqvGen r a b) (h₂ : Relation.EqvGen r b c) :
    Relation.EqvGen r a c := Relation.EqvGen.trans a b c h₁ h₂

example {α : Type*} (r P : α → α → Prop)
    (hrel : ∀ a b, r a b → P a b)
    (hrefl : ∀ a, P a a)
    (hsymm : ∀ a b, P a b → P b a)
    (htrans : ∀ a b c, P a b → P b c → P a c) :
    ∀ a b, Relation.EqvGen r a b → P a b := by
  intro a b h
  induction h with
  | rel a b hab => exact hrel a b hab
  | refl a => exact hrefl a
  | symm a b _ ih => exact hsymm a b ih
  | trans a b c _ _ ih₁ ih₂ => exact htrans a b c ih₁ ih₂

end MetricGraphMaterialDraft
-- END material-imported-definition audit
