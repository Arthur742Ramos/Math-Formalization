module
import ChallengeMaterial

public section

open MeasureTheory ENNReal
open Set Filter Asymptotics
open scoped Topology
open MetricGraphMaterialDraft

example {α : Type*} (s : Finset α) (f : α → ℝ) :
    s.sum f = (s.val.map f).sum := generated_sum_contract s f
example {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ a : α, f a) = Finset.univ.sum f := finite_univ_sum_contract f
example : (volume : Measure ℝ) = StieltjesFunction.id.measure := real_volume_contract
example (P : ℝ → Prop) : (∀ᵐ x : ℝ ∂volume, P x) ↔ volume {x | ¬ P x} = 0 :=
  ae_real_volume_contract P
example (f : ℝ → ℝ) (f' : ℝ →L[ℝ] ℝ) (L : Filter (ℝ × ℝ)) :
    HasFDerivAtFilter f f' L ↔
      (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) =o[L] (fun p => p.1 - p.2) :=
  derivative_normed_little_o_contract f f' L
example {α : Type*} (f g : α → ℝ) (L : Filter α) :
    f =o[L] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in L, ‖f x‖ ≤ c * ‖g x‖ :=
  little_o_eventual_bound_contract f g L
example (f : ℝ → ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable f μ ↔ ∃ g : ℝ → ℝ, StronglyMeasurable g ∧ f =ᵐ[μ] g :=
  ae_strongly_measurable_contract f μ
example (f : ℝ → ℝ) (μ : Measure ℝ) : HasFiniteIntegral f μ ↔ (∫⁻ x, ‖f x‖ₑ ∂μ) < ∞ :=
  finite_integral_contract f μ
example (a b : ℝ) : volume (Ioc a b) = ENNReal.ofReal (b - a) := real_volume_ioc_contract a b


example (μ : Measure ℝ) (P : ℝ → Prop) :
    (∀ᵐ x : ℝ ∂μ, P x) ↔ μ {x | ¬ P x} = 0 := ae_measure_null_contract μ P
theorem MetricGraphMaterialImporterCheck.restricted_ae_instance (a b : ℝ) (P : ℝ → Prop) :
    (∀ᵐ x : ℝ ∂(volume.restrict (Ioc a b)), P x) ↔
      (volume.restrict (Ioc a b)) {x | ¬ P x} = 0 :=
  ae_measure_null_contract (volume.restrict (Ioc a b)) P
theorem MetricGraphMaterialImporterCheck.pair_filter_composition (f : ℝ → ℝ) (f' : ℝ →L[ℝ] ℝ) (L : Filter (ℝ × ℝ)) :
    HasFDerivAtFilter f f' L ↔
      ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ p in L,
        ‖f p.1 - f p.2 - f' (p.1 - p.2)‖ ≤ c * ‖p.1 - p.2‖ :=
  (derivative_normed_little_o_contract f f' L).trans
    (little_o_eventual_bound_contract (fun p => f p.1 - f p.2 - f' (p.1 - p.2))
      (fun p => p.1 - p.2) L)
example {α β : Type*} (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ l₁.map f ≤ l₂ := filter_tendsto_contract f l₁ l₂
example {α β : Type*} (f : α → β) (l : Filter α) (s : Set β) :
    s ∈ l.map f ↔ f ⁻¹' s ∈ l := filter_map_membership_contract f l s
example {α β : Type*} (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ := filter_tendsto_preimage_contract f l₁ l₂
example {α : Type*} [TopologicalSpace α] (x : α) (s : Set α) :
    𝓝[s] x = 𝓝 x ⊓ 𝓟 s := nhds_within_contract x s
example {α : Type*} [TopologicalSpace α] (x : α) :
    𝓝 x = ⨅ s ∈ {s : Set α | x ∈ s ∧ IsOpen s}, 𝓟 s := nhds_open_sets_contract x
example {α : Type*} [TopologicalSpace α] (x : α) (s : Set α) :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := mem_nhds_open_contract x s
theorem MetricGraphMaterialImporterCheck.derivative_at_nhds_instance (f : ℝ → ℝ) (v x : ℝ) (s : Set ℝ) :
    (HasDerivAt f v x ↔ HasDerivAtFilter f v (𝓝 x ×ˢ pure x)) ∧
      (s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t) := derivative_at_nhds_contract f v x s
example {α : Type*} [TopologicalSpace α] (r : α → α → Prop) :
    Continuous (@Quot.mk α r) := quotient_map_continuity_contract r
example {α : Type*} [TopologicalSpace α] (r : α → α → Prop) :
    (inferInstance : TopologicalSpace (Quot r)) = TopologicalSpace.coinduced (Quot.mk r) inferInstance :=
  quotient_topology_contract r
example {V E : Type*} [TopologicalSpace V] [TopologicalSpace E] (source target : E → V) :
    (inferInstance : TopologicalSpace (MetricGraphPathPrototype.Graph source target)) =
      TopologicalSpace.coinduced (Quot.mk (MetricGraphPathPrototype.EdgeGlue source target)) inferInstance :=
  graph_quotient_topology_contract source target
example (z : ℂ) : Complex.sin z = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 :=
  complex_sine_contract z
example (z : ℂ) : Complex.cos z = (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2 :=
  complex_cosine_contract z

#print axioms MetricGraphMaterialDraft.ae_measure_null_contract
#print axioms MetricGraphMaterialDraft.filter_tendsto_contract
#print axioms MetricGraphMaterialDraft.filter_map_membership_contract
#print axioms MetricGraphMaterialDraft.filter_tendsto_preimage_contract
#print axioms MetricGraphMaterialDraft.nhds_within_contract
#print axioms MetricGraphMaterialDraft.nhds_open_sets_contract
#print axioms MetricGraphMaterialDraft.mem_nhds_open_contract
#print axioms MetricGraphMaterialDraft.derivative_at_nhds_contract
#print axioms MetricGraphMaterialDraft.quotient_map_continuity_contract
#print axioms MetricGraphMaterialDraft.quotient_topology_contract
#print axioms MetricGraphMaterialDraft.graph_quotient_topology_contract
#print axioms MetricGraphMaterialDraft.complex_sine_contract
#print axioms MetricGraphMaterialDraft.complex_cosine_contract
#print axioms MetricGraphMaterialImporterCheck.restricted_ae_instance
#print axioms MetricGraphMaterialImporterCheck.pair_filter_composition
#print axioms MetricGraphMaterialImporterCheck.derivative_at_nhds_instance
#print axioms MetricGraphMaterialDraft.generated_sum_contract
#print axioms MetricGraphMaterialDraft.finite_univ_sum_contract
#print axioms MetricGraphMaterialDraft.real_volume_contract
#print axioms MetricGraphMaterialDraft.ae_real_volume_contract
#print axioms MetricGraphMaterialDraft.derivative_normed_little_o_contract
#print axioms MetricGraphMaterialDraft.little_o_eventual_bound_contract
#print axioms MetricGraphMaterialDraft.ae_strongly_measurable_contract
#print axioms MetricGraphMaterialDraft.finite_integral_contract
#print axioms MetricGraphMaterialDraft.real_volume_ioc_contract
