module
import SolutionMaterial

open MeasureTheory ENNReal
open Set Filter Asymptotics
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
example (f g : ℝ → ℝ) (L : Filter ℝ) :
    f =o[L] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in L, ‖f x‖ ≤ c * ‖g x‖ :=
  little_o_eventual_bound_contract f g L
example (f : ℝ → ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable f μ ↔ ∃ g : ℝ → ℝ, StronglyMeasurable g ∧ f =ᵐ[μ] g :=
  ae_strongly_measurable_contract f μ
example (f : ℝ → ℝ) (μ : Measure ℝ) : HasFiniteIntegral f μ ↔ (∫⁻ x, ‖f x‖ₑ ∂μ) < ∞ :=
  finite_integral_contract f μ
example (a b : ℝ) : volume (Ioc a b) = ENNReal.ofReal (b - a) := real_volume_ioc_contract a b

#print axioms MetricGraphMaterialDraft.generated_sum_contract
#print axioms MetricGraphMaterialDraft.finite_univ_sum_contract
#print axioms MetricGraphMaterialDraft.real_volume_contract
#print axioms MetricGraphMaterialDraft.ae_real_volume_contract
#print axioms MetricGraphMaterialDraft.derivative_normed_little_o_contract
#print axioms MetricGraphMaterialDraft.little_o_eventual_bound_contract
#print axioms MetricGraphMaterialDraft.ae_strongly_measurable_contract
#print axioms MetricGraphMaterialDraft.finite_integral_contract
#print axioms MetricGraphMaterialDraft.real_volume_ioc_contract
