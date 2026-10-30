module
import ChallengeMaterial

open MeasureTheory
open MetricGraphMaterialDraft

example {α : Type*} (s : Finset α) (f : α → ℝ) :
    s.sum f = (s.val.map f).sum := generated_sum_contract s f
example {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ a : α, f a) = Finset.univ.sum f := finite_univ_sum_contract f
example : (volume : Measure ℝ) = StieltjesFunction.id.measure := real_volume_contract
example (P : ℝ → Prop) : (∀ᵐ x : ℝ ∂volume, P x) ↔ volume {x | ¬ P x} = 0 :=
  ae_real_volume_contract P

#print axioms MetricGraphMaterialDraft.generated_sum_contract
#print axioms MetricGraphMaterialDraft.finite_univ_sum_contract
#print axioms MetricGraphMaterialDraft.real_volume_contract
#print axioms MetricGraphMaterialDraft.ae_real_volume_contract
