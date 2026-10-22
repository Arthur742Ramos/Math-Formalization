module
public import SECChallenge

public section

-- BEGIN material-imported-definition audit
namespace SECChallengeDefinitions
open scoped BigOperators NNReal

theorem interval_literal (a b x : ℝ) : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl

theorem finite_enumeration {ι : Type*} [Fintype ι] (i : ι) : i ∈ (Fintype.elems : Finset ι) :=
  Fintype.complete i

theorem no_duplicate_indices {ι : Type*} (s : Finset ι) : s.val.Nodup := s.nodup

theorem finite_sum_literal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) = (s.val.map f).sum := rfl

theorem finite_product_literal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    s.prod f = (s.val.map f).prod := rfl

theorem natural_ceiling_literal (a : ℝ) : Nat.ceil a = FloorSemiring.ceil a := rfl

theorem real_sqrt_literal (a : ℝ) :
    Real.sqrt a = (NNReal.sqrt (Real.toNNReal a) : ℝ) := by unfold Real.sqrt; rfl

theorem nonnegative_sqrt_literal :
    NNReal.sqrt = (NNReal.powOrderIso 2 two_ne_zero : ℝ≥0 ≃o ℝ≥0).symm := rfl

theorem clip_nonnegative_literal (a : ℝ) : (Real.toNNReal a : ℝ) = max a 0 := rfl

theorem natural_ceiling_meaning (a : ℝ) (n : ℕ) : Nat.ceil a ≤ n ↔ a ≤ (n:ℝ) :=
  Nat.ceil_le

theorem square_root_meaning (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ Real.sqrt a ∧ Real.sqrt a ^ 2 = a := ⟨Real.sqrt_nonneg a, Real.sq_sqrt ha⟩

theorem finite_card_literal {ι : Type*} (s : Finset ι) : s.card = s.val.card := rfl

theorem type_card_literal (ι : Type*) [Fintype ι] : Fintype.card ι = (Finset.univ : Finset ι).card := rfl

theorem convex_literal {ν : Type} (s : Set (ν → ℝ)) : Convex ℝ s ↔
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 → a • x+b • y ∈ s := Iff.rfl

theorem convex_hull_meaning {ν : Type} (s : Set (ν → ℝ)) (x : ν → ℝ) :
    x ∈ convexHull ℝ s ↔ ∀ t, s ⊆ t → Convex ℝ t → x ∈ t := mem_convexHull_iff

theorem affine_independence_literal {ι ν : Type*} (p : ι → ν → ℝ) :
    AffineIndependent ℝ p ↔ ∀ (s : Finset ι) (w : ι → ℝ),
      (∑ i ∈ s, w i) = 0 → s.weightedVSub p w = (0 : ν → ℝ) → ∀ i ∈ s, w i = 0 := Iff.rfl

theorem weighted_subtraction_zero_sum {ι ν : Type*} (s : Finset ι) (p : ι → ν → ℝ)
    (w : ι → ℝ) (hw : ∑ i ∈ s, w i = 0) :
    s.weightedVSub p w = ∑ i ∈ s, w i • p i := by
  rw [s.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero w p hw 0]
  simp only [Finset.weightedVSubOfPoint_apply, vsub_eq_sub, sub_zero]

theorem vector_span_literal {ν : Type} (s : Set (ν → ℝ)) :
    vectorSpan ℝ s = Submodule.span ℝ (Set.image2 (fun a b => a-b) s s) := rfl

theorem submodule_span_literal {ν : Type} (s : Set (ν → ℝ)) :
    Submodule.span ℝ s = sInf {p : Submodule ℝ (ν → ℝ) | s ⊆ p} := rfl

theorem finite_rank_literal {ν : Type} :
    Module.finrank ℝ (ν → ℝ) = Cardinal.toNat (Module.rank ℝ (ν → ℝ)) := rfl

theorem finite_feature_dimension (ν : Type) [Fintype ν] :
    Module.finrank ℝ (ν → ℝ) = Fintype.card ν := Module.finrank_pi ℝ

theorem caratheodory_contract {ν : Type} {s : Set (ν → ℝ)} {x : ν → ℝ}
    (hx : x ∈ convexHull ℝ s) :
    ∃ (κ : Type) (_ : Fintype κ) (z : κ → ν → ℝ) (w : κ → ℝ),
      Set.range z ⊆ s ∧ AffineIndependent ℝ z ∧ (∀ j, 0 < w j) ∧
      (∑ j, w j) = 1 ∧ (∑ j, w j • z j) = x :=
  eq_pos_convex_span_of_mem_convexHull hx

end SECChallengeDefinitions
-- END material-imported-definition audit
