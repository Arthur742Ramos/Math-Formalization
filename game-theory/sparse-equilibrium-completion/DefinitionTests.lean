module
public import SECSolution

public section

-- BEGIN material-imported-definition audit
namespace SECDefinitions
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


theorem compact_filter_literal {ν : Type} (s : Set (ν → ℝ)) : IsCompact s ↔
    ∀ ⦃f : Filter (ν → ℝ)⦄, f.NeBot → f ≤ Filter.principal s → ∃ x ∈ s, ClusterPt x f := by
  constructor
  · intro h f hf hfs
    let := hf
    exact h hfs
  · intro h f hf hfs
    exact h hf hfs

theorem closed_complement_literal {ν : Type} (s : Set (ν → ℝ)) :
    IsClosed s ↔ IsOpen sᶜ := ⟨fun h => h.isOpen_compl, fun h => ⟨h⟩⟩

theorem continuous_open_preimage {ν : Type} (f : (ν → ℝ) → ℝ) (h : Continuous f)
    (s : Set ℝ) (hs : IsOpen s) : IsOpen (f ⁻¹' s) := h.isOpen_preimage s hs

theorem strong_dual_literal {ν : Type} : StrongDual ℝ (ν → ℝ) = ((ν → ℝ) →L[ℝ] ℝ) := rfl

theorem linear_map_laws {ν : Type} (L : (ν → ℝ) →ₗ[ℝ] ℝ) (x y : ν → ℝ) (a : ℝ) :
    L (x+y) = L x+L y ∧ L (a • x) = a*L x := ⟨L.map_add x y, L.map_smul a x⟩

theorem continuous_linear_fields {ν : Type} (f : StrongDual ℝ (ν → ℝ)) :
    Continuous f ∧ ∀ x y, f (x+y) = f x+f y := ⟨f.continuous, f.map_add⟩

theorem set_image_literal {ν : Type} (f : (ν → ℝ) → (ν → ℝ)) (s : Set (ν → ℝ)) (y : ν → ℝ) :
    y ∈ f '' s ↔ ∃ x ∈ s, f x = y := Iff.rfl

theorem compact_closed_separation_contract {ν : Type} [Fintype ν]
    (s t : Set (ν → ℝ)) (hs : Convex ℝ s) (hsc : IsCompact s)
    (ht : Convex ℝ t) (htc : IsClosed t) (hd : Disjoint s t) :
    ∃ (f : StrongDual ℝ (ν → ℝ)) (u v : ℝ),
      (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
  geometric_hahn_banach_compact_closed hs hsc ht htc hd


theorem finite_ordinal_bound (n : ℕ) (i : Fin n) : i.val < n := i.isLt

theorem finite_ordinal_extensionality {n : ℕ} (i j : Fin n) (h : i.val=j.val) : i=j := Fin.ext h

theorem natural_range_literal (n : ℕ) : (Finset.range n).val = Multiset.range n := rfl

theorem finite_upper_interval_literal {n : ℕ} (i : Fin n) :
    Finset.Ioi i = LocallyFiniteOrderTop.finsetIoi i := rfl

theorem natural_range_meaning (n i : ℕ) : i ∈ Finset.range n ↔ i < n := Finset.mem_range

theorem finite_lower_interval_literal {n : ℕ} (i : Fin n) :
    Finset.Iio i = LocallyFiniteOrderBot.finsetIio i := rfl

theorem finite_lower_interval_meaning {n : ℕ} (i j : Fin n) :
    j ∈ Finset.Iio i ↔ j < i := Finset.mem_Iio

theorem finite_prefix_cardinality {n : ℕ} (i : Fin n) : (Finset.Iio i).card = i.val := Fin.card_Iio i

theorem finite_sum_range_conversion (n : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin n, f i.val) = ∑ i ∈ Finset.range n, f i := Fin.sum_univ_eq_sum_range f n

theorem relation_embedding_meaning {α β : Type*} [LE α] [LE β]
    (e : α ↪o β) (i j : α) : e i ≤ e j ↔ i ≤ j := e.map_rel_iff'

theorem sorted_finite_coverage {n : ℕ} (s : Finset (Fin n)) :
    Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ = s :=
  s.map_orderEmbOfFin_univ rfl

theorem sorted_finite_membership {n : ℕ} (s : Finset (Fin n)) (i : Fin s.card) :
    s.orderEmbOfFin rfl i ∈ s := s.orderEmbOfFin_mem rfl i

theorem cubic_power_mean_contract {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f i)^3 ≤ (Fintype.card ι : ℝ)^2 * ∑ i, (f i)^3 := by
  simpa using pow_sum_le_card_mul_sum_pow (s := Finset.univ) (by simpa using hf) 2

theorem natural_minimum_contract (p : ℕ → Prop) [DecidablePred p] (hp : ∃ n, p n) :
    p (Nat.find hp) ∧ ∀ n, p n → Nat.find hp ≤ n :=
  ⟨Nat.find_spec hp, fun _ h => Nat.find_min' hp h⟩

theorem natural_minimum_projection (p : ℕ → Prop) [DecidablePred p] (hp : ∃ n, p n) :
    Nat.find hp = (Nat.findX hp).val := by
  apply Nat.le_antisymm (Nat.find_min' hp (Nat.findX hp).2.1)
  exact Nat.le_of_not_gt fun h => (Nat.findX hp).2.2 _ h (Nat.find_spec hp)

theorem clipped_payoff_interval_meaning (a δ x : ℝ) :
    SparseCompletion.ClippedObservation a δ x ↔
      x ∈ Set.Icc (max (-1) (a-δ)) (min 1 (a+δ)) :=
  SparseCompletion.clipped_observation_interval a δ x

theorem equivalence_inverse_meaning {α β : Type*} (e : α ≃ β) (a : α) (b : β) :
    e.symm (e a)=a ∧ e (e.symm b)=b := ⟨e.symm_apply_apply a,e.apply_symm_apply b⟩

theorem dependent_pair_meaning {α : Type*} {β : α → Type*} (i : α) (j : β i) :
    (Sigma.mk i j).fst=i ∧ (Sigma.mk i j).snd=j := ⟨rfl,rfl⟩

theorem dependent_finite_membership {ι : Type*} {κ : ι → Type*}
    (s : Finset ι) (t : ∀ i, Finset (κ i)) (x : Sigma κ) :
    x ∈ s.sigma t ↔ x.1 ∈ s ∧ x.2 ∈ t x.1 := Finset.mem_sigma

theorem dependent_sum_contract {ι : Type*} {κ : ι → Type*}
    [Fintype ι] [∀ i, Fintype (κ i)] (f : Sigma κ → ℝ) :
    (∑ x, f x)=∑ i, ∑ j, f ⟨i,j⟩ := Fintype.sum_sigma f

theorem bin_offset_contract {h : ℕ} (L : Fin h → ℕ) (b : Fin h) (i : Fin (L b)) :
    (finSigmaFinEquiv ⟨b,i⟩).val=(∑ j : Fin b.val, L (Fin.castLE b.isLt.le j))+i.val :=
  finSigmaFinEquiv_apply ⟨b,i⟩

theorem bin_partition_bijection {h : ℕ} (L : Fin h → ℕ) :
    Function.Bijective (finSigmaFinEquiv : ((b : Fin h) × Fin (L b)) → Fin (∑ b, L b)) :=
  finSigmaFinEquiv.bijective

theorem ordinal_reversal_value {n : ℕ} (i : Fin n) : i.rev.val=n-(i.val+1) := rfl

theorem ordinal_reversal_involution {n : ℕ} (i : Fin n) : i.rev.rev=i := Fin.rev_rev i

theorem reversal_permutation_meaning {n : ℕ} (i : Fin n) : Fin.revPerm i=i.rev := rfl

theorem equivalence_sum_contract {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : (∑ i, f (e i))=∑ j, f j := Equiv.sum_comp e f

end SECDefinitions
-- END material-imported-definition audit
