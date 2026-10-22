module
public import SECSolution
public meta import SECSolution

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


theorem finite_image_literal {ι κ : Type*} [DecidableEq κ] (f : ι → κ) (s : Finset ι) :
    (s.image f).val=(s.val.map f).dedup := rfl

theorem finite_image_membership {ι κ : Type*} [DecidableEq κ] (f : ι → κ) (s : Finset ι) (y : κ) :
    y ∈ s.image f ↔ ∃ x ∈ s, f x=y := Finset.mem_image

theorem finite_image_card_le {ι κ : Type*} [DecidableEq κ] (f : ι → κ) (s : Finset ι) :
    (s.image f).card ≤ s.card := Finset.card_image_le

theorem finite_image_card_exact {ι κ : Type*} [DecidableEq κ] (f : ι → κ) (s : Finset ι)
    (hf : Function.Injective f) : (s.image f).card=s.card := Finset.card_image_of_injective s hf

theorem injectivity_literal {ι κ : Type*} (f : ι → κ) :
    Function.Injective f ↔ ∀ ⦃x y⦄, f x=f y → x=y := Iff.rfl



theorem antitone_literal {m : ℕ} (v : Fin m → ℝ) :
    Antitone v ↔ ∀ ⦃i j⦄, i ≤ j → v j ≤ v i := Iff.rfl

theorem finite_nonempty_literal {ι : Type*} (s : Finset ι) :
    s.Nonempty ↔ ∃ i, i ∈ s := Iff.rfl

theorem finite_maximum_contract {m : ℕ} (s : Finset (Fin m)) (hs : s.Nonempty) :
    s.max' hs ∈ s ∧ ∀ i ∈ s, i ≤ s.max' hs :=
  ⟨Finset.max'_mem s hs,fun i hi => Finset.le_max' s i hi⟩


theorem finite_real_maximum_contract (s : Finset ℝ) (hs : s.Nonempty) :
    s.max' hs ∈ s ∧ ∀ x ∈ s, x ≤ s.max' hs :=
  ⟨Finset.max'_mem s hs,fun x hx => Finset.le_max' s x hx⟩

theorem finite_maximum_supremum_literal {α : Type*} [LinearOrder α]
    (s : Finset α) (hs : s.Nonempty) : s.max' hs=s.sup' hs id := rfl

theorem insert_zero_membership (s : Finset ℝ) (x : ℝ) :
    x ∈ insert 0 s ↔ x=0 ∨ x∈s := by
  classical
  exact Finset.mem_insert

theorem singleton_maximum_zero :
    ({0} : Finset ℝ).max' (Finset.singleton_nonempty 0)=0 := Finset.max'_singleton 0

theorem complement_membership {α : Type*} (C : Set α) (x : α) :
    x ∈ Cᶜ ↔ x ∉ C := Iff.rfl

theorem subtype_property {α : Type*} {p : α → Prop} (x : Subtype p) : p x.val := x.property

theorem subtype_finite_enumeration {α : Type*} [Fintype α] (C : Set α)
    [DecidablePred (· ∈ C)] (x : C) : x ∈ (Finset.univ : Finset C) := Finset.mem_univ x

theorem finite_type_equivalence {α : Type*} [Fintype α] :
    Function.Bijective (Fintype.equivFin α) := (Fintype.equivFin α).bijective

theorem subset_partition_forward {α : Type*} (C : Set α) [DecidablePred (· ∈ C)] :
    (∀ x : C, Equiv.Set.sumCompl C (Sum.inl x)=x.val) ∧
    (∀ x : ↥(Cᶜ), Equiv.Set.sumCompl C (Sum.inr x)=x.val) := ⟨fun _ => rfl,fun _ => rfl⟩

theorem subset_partition_inverse {α : Type*} (C : Set α) [DecidablePred (· ∈ C)] (x : α) :
    Equiv.Set.sumCompl C ((Equiv.Set.sumCompl C).symm x)=x := (Equiv.Set.sumCompl C).apply_symm_apply x

theorem decidable_predicate_literal {α : Sort*} (p : α → Prop) :
    DecidablePred p = ((x : α) → Decidable (p x)) := rfl

theorem decidable_reflection (p : Prop) (d : Decidable p) : d.decide.Reflects p := @Decidable.reflects_decide p d

theorem linear_order_contract {α : Type*} [LinearOrder α] (a b c : α) :
    (a ≤ b ∨ b ≤ a) ∧ (a ≤ b → b ≤ c → a ≤ c) ∧
    (a ≤ b → b ≤ a → a=b) ∧ (a < b ↔ a ≤ b ∧ ¬ b ≤ a) :=
  ⟨le_total a b,fun h h' => le_trans h h',fun h h' => le_antisymm h h',lt_iff_le_not_ge⟩

theorem finite_supremum_contract {α β : Type*} [SemilatticeSup α]
    (s : Finset β) (hs : s.Nonempty) (f : β → α) (a : α) :
    s.sup' hs f ≤ a ↔ ∀ b ∈ s, f b ≤ a := Finset.sup'_le_iff hs f

theorem insert_zero_nonempty (s : Finset ℝ) : (insert 0 s).Nonempty := by
  classical
  exact Finset.insert_nonempty 0 s

theorem insert_zero_literal (s : Finset ℝ) : (insert 0 s).val=Multiset.ndinsert 0 s.val := by
  classical
  rfl

theorem right_tuple_projection_contract {α β γ : Type*} (a : α) (b : β) (c : γ) :
    (a,b,c).1=a ∧ (a,b,c).2.1=b ∧ (a,b,c).2.2=c := ⟨rfl,rfl,rfl⟩

theorem tuple_real_function_mix_contract {ι α : Type*}
    (z z' : (ι → ℝ) × (ι → α → ℝ) × (α → α → ℝ)) (a b : ℝ) :
    (a • z+b • z').1=a • z.1+b • z'.1 ∧
    (a • z+b • z').2.1=a • z.2.1+b • z'.2.1 ∧
    (a • z+b • z').2.2=a • z.2.2+b • z'.2.2 := ⟨rfl,rfl,rfl⟩

theorem pi_real_mix_evaluation_contract {ι α : Type*}
    (V V' : ι → α → ℝ) (a b : ℝ) (i : ι) (h : α) :
    (a • V+b • V') i h=a*V i h+b*V' i h := rfl

theorem real_infimum_literal (s : Set ℝ) : sInf s= -sSup (-s) := Real.sInf_def s

theorem compact_infimum_attained (s : Set ℝ) (hc : IsCompact s) (hn : s.Nonempty) :
    sInf s ∈ s := hc.sInf_mem hn

theorem compact_infimum_lower (s : Set ℝ) (hc : IsCompact s) (a : ℝ) (ha : a ∈ s) :
    sInf s ≤ a := csInf_le hc.bddBelow ha

theorem real_infimum_glb (s : Set ℝ) (hn : s.Nonempty) (hb : BddBelow s) :
    IsGLB s (sInf s) := Real.isGLB_sInf hn hb

theorem cartesian_product_literal {α β : Type*} (s : Set α) (t : Set β) (a : α) (b : β) :
    (a,b) ∈ s ×ˢ t ↔ a ∈ s ∧ b ∈ t := Iff.rfl

theorem unit_singleton_contract (x : Unit) : x=() := by cases x; rfl

theorem disjoint_sum_eliminator_contract {α β γ : Type*} (f : α → γ) (g : β → γ)
    (a : α) (b : β) : Sum.elim f g (Sum.inl a)=f a ∧ Sum.elim f g (Sum.inr b)=g b := ⟨rfl,rfl⟩

theorem clone_index_cardinality (n : ℕ) : Fintype.card (Fin (n+1) ⊕ Unit)=n+2 := by
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]

theorem clone_sum_literal (n : ℕ) (f : Fin (n+1) ⊕ Unit → ℝ) :
    (∑ h, f h)=(∑ i, f (Sum.inl i))+f (Sum.inr ()) := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]

theorem conditional_infimum_contract {α : Type*} [ConditionallyCompleteLattice α]
    (s : Set α) (hn : s.Nonempty) (hb : BddBelow s) : IsGLB s (sInf s) :=
  ConditionallyCompleteLattice.isGLB_csInf s hn hb

theorem bounded_below_literal (s : Set ℝ) : BddBelow s ↔ ∃ a, ∀ b ∈ s, a ≤ b := Iff.rfl

theorem greatest_lower_bound_contract (s : Set ℝ) (a : ℝ) :
    IsGLB s a ↔ (∀ b ∈ s, a ≤ b) ∧ ∀ c, (∀ b ∈ s, c ≤ b) → c ≤ a := Iff.rfl

theorem compact_product_contract {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (s : Set α) (t : Set β) (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ×ˢ t) := hs.prod ht


theorem rational_denominator_nonzero (q : ℚ) : q.den ≠ 0 := q.den_nz

theorem rational_denominator_positive (q : ℚ) : 0 < q.den := Nat.pos_of_ne_zero q.den_nz

theorem rational_real_numerator_denominator (q : ℚ) :
    (q : ℝ)=(q.num : ℝ)/(q.den : ℝ) := Rat.cast_def q

theorem rational_real_add_mul (q r : ℚ) :
    ((q+r : ℚ) : ℝ)=(q : ℝ)+(r : ℝ) ∧ ((q*r : ℚ) : ℝ)=(q : ℝ)*(r : ℝ) :=
  ⟨Rat.cast_add _ _,Rat.cast_mul _ _⟩

theorem rational_real_sub_neg (q r : ℚ) :
    ((q-r : ℚ) : ℝ)=(q : ℝ)-(r : ℝ) ∧ ((-q : ℚ) : ℝ)= -(q : ℝ) :=
  ⟨Rat.cast_sub _ _,Rat.cast_neg _⟩

theorem rational_real_order (q r : ℚ) : (q : ℝ) ≤ (r : ℝ) ↔ q ≤ r := Rat.cast_le

theorem rational_real_injective (q r : ℚ) : (q : ℝ)=(r : ℝ) ↔ q=r := Rat.cast_inj

theorem rational_real_sum {α : Type*} (s : Finset α) (f : α → ℚ) :
    ((∑ i ∈ s, f i : ℚ) : ℝ)=∑ i ∈ s, (f i : ℝ) := by norm_cast

theorem rational_cast_selector {α : Type*} [RatCast α] (q : ℚ) :
    (q : α)=RatCast.ratCast q := rfl

theorem rational_identity_cast (q : ℚ) : Rat.cast (K := ℚ) q=q := rfl

theorem set_nonempty_literal {α : Type*} (s : Set α) : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl

theorem type_nonempty_literal {α : Type*} : Nonempty α ↔ ∃ _x : α, True := by
  constructor
  · rintro ⟨x⟩; exact ⟨x,True.intro⟩
  · rintro ⟨x,_⟩; exact ⟨x⟩

theorem finite_support_membership {α : Type*} (s : Finset α) (i : s) : (i : α) ∈ s :=
  i.property

theorem finite_support_enumeration {α : Type*} (s : Finset α) :
    (Finset.univ : Finset s)=s.attach := rfl

theorem finite_min_image_contract {α : Type*} (s : Set α) (f : α → ℝ)
    (hf : s.Finite) (hn : s.Nonempty) : ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b :=
  s.exists_min_image f hf hn


theorem natural_floor_literal (x : ℝ) : Nat.floor x=FloorSemiring.floor x := rfl

theorem natural_floor_nonnegative_bound (x : ℝ) (hx : 0 ≤ x) : (Nat.floor x : ℝ) ≤ x :=
  Nat.floor_le hx

theorem natural_floor_next_integer (x : ℝ) : x < (Nat.floor x : ℝ)+1 := Nat.lt_floor_add_one x

theorem natural_floor_monotone (x y : ℝ) (hxy : x ≤ y) : Nat.floor x ≤ Nat.floor y :=
  Nat.floor_mono hxy

theorem finite_allocation_index_card {α : Type*} [Fintype α] [DecidableEq α] (N : ℕ) :
    Fintype.card (α → Fin N)=N^Fintype.card α := by
  simp only [Fintype.card_fun,Fintype.card_fin]


theorem monotone_rational_predicate_literal (P : ℚ → Prop) :
    Monotone P ↔ ∀ a b : ℚ, a ≤ b → P a → P b := by
  constructor
  · intro h a b hab; exact h hab
  · intro h a b hab; exact h a b hab

theorem rational_archimedean_contract (x : ℚ) : ∃ n : ℕ, x < n := exists_nat_gt x


theorem rational_natural_ceil_literal (q : ℚ) : Nat.ceil q=(-Rat.floor (-q)).toNat := rfl

theorem rational_integer_floor_literal (q : ℚ) : Int.floor q=Rat.floor q := rfl

theorem natural_sqrt_lower (n : ℕ) : Nat.sqrt n*Nat.sqrt n ≤ n := Nat.sqrt_le n

theorem natural_sqrt_upper (n : ℕ) : n < (Nat.sqrt n+1)^2 := by
  simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' n

theorem rational_ceil_bound (q : ℚ) : q ≤ (Nat.ceil q : ℚ) := Nat.le_ceil q


theorem rational_ceil_strict_bound (q : ℚ) (hq : 0 ≤ q) : (Nat.ceil q : ℚ) < q+1 :=
  Nat.ceil_lt_add_one hq

theorem natural_sqrt_self_bound (n : ℕ) : Nat.sqrt n ≤ n := Nat.sqrt_le_self n


example (s : Finset ℚ) (hs : s.Nonempty) : s.min' hs = s.inf' hs id := rfl
example (s : Finset ℚ) (hs : s.Nonempty) :
    s.inf' hs id = WithTop.untop (s.inf (fun x => (x : WithTop ℚ))) (by rcases hs with ⟨x,hx⟩; simp; exact ⟨x,hx⟩) := rfl
example (s : Finset ℚ) (hs : s.Nonempty) : s.min' hs ∈ s := Finset.min'_mem s hs
example (s : Finset ℚ) (x : ℚ) (hx : x ∈ s) : s.min' ⟨x,hx⟩ ≤ x := Finset.min'_le s x hx
example (xs : List ℚ) : xs.filter (fun x => x < 0) = xs.filter (fun x => decide (x < 0)) := rfl
example {n : ℕ} (f : Fin n → ℚ) (x : ℚ) : x ∈ List.ofFn f ↔ ∃ i, f i = x := List.mem_ofFn
example {n : ℕ} (f : Fin n → ℚ) : (List.ofFn f).length=n := List.length_ofFn
example {n : ℕ} (x : ℚ) (q : Fin n → ℚ) :
    Fin.cons (α := fun _ => ℚ) x q = fun j => Fin.cases x q j := rfl
example {n : ℕ} (x : ℚ) (q : Fin n → ℚ) : Fin.cons (α := fun _ => ℚ) x q 0=x := by simp
example {n : ℕ} (x : ℚ) (q : Fin n → ℚ) (i : Fin n) :
    Fin.cons (α := fun _ => ℚ) x q i.succ=q i := by simp
example {n : ℕ} (f : Fin (n+1) → ℚ) : (∑ j, f j)=f 0+∑ j : Fin n, f j.succ := Fin.sum_univ_succ f

example {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i,j)).val=j.val+n*i.val := rfl
example {m n : ℕ} (u : Fin (m*n)) :
    (finProdFinEquiv.symm u).1.val=u.val/n := rfl
example {m n : ℕ} (u : Fin (m*n)) :
    (finProdFinEquiv.symm u).2.val=u.val%n := rfl
example {m n : ℕ} (u : Fin (m*n)) : u.divNat.val=u.val/n := rfl
example {m n : ℕ} (u : Fin (m*n)) : u.modNat.val=u.val%n := rfl


-- Stable public Option combinators and compiler-generated dependent elimination.
example {α β : Type*} (f : α → Option β) : (none : Option α).bind f=none := rfl
example {α β : Type*} (a : α) (f : α → Option β) : (some a).bind f=f a := rfl
universe uOptionAudit vOptionAudit
example {α : Type uOptionAudit} {motive : Option α → Sort vOptionAudit}
    (hn : motive none) (hs : ∀ a, motive (some a)) : Option.rec hn hs none=hn := rfl
example {α : Type uOptionAudit} {motive : Option α → Sort vOptionAudit}
    (hn : motive none) (hs : ∀ a, motive (some a)) (a : α) : Option.rec hn hs (some a)=hs a := rfl


/- Explicit finite-sum indexing and natural logarithm contracts. -/
example {m n : ℕ} (i : Fin m) : (finSumFinEquiv (Sum.inl i) : Fin (m+n)).val=i.val := rfl
example {m n : ℕ} (j : Fin n) : (finSumFinEquiv (Sum.inr j) : Fin (m+n)).val=m+j.val := rfl
example {m n : ℕ} (i : Fin m) :
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m+n)).symm (Fin.castAdd n i)=Sum.inl i :=
  finSumFinEquiv.symm_apply_apply (Sum.inl i)
example {m n : ℕ} (j : Fin n) :
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m+n)).symm (Fin.natAdd m j)=Sum.inr j :=
  finSumFinEquiv.symm_apply_apply (Sum.inr j)
example {α β γ δ : Type*} (e : α ≃ β) (f : γ ≃ δ) (a : α) :
    Equiv.sumCongr e f (Sum.inl a)=Sum.inl (e a) := rfl
example {α β γ δ : Type*} (e : α ≃ β) (f : γ ≃ δ) (c : γ) :
    Equiv.sumCongr e f (Sum.inr c)=Sum.inr (f c) := rfl
example {α : Type*} (a : α) : Equiv.refl α a=a := rfl
example {α β : Type*} (e : α ≃ β) (b : β) : e.symm b=e.invFun b := rfl
example {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) (a : α) : e.trans f a=f (e a) := rfl
example (N : ℕ) : N < 2^(Nat.log2 N+1) := Nat.lt_log2_self
example (N : ℕ) : Nat.log2 N=(if 2 ≤ N then Nat.log2 (N/2)+1 else 0) := Nat.log2_def N
example : Nat.log2 0=0 := Nat.log2_zero
example (q : ℚ) : q ≤ (Nat.ceil q : ℚ) := Nat.le_ceil q


example {n : ℕ} (f g : Fin n → ℚ) : decide (f=g)=true ↔ ∀ i, f i=g i := by
  rw [decide_eq_true_eq]
  exact ⟨fun h i => congrFun h i,fun h => funext h⟩
example (P : Fin 0 → Prop) [DecidablePred P] : decide (∀ i, P i)=true := by simp
example (P : Fin 1 → Prop) [DecidablePred P] : decide (∀ i, P i)=true ↔ P 0 := by simp


/- Exact interval-value continuity and implication-order contracts. -/
example {α β : Type*} (e : α ≃ β) : Function.Surjective e := e.surjective
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x*g x) := hf.mul hg
example (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) :
    Continuous (fun x => f x*c) := hf.mul_const c
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x+g x) := hf.add hg
example : Continuous (fun p : ℝ × ℝ => p.1*p.2) := continuous_mul
example (P Q : Prop) : P ≤ Q ↔ (P → Q) := Iff.rfl


/- Exact core dependent-conditional laws for the computed initializer. -/
example {α : Sort*} (c : Prop) [Decidable c] (h : c)
    (t : c → α) (e : ¬c → α) : dite c t e=t h := dite_eq_left h
example {α : Sort*} (c : Prop) [Decidable c] (h : ¬c)
    (t : c → α) (e : ¬c → α) : dite c t e=e h := dite_eq_right h


/- Exact finite-list generator, runtime and floor semantics for executed grid search. -/
theorem finite_list_argmin_literal {α β : Type*} [Preorder β] [DecidableLT β]
    (f : α → β) (l : List α) :
    l.argmin f=l.foldl (List.argAux (fun b c => f b < f c)) none := rfl

theorem finite_list_argmin_member {α : Type*} (f : α → ℚ) (l : List α) (a : α)
    (h : l.argmin f=some a) : a ∈ l := List.argmin_mem h

theorem finite_list_argmin_none {α : Type*} (f : α → ℚ) (l : List α) :
    l.argmin f=none ↔ l=[] := List.argmin_eq_none

theorem finite_list_argmin_minimal {α : Type*} (f : α → ℚ) (l : List α) (a b : α)
    (ha : a ∈ l) (hb : l.argmin f=some b) : f b ≤ f a := List.le_of_mem_argmin ha hb

theorem finite_filterMap_membership {α β : Type*} (f : α → Option β) (l : List α) (b : β) :
    b ∈ l.filterMap f ↔ ∃ a ∈ l,f a=some b := List.mem_filterMap

theorem finite_filterMap_runtime {α β : Type*} (f : α → Option β) (l : List α) :
    l.filterMap f=List.filterMapTR f l := by rw [List.filterMap_eq_filterMapTR]

theorem finite_flatMap_runtime {α β : Type*} (f : α → List β) (l : List α) :
    l.flatMap f=List.flatMapTR f l := by rw [List.flatMap_eq_flatMapTR]

theorem finite_range_literal (n : ℕ) : List.finRange n=List.ofFn (fun i : Fin n => i) := rfl

theorem finite_range_member (n : ℕ) (i : Fin n) : i ∈ List.finRange n := List.mem_finRange i

theorem finite_range_length (n : ℕ) : (List.finRange n).length=n := List.length_finRange

theorem finite_array_append_list {α : Type*} (a : Array α) (l : List α) :
    (Array.appendList a l).toList=a.toList++l := by
  simpa only [Array.appendList_eq_append] using (Array.toList_appendList (xs := a) (l := l))

theorem finite_array_push_list {α : Type*} (a : Array α) (x : α) :
    (a.push x).toList=a.toList++[x] := Array.toList_push

theorem finite_decidable_rel_literal {α : Sort*} (r : α → α → Prop) :
    DecidableRel r=(∀ a b,Decidable (r a b)) := rfl

theorem finite_decidable_lt_literal :
    DecidableLT ℚ=DecidableRel (fun a b : ℚ => a < b) := rfl

theorem finite_rat_nat_floor_cast (q : ℚ) : Nat.floor (q : ℝ)=Nat.floor q := by
  rw [←Int.floor_toNat,←Int.floor_toNat,Rat.floor_cast]

theorem finite_list_fold_nil {α β : Type*} (f : α → β → α) (z : α) :
    ([] : List β).foldl f z=z := rfl

theorem finite_list_fold_cons {α β : Type*} (f : α → β → α) (z : α) (a : β) (l : List β) :
    (a::l).foldl f z=l.foldl f (f z a) := rfl


theorem finite_sigma_empty_roundtrip {a b : Type*} [IsEmpty a] [IsEmpty b] (x : a) :
    (Equiv.equivOfIsEmpty a b).symm ((Equiv.equivOfIsEmpty a b) x) = x :=
  (Equiv.equivOfIsEmpty a b).symm_apply_apply x

theorem finite_sigma_congr_literal {a b : Type*} {f : b → Type*} (e : a ≃ b)
    (x : Sigma (fun a => f (e a))) : (e.sigmaCongrLeft) x = ⟨e x.1, x.2⟩ := rfl

theorem finite_sigma_unique_inverse {a : Type*} (f : a → Type*) [Unique a] (y : f default) :
    (Equiv.uniqueSigma f).symm y = ⟨default, y⟩ := Equiv.uniqueSigma_symm_apply y

theorem finite_sigma_fin_congr {m n : Nat} (h : m = n) (i : Fin m) :
    ((finCongr h) i).val = i.val := finCongr_apply_coe h i

theorem finite_sigma_cast_literal {n : Nat} (i : Fin n) : (Fin.cast rfl i).val = i.val := rfl

theorem finite_sigma_default_zero : (default : Fin 1).val = 0 := rfl


theorem finite_sigma_nonzero {n : Nat} [NeZero n] : n ≠ 0 := NeZero.ne n

theorem finite_sigma_positive {n : Nat} [NeZero n] : 0 < n := Nat.pos_of_neZero n

theorem finite_sigma_successor_nonzero (n : Nat) : NeZero (n+1) := inferInstance


theorem finite_floorsemiring_nat_cast {α : Type*} [Semiring α] [PartialOrder α]
    [FloorSemiring α] : Function.Injective (Nat.cast : ℕ → α) :=
  FloorSemiring.natCast_strictMono.injective


theorem finite_nontrivial_one_nonzero {α : Type*} [MulZeroOneClass α] [Nontrivial α] :
    (1 : α) ≠ 0 := (NeZero.one (M₀ := α)).out

/-- Exact-size Vector data invariant. -/
theorem counted_vector_size {α : Type*} {n : Nat} (v : Vector α n) :
    v.toArray.size = n := v.size_toArray

/-- The actual finite-index transport used by the exposed Vector accessor. -/
theorem counted_vector_get {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) :
    v.get i = v.toArray[(i.cast v.size_toArray.symm).val] := rfl

/-- Indexing notation denotes the valid-index method of the supplied instance. -/
theorem counted_getelem_method {C : Type*} {I : Type*} {α : Type*}
    {valid : C → I → Prop} [inst : GetElem C I α valid]
    (c : C) (i : I) (hi : valid c i) :
    c[i]'hi = @GetElem.getElem C I α valid inst c i hi := rfl

/-- Use the proved Array/List conversion contract across module boundaries. -/
theorem counted_array_read {α : Type*} (a : Array α) (i : Nat)
    (hi : i < a.toList.length) : a[i] = a.toList[i] :=
  (Array.getElem_toList hi).symm

/-- Logical Boolean conjunction truth-table branch; not an operational cost law. -/
theorem counted_bool_false (b : Bool) : Bool.and false b = false := rfl

/-- Actual pinned csimp theorem, proved equality rather than opaque rfl assertion. -/
theorem counted_bool_executable : Bool.and = Bool.Internal.and :=
  Bool.and_eq_internalAnd

/-- Structural right fold supporting the literal sum definition. -/
theorem counted_foldr_cons {α β : Type*} (f : α → β → β) (z : β)
    (a : α) (xs : List α) : (a :: xs).foldr f z = f a (xs.foldr f z) :=
  List.foldr_cons

/-- Generic Add/Zero sum contract; applies to both Rat values and Nat ledgers. -/
theorem counted_sum_cons {α : Type*} [Add α] [Zero α] (a : α) (xs : List α) :
    (a :: xs).sum = a + xs.sum := List.sum_cons

/-- Actual logical finite-bounded read in the tail; no default element or choice. -/
theorem counted_list_get_succ {α : Type*} (a : α) (xs : List α)
    (i : Fin xs.length) : (a :: xs).get i.succ = xs.get i := rfl


-- Minimum-support retained foundation controls
universe minimumU minimumV

example {α : Sort minimumU} {r : α → α → Prop} {x y : α} (h : Acc r x) (hy : r y x) : Acc r y := Acc.inv h hy

example {α : Sort minimumU} {r : α → α → Prop} {C : α → Sort minimumV} (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) (h : Acc r x) : WellFounded.fixF F x h = F x (fun y hy => WellFounded.fixF F y (Acc.inv h hy)) := WellFounded.fixF_eq F x h

example {α : Sort minimumU} {r : α → α → Prop} {C : α → Sort minimumV} (hw : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : WellFounded.fix hw F x = F x (fun y _ => WellFounded.fix hw F y) := WellFounded.fix_eq hw F x

example (p : Prop) : (letI : Decidable p := Classical.propDecidable p; decide p = true) ↔ p := by
  classical
  simp

theorem finite_equiv_card_bijective {α : Type*} [Fintype α] {n : ℕ} (h : Fintype.card α = n) : Function.Bijective (Fintype.equivFinOfCardEq h) := (Fintype.equivFinOfCardEq h).bijective

theorem finite_classical_decEq {α : Sort*} (a b : α) : (@decide (a = b) (Classical.decEq α a b) = true) ↔ a = b := @decide_eq_true_iff (a = b) (Classical.decEq α a b)

-- Reviewed sorting and equivalence semantic controls

theorem sort_merge_empty {α : Type*} (le : α → α → Bool) (ys : List α) :
    List.merge [] ys le = ys := List.nil_merge ys

theorem sort_merge_cons {α : Type*} (le : α → α → Bool) (a b : α) (xs ys : List α) :
    List.merge (a::xs) (b::ys) le =
      if le a b then a::List.merge xs (b::ys) le else b::List.merge (a::xs) ys le :=
  List.cons_merge_cons le a b xs ys

theorem sort_merge_length {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    (List.merge xs ys le).length = xs.length+ys.length := List.length_merge le xs ys

theorem sort_split_model {α : Type*} (xs : List α) (n : ℕ) :
    xs.splitAt n = (xs.take n,xs.drop n) := List.splitAt_eq

theorem sort_reverse_aux {α : Type*} (a : α) (xs ys : List α) :
    List.reverseAux (a::xs) ys = List.reverseAux xs (a::ys) := List.reverseAux_cons

theorem sort_reverse_empty {α : Type*} : ([] : List α).reverse = [] := List.reverse_nil

theorem sort_take_cons {α : Type*} (a : α) (xs : List α) (n : ℕ) :
    (a::xs).take (n+1) = a::xs.take n := List.take_succ_cons

theorem sort_drop_cons {α : Type*} (a : α) (xs : List α) (n : ℕ) :
    (a::xs).drop (n+1) = xs.drop n := List.drop_succ_cons

theorem sort_pairwise_cons {α : Type*} (R : α → α → Prop) (a : α) (xs : List α) :
    List.Pairwise R (a::xs) ↔ (∀ b ∈ xs, R a b) ∧ List.Pairwise R xs := List.pairwise_cons

theorem sort_nodup_definition {α : Type*} (xs : List α) :
    xs.Nodup = List.Pairwise (· ≠ ·) xs := rfl

theorem sort_perm_reflexive {α : Type*} (xs : List α) : xs.Perm xs := .refl _

theorem sort_length_cons {α : Type*} (a : α) (xs : List α) :
    (a::xs).length = xs.length+1 := rfl

theorem sort_length_runtime {α : Type*} (xs : List α) :
    xs.length = xs.lengthTR := congrFun (congrFun List.length_eq_lengthTR α) xs

theorem sort_merge_pairwise {α : Type*} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b = true ∨ le b a = true) (xs ys : List α)
    (hx : xs.Pairwise (fun a b => le a b = true))
    (hy : ys.Pairwise (fun a b => le a b = true)) :
    (List.merge xs ys le).Pairwise (fun a b => le a b = true) :=
  List.pairwise_merge trans (fun a b => by simpa only [Bool.or_eq_true] using total a b) xs ys hx hy

theorem sort_merge_permutation {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    (List.merge xs ys le).Perm (xs++ys) := List.merge_perm_append le

theorem sort_pairwise_indexed {α : Type*} (R : α → α → Prop) (xs : List α) :
    xs.Pairwise R ↔ ∀ (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length),
      i < j → R xs[i] xs[j] := List.pairwise_iff_getElem

theorem sort_prefix_suffix {α : Type*} (xs : List α) (n : ℕ) :
    xs.take n ++ xs.drop n = xs := List.take_append_drop n xs

theorem sort_permutation_membership {α : Type*} (xs ys : List α) (h : xs.Perm ys) (a : α) :
    a ∈ xs ↔ a ∈ ys := h.mem_iff

theorem sort_permutation_map {α β : Type*} (f : α → β) (xs ys : List α) (h : xs.Perm ys) :
    (xs.map f).Perm (ys.map f) := h.map f

theorem sort_permutation_nodup {α : Type*} (xs ys : List α) (h : xs.Perm ys) :
    xs.Nodup ↔ ys.Nodup := h.nodup_iff

theorem sort_rational_order (a b : ℚ) :
    decide (b ≤ a) = true ↔ b ≤ a := by simp only [decide_eq_true_eq]

theorem sort_surjective_meaning {α β : Type*} (f : α → β) :
    Function.Surjective f ↔ ∀ b, ∃ a, f a = b := Iff.rfl

theorem sort_bijective_meaning {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f := Iff.rfl

theorem sort_bijection_forward {α β : Type*} (f : α → β) (h : Function.Bijective f) :
    (Equiv.ofBijective f h : α → β) = f := Equiv.coe_ofBijective f h

theorem sort_bijection_inverse {α β : Type*} (f : α → β) (h : Function.Bijective f) (b : β) :
    f ((Equiv.ofBijective f h).symm b) = b := Equiv.ofBijective_apply_symm_apply f h b

theorem sort_surjInv_contract {α β : Type*} (f : α → β) (h : Function.Surjective f) (b : β) :
    f (Function.surjInv h b) = b := Function.surjInv_eq h b

theorem sort_choose_contract {α : Type*} (p : α → Prop) (h : ∃ a,p a) :
    p (Classical.choose h) := Classical.choose_spec h


-- Authenticated natural-measure recursion context; no cost theorem.
example (n : Nat) : WellFounded.Nat.eager n = n := WellFounded.Nat.eager_eq n
example {α : Sort u} {C : α → Sort v} (h : α → Nat) (F : (x : α) → ((y : α) → h y < h x → C y) → C x) (x : α) : WellFounded.Nat.fix (motive := C) h F x = F x (fun y _ => WellFounded.Nat.fix (motive := C) h F y) := WellFounded.Nat.fix_eq (motive := C) h F x

open SparseCompletion
#guard rationalSortedCutCheck 1 0 0 (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) = (true,1)
#guard rationalSortedCutCheck 1 0 (-1) (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) = (false,1)
#guard (rationalSortedCutCheck 1 2 0 (fun _ : Fin 2 => 1) (fun i => if i.val=0 then 1 else -1)).1 = true
#guard (rationalSortedCutCheck 1 2 0 (fun _ : Fin 2 => 1) (fun i => if i.val=0 then 2 else -2)).1 = false
#guard (rationalSortedCutCheck 1 2 0 (fun _ : Fin 2 => 1) (fun i => if i.val=0 then -2 else 2)).1 = false
#guard ((rationalLabelSort (fun i : Fin 3 => if i.val=0 then (1/2 : ℚ) else if i.val=1 then -3 else 2)).1.map Prod.fst).map Fin.val = [2,0,1]
#guard (rationalPerspectiveCutCheck 1 1 0 (fun i : Fin 2 => if i.val=0 then 0 else 1) (fun _ => 0)).1 = true
#guard (rationalPerspectiveCutCheck 1 1 0 (fun _ : Fin 1 => 1) (fun _ => 1)).1 = false
#guard (rationalPerspectiveCutCheck 1 1 1 (fun _ : Fin 1 => 1) (fun _ => 1)).1 = true
#guard (rationalIntervalCutCheck 1 1 0 (fun _ : Fin 1 => 1) (fun i : Fin 2 => if i.val=0 then 0 else 1) (fun _ _ => 0)).1 = true
#guard (rationalPerspectiveCutCheck 1 1 0 (fun _ : Fin 1 => (1/2 : ℚ)) (fun _ => (1/8 : ℚ))).1 = true


-- Exact deduplication, denominator and generated-recursor semantics
theorem future43_list_toFinset_delegation {α : Type*} [DecidableEq α] (xs : List α) : xs.toFinset = (xs : Multiset α).toFinset := rfl

theorem future43_multiset_toFinset_data {α : Type*} [DecidableEq α] (s : Multiset α) : s.toFinset.val = s.dedup := rfl

theorem future43_multiset_dedup_coercion {α : Type*} [DecidableEq α] (xs : List α) : (xs : Multiset α).dedup = (xs.dedup : Multiset α) := Multiset.coe_dedup xs

theorem future43_list_dedup_fold_selector {α : Type*} [DecidableEq α] (xs : List α) : xs.dedup = List.pwFilter (· ≠ ·) xs := rfl

theorem future43_pairwise_filter_fold {α : Type*} (R : α → α → Prop) [DecidableRel R] (xs : List α) : List.pwFilter R xs = xs.foldr (fun x ys => if ∀ y ∈ ys, R x y then x::ys else ys) [] := rfl

theorem future43_constructor_payload_conversion {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup) : (⟨(xs : Multiset α), by simpa only [Multiset.coe_nodup] using hn⟩ : Finset α) = xs.toFinset := List.toFinset_eq hn

theorem future43_multiset_coercion_nodup {α : Type*} (xs : List α) : (xs : Multiset α).Nodup ↔ xs.Nodup := Multiset.coe_nodup

theorem future43_rational_denominator_positive (q : ℚ) : 0 < q.den := Rat.den_pos q

theorem future43_rational_sum_denominator_contract (q t : ℚ) : (q+t).den ∣ q.den*t.den := Rat.add_den_dvd q t

theorem future43_list_generated_recursor_nil {α β : Type*} (z : β) (step : α → List α → β → β) : List.rec (motive := fun _ : List α => β) z step [] = z := rfl

theorem future43_list_generated_recursor_cons {α β : Type*} (z : β) (step : α → List α → β → β) (a : α) (xs : List α) : List.rec (motive := fun _ : List α => β) z step (a::xs) = step a xs (List.rec (motive := fun _ : List α => β) z step xs) := rfl

open SparseCompletion
#guard rationalViolationSearch 1 0 0 0 0 [] = (none,1)
#guard rationalViolationSearch 1 0 (-1) 0 0 [] = (some 0,1)
#guard rationalViolationSearch 1 2 0 0 0 [(1,2)] = (some 1,2)
#guard rationalViolationSearch 1 2 0 0 0 [(1,0),(1,2)] = (some 2,3)
#guard rationalViolationSearch 1 2 0 1 2 [(1,0)] = (some 0,1)
#guard rationalViolationSearch 1 2 0 0 0 [(1,0),(1,0)] = (none,3)
#guard (rationalSortedViolation (m:=0) 1 0 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).1 = none
#guard (rationalSortedViolation (m:=0) 1 0 (-1) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).1 = some ∅
#guard (rationalSortedViolation 1 2 0 (fun _ : Fin 2 => 1) (fun i => if i.val=0 then 0 else 2)).1 = some {⟨1,by decide⟩}
#guard (rationalSortedViolation 1 2 0 (fun _ : Fin 2 => 1) (fun _ => 0)).1 = none
#guard (rationalSortedViolation 1 2 1 (fun _ : Fin 2 => 1) (fun _ => 2)).1 = some Finset.univ
#guard (rationalSortedViolation 1 2 0 (fun _ : Fin 2 => 0) (fun _ => 3)).1 = none
#guard (rationalSortedViolation 1 2 0 (fun _ : Fin 2 => 1) (fun i => if i.val=0 then 0 else 2)).2 ≤ 2*(Nat.log2 2+2)+1
#guard rationalPrefixArithmetic 0 1 0 0 0 [] = (true,1,4)
#guard rationalPrefixArithmetic 0 1 0 0 0 [(1,1)] = (false,2,10)
#guard rationalPrefixArithmetic 0 1 1 0 2 [(1,0),(1,0)] = (false,1,4)
#guard rationalPrefixArithmetic 0 1 (-1) 0 0 [] = (false,1,4)
#guard rationalPrefixArithmetic 0 1 0 0 0 [(1,0),(1,0)] = (true,3,16)
#guard rationalSortedArithmetic 0 1 0 (fun _ : Fin 0 => 0) (fun _ => 0) = (true,1,4)
#guard rationalSortedArithmetic 0 1 0 (fun _ : Fin 1 => 1) (fun _ => 0) = (true,2,11)
#guard rationalSortedArithmetic 0 1 0 (fun _ : Fin 1 => 1) (fun _ => 1) = (false,2,11)
#guard rationalSortedArithmetic 0 1 (-1) (fun _ : Fin 0 => 0) (fun _ => 0) = (false,1,4)
#guard rationalDenominatorProduct [(1/2 : ℚ),1/3] = 6
#guard (([(1/2 : ℚ),-1/2] : List ℚ).sum).den = 1
#guard rationalNodupSortedViolation 0 1 (-1) (fun _ : Fin 0 => 0) (fun _ => 0) = (some ∅,1)
#guard rationalNodupSortedViolation 0 1 0 (fun _ : Fin 1 => 1) (fun _ => 1) = (some {0},2)
#guard rationalIntervalExactCheck (fun _ : Fin 1 => fun _ : Fin 1 => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => 1/2) (fun _ => 1/2) 1 (1/2) 0 = true
#guard rationalIntervalExactCheck (fun _ : Fin 1 => fun _ : Fin 1 => 1) (fun _ => fun _ => 1) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => 1) (fun _ => 0) 1 0 0 = false
#guard rationalIntervalExactCheck (fun _ : Fin 1 => fun _ : Fin 1 => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 1) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => 1) (fun _ => 0) 1 0 0 = false
#guard rationalIntervalExactCheck (fun _ : Fin 1 => fun _ : Fin 1 => 0) (fun _ => fun _ => 0) (fun _ => fun _ => 0) (fun _ => fun _ => (-1)) (fun _ => fun _ => 1) (fun _ => fun _ => 1/2) (fun _ => 1/2) (fun _ => 1/2) 1 (1/2) 1 = false
#guard ((rationalIntervalExactReconstruction (k:=1) (m:=1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1/2) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1/2) (fun _ => 1/2) 1 (1/2) (1/2)).map (fun out => out.1 0 0)) = some 1
#guard (rationalIntervalExactReconstruction (k:=1) (m:=1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1) (fun _ => 0) 1 0 0).isNone
#guard (rationalIntervalExactReconstruction (k:=1) (m:=1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1) (fun _ => 0) 1 0 0).isNone
#guard (rationalIntervalExactReconstruction (k:=1) (m:=0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1) (fun _ => 0) 1 0 0).isSome
#guard ((rationalIntervalExactReconstruction (k:=1) (m:=1) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1) (fun _ => 0) 1 0 0).map (fun out => out.1 0 0)) = some (-1)
#guard (rationalIntervalExactReconstruction (k:=1) (m:=1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 1/2) (fun _ => 1/2) 0 (1/2) 0).isSome


-- Exact relation, generated-recursor and finite-existential semantics
theorem future52_relation_refl_trans_refl {α : Type*} (R : α → α → Prop) (a : α) : Relation.ReflTransGen R a a := .refl

theorem future52_relation_refl_trans_tail {α : Type*} {R : α → α → Prop} {a b c : α}
    (h : Relation.ReflTransGen R a b) (e : R b c) : Relation.ReflTransGen R a c := .tail h e

theorem future52_natural_recursor_zero {α : Sort*} (z : α) (step : Nat → α → α) : Nat.rec z step 0 = z := rfl

theorem future52_natural_recursor_succ {α : Sort*} (z : α) (step : Nat → α → α) (n : Nat) :
    Nat.rec z step (Nat.succ n) = step n (Nat.rec z step n) := rfl

theorem future52_finite_exists_runtime_semantics {n : Nat} {f : (i : Nat) → i < n → Bool} :
    Nat.anyLTTR n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := Nat.anyLTTR_eq_true

theorem future52_finite_exists_csimp_equality : @Nat.decidableExistsLT = @Nat.decidableExistsLTTR :=
  Nat.decidableExistsLT_eq_decidableExistsLTTR

theorem future52_finite_exists_decide_true {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    decide (∃ i, P i) = true ↔ ∃ i, P i := by simp only [decide_eq_true_eq]

theorem future52_bool_disjunction_false (b : Bool) : Bool.or false b = b := rfl

theorem future52_bool_disjunction_true (b : Bool) : Bool.or true b = true := rfl

theorem future52_bool_disjunction_runtime_equality : Bool.or = Bool.Internal.or := Bool.or_eq_internalOr

open SparseCompletion
#guard rationalPerspectiveViolation 0 1 0 (fun _ : Fin 1 => 1) (fun _ => 1) = (some {0},2)
#guard rationalPerspectiveViolation 0 1 1 (fun _ : Fin 1 => 1) (fun _ => 1) = (none,2)
#guard rationalPerspectiveViolation 1 0 0 (fun _ : Fin 1 => 0) (fun _ => 0) = (none,2)
#guard rationalPerspectiveViolation 0 1 (-1) (fun _ : Fin 0 => 0) (fun _ => 0) = (none,1)
#guard rationalIntervalViolation 0 1 0 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) (fun _ _ => 1) = (some {0},2)
#guard rationalIntervalViolation 0 1 1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1) (fun _ _ => 1) = (none,2)
#guard rationalIntervalViolation 1 0 0 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 0) (fun _ _ => 0) = (none,2)
#guard rationalDemandNetworkCut (fun _ : Fin 0 => 0) (fun _ _ => 0) ∅ = 0
#guard rationalDemandNetworkCut (fun i : Fin 2 => if i=0 then 1 else -1) (fun i j => if i=j then 0 else 1) {0} = 1
#guard rationalDemandNetworkCut (fun i : Fin 2 => if i=0 then 1 else -1) (fun i j => if i=j then 0 else 1) ∅ = 1
#guard rationalDemandNetworkCut (fun i : Fin 2 => if i=0 then 1 else -1) (fun i j => if i=j then 0 else 1) Finset.univ = 1
#guard (rationalPerspectiveSeparator (m:=1) 1 1 0 {0} (fun _ => 1)).1 0 = 1
#guard (rationalPerspectiveSeparator (m:=1) 1 1 0 {0} (fun _ => 1)).2.1 0 = 1
#guard (rationalPerspectiveSeparator (m:=1) 1 1 0 {0} (fun _ => 1)).2.2 = -1
#guard (rationalPerspectiveSeparator (m:=1) 1 1 0 {0} (fun _ => 1/2)).1 0 = 0
#guard (rationalPerspectiveSeparator (m:=1) 1 1 0 {0} (fun _ => 1/2)).2.2 = -(1/4)
#guard rationalFlowCertificateCheck (m:=0) (fun _ => 0) (fun _ => 0) 1 0 0 (fun _ _ => 0) (fun _ => 0) = true
#guard rationalFlowCertificateCheck (m:=1) (fun _ => 0) (fun _ => 0) 1 0 0 (fun _ _ => 0) (fun _ => 0) = true
#guard rationalFlowCertificateCheck (m:=1) (fun _ => 0) (fun _ => 1) 1 0 0 (fun _ _ => 0) (fun _ => 0) = false
#guard rationalFlowCertificateCheck (m:=1) (fun _ => 1/2) (fun _ => 0) 0 (1/2) 0 (fun _ _ => 0) (fun _ => 0) = true
#guard rationalFlowCertificateCheck (m:=1) (fun _ => 1/2) (fun _ => 0) 0 (1/2) 0 (fun _ _ => 1) (fun _ => 0) = false
#guard rationalFlowCertificateCheck (m:=0) (fun _ => 0) (fun _ => 0) (-1) 0 0 (fun _ _ => 0) (fun _ => 0) = false
#guard ((rationalFlowCompletionFromCertificate (m:=2) (fun _ => 1/2) (fun i => if i=0 then 1/2 else -1/2) 1 1 0 (fun i j => if i=0 ∧ j=1 then 1/4 else 0) (fun i => if i=1 then 1/4 else 0)).map (fun B => (B 0 1,B 1 0))) = some (-1,1)
#guard ((rationalFlowCompletionFromCertificate (m:=2) (fun i => if i=0 then 0 else 1/2) (fun i => if i=0 then 1/2 else 0) 1 (1/2) 0 (fun _ _ => 0) (fun _ => 0)).map (fun B => (B 0 1,B 1 0))) = some (-1,1)
#guard (rationalFlowCompletionFromCertificate (m:=2) (fun i => if i=0 then 0 else 1/2) (fun i => if i=0 then 1 else 0) 1 (1/2) 0 (fun _ _ => 0) (fun _ => 0)).isNone
#guard rationalFlowCertificateCheck (m:=2) (fun _ => 1/2) (fun i => if i=0 then 1/2 else -1/2) 1 1 0 (fun _ _ => 0) (fun _ => 0) = false
#guard 3 ∈ residualReachLayers (fun i j : Fin 4 => decide (j.val=i.val+1)) 0 3
#guard 3 ∉ residualReachLayers (fun i j : Fin 4 => decide (j.val=i.val+1)) 0 2
#guard residualReachLayers (fun i j : Fin 4 => decide (j.val=i.val+1)) 0 4 = Finset.univ
#guard 0 ∉ residualReachLayers (fun i j : Fin 3 => decide (j.val=i.val+1)) 2 3
#guard residualReachLayers (fun _ _ : Fin 1 => false) 0 1 = {0}
#guard residualReachLayers (fun i j : Fin 2 => decide (i ≠ j)) 0 2 = Finset.univ
#guard rationalResidualAdj (n:=1) (fun _ _ => 1) (fun _ _ => 1) 0 0 = false
#guard rationalResidualAdj (n:=1) (fun _ _ => 0) (fun _ _ => -1) 0 0 = true
#guard rationalNetFlow (n:=2) (fun i j => if i=0 ∧ j=1 then 1/4 else if i=1 ∧ j=0 then 1/8 else 0) 0 1 = 1/8
#guard rationalResidualAdj (n:=2) (fun _ _ => 1/4) (rationalNetFlow (fun i j => if i=0 ∧ j=1 then 1/4 else if i=1 ∧ j=0 then 1/8 else 0)) 0 1 = true
#guard rationalResidualAdj (n:=2) (fun _ _ => 1/4) (fun i j => if i=0 ∧ j=1 then 1/4 else if i=1 ∧ j=0 then 1/8 else 0) 0 1 = false


-- Fourteen retained semantic bridges; exact compilation receipts are recorded separately.
theorem finite_complement_universe_difference {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) : sᶜ = Finset.univ \ s := Finset.compl_eq_univ_sdiff s

theorem finite_complement_membership {α : Type*} [Fintype α] [DecidableEq α] (a : α) (s : Finset α) : a ∈ sᶜ ↔ a ∉ s := Finset.mem_compl

theorem finite_difference_data {α : Type*} [DecidableEq α] (s t : Finset α) : (s \ t).val = s.val - t.val := Finset.sdiff_val s t

theorem list_difference_nil {α : Type*} [BEq α] (xs : List α) : xs.diff [] = xs := rfl

theorem list_erasure_runtime_equality : @List.erase = @List.eraseTR := List.erase_eq_eraseTR

theorem finite_erasure_data {α : Type*} [DecidableEq α] (s : Finset α) (a : α) : (s.erase a).val = s.val.erase a := Finset.erase_val s a

theorem multiset_erasure_quotient {α : Type*} [DecidableEq α] (xs : List α) (a : α) : (xs : Multiset α).erase a = (xs.erase a : Multiset α) := Multiset.coe_erase xs a

theorem generated_abs_rational_semantics (q : ℚ) : |q| = max q (-q) := abs_eq_max_neg

theorem generated_single_real_semantics {ι : Type*} [DecidableEq ι] (i j : ι) (x : ℝ) : (Pi.single i x : ι → ℝ) j = (if j = i then x else 0) := Pi.single_apply i x j

theorem finite_vector_constructor_array {α : Type*} {n : ℕ} (f : Fin n → α) : (Vector.ofFn f).toArray = Array.ofFn f := rfl

theorem finite_vector_constructor_coordinate {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) : (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  simp only [Vector.getElem_ofFn]

theorem integer_magnitude_nonnegative_constructor (n : ℕ) : (Int.ofNat n).natAbs = n := rfl

theorem integer_magnitude_negative_constructor (n : ℕ) : (Int.negSucc n).natAbs = n+1 := rfl

theorem integer_magnitude_rational_cast (z : ℤ) : (z.natAbs : ℚ) = |(z : ℚ)| := by
  rw [Nat.cast_natAbs,Int.cast_abs]

open SparseCompletion

def cachedBFSTestChain : CachedBFSAdj 4 :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => decide (v.val=u.val+1)))
def cachedBFSTestShortcut : CachedBFSAdj 4 :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => decide
    (v.val=u.val+1 ∨ (u.val=0 ∧ v.val=3))))
def cachedBFSTestCycle : CachedBFSAdj 3 :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => decide
    (v.val=(u.val+1)%3)))
def cachedBFSTestDisconnected : CachedBFSAdj 3 :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => decide (u.val=0 ∧ v.val=1)))
def cachedBFSTestSingleton : CachedBFSAdj 1 :=
  Vector.ofFn (fun _ => Vector.ofFn (fun _ => false))

#guard (cachedBFSPath cachedBFSTestChain 0 3).map (List.map Fin.val)=some [0,1,2,3]
#guard (cachedBFSResult cachedBFSTestChain 0 3).map (fun z => z.2.map Fin.val)=some (some 2)
#guard (cachedBFSPath cachedBFSTestChain 3 0)=none
#guard (cachedBFSPath cachedBFSTestShortcut 0 3).map (List.map Fin.val)=some [0,3]
#guard (cachedBFSPath cachedBFSTestCycle 2 1).map (List.map Fin.val)=some [2,0,1]
#guard (cachedBFSPath cachedBFSTestCycle 1 1).map (List.map Fin.val)=some [1]
#guard (cachedBFSPath cachedBFSTestDisconnected 0 2)=none
#guard (cachedBFSPath cachedBFSTestDisconnected 0 1).map (List.map Fin.val)=some [0,1]
#guard (cachedBFSResult cachedBFSTestSingleton 0 0).map
  (fun z => (z.1.map Fin.val,z.2.map Fin.val))=some ([0],none)
#guard (cachedBFSResult cachedBFSTestChain 2 2).map (fun z => z.2)=some none

def cachedBFSTestCapacity : Fin 2 → Fin 2 → ℚ :=
  fun u v => if u.val=0 ∧ v.val=1 then 1 else 0
/-- Net flow includes the negative reverse entry. -/
def cachedBFSTestNetFlow : Fin 2 → Fin 2 → ℚ :=
  fun u v => if u.val=0 ∧ v.val=1 then 1 else
    if u.val=1 ∧ v.val=0 then -1 else 0

#guard ((cacheResidualAdj cachedBFSTestCapacity cachedBFSTestNetFlow).get 0).get 1=false
#guard ((cacheResidualAdj cachedBFSTestCapacity cachedBFSTestNetFlow).get 1).get 0=true
#guard (cachedRationalResidualPath cachedBFSTestCapacity cachedBFSTestNetFlow 1 0).map
  (fun z => z.1.map Fin.val)=some [1,0]
#guard cachedRationalResidualPath cachedBFSTestCapacity cachedBFSTestNetFlow 0 1=none
#guard (cacheResidualAdj (n:=0) (fun _ _ => 0) (fun _ _ => 0)).size=0

#guard rationalPositiveNetFlow (n:=1) (fun _ _ => -(3/4)) 0 0 = 0
#guard rationalPositiveNetFlow (n:=1) (fun _ _ => 3/4) 0 0 = 3/4
#guard rationalNetFlow (rationalPositiveNetFlow (n:=2) (fun i j => if i=0 ∧ j=1 then 3/4 else if i=1 ∧ j=0 then -(3/4) else 0)) 0 1 = 3/4

end SECDefinitions
-- END material-imported-definition audit
