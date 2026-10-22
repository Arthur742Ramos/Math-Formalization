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

end SECChallengeDefinitions
-- END material-imported-definition audit
