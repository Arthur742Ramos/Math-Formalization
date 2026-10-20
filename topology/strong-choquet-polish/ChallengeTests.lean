module
public import SCChallenge
open StrongChoquet Set Filter Topology TopologicalSpace
open scoped Topology

#check StrongChoquet.exists_legalPlay
#check StrongChoquet.strong_of_isEmpty
#check StrongChoquet.strong_of_completeMetric
#check StrongChoquet.strong_of_completelyMetrizable
#check StrongChoquet.completelyMetrizable_iInter
#check StrongChoquet.completelyMetrizable_of_isGdelta
#check StrongChoquet.isGdelta_range_of_strong
#check StrongChoquet.completelyMetrizable_of_strong
#check StrongChoquet.strong_iff_completelyMetrizable
#check StrongChoquet.polish_iff_strong
#check StrongChoquet.Move
#check StrongChoquet.Strategy
#check StrongChoquet.history
#check StrongChoquet.Follows
#check StrongChoquet.Winning
#check StrongChoquet.Strong

section Contracts
variable {X : Type u} [TopologicalSpace X]
example (a : Move X) : IsOpen a.region ∧ a.point ∈ a.region := ⟨a.isOpen, a.mem⟩
example (σ : Strategy X) (a : Move X) (h : List (Move X)) :
    IsOpen (σ.move a h) ∧ a.point ∈ σ.move a h ∧ σ.move a h ⊆ a.region :=
  ⟨σ.isOpen a h, σ.contains a h, σ.subset a h⟩
example (a : ℕ → Move X) : history a 3 = [a 2, a 1, a 0] := rfl
example (a : ℕ → Move X) (n : ℕ) : (history a n).length = n := history_length a n
example (a : ℕ → Move X) (n : ℕ) : history a n = (List.range n).reverse.map a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, List.range_succ, ih]
example (σ : Strategy X) (a : ℕ → Move X) : Follows σ a ↔
    ∀ n, (a (n+1)).region ⊆ σ.move (a n) (history a n) := Iff.rfl
example (σ : Strategy X) : Winning σ ↔
    ∀ a, Follows σ a → ∃ x, ∀ n, x ∈ σ.move (a n) (history a n) := by
  simp only [Winning, Set.Nonempty, mem_iInter]
example : Strong X ↔ ∃ σ : Strategy X, Winning σ := Iff.rfl
example (σ : Strategy X) (a : ℕ → Move X) (ha : Follows σ a) :
    (⋂ n, (a n).region) = ⋂ n, σ.move (a n) (history a n) := intersection_eq σ a ha
example (σ : Strategy X) (a₀ : Move X) :
    ∃ a : ℕ → Move X, a 0 = a₀ ∧ Follows σ a := exists_legalPlay σ a₀
example [IsEmpty X] : Strong X := strong_of_isEmpty
example [IsEmpty X] : IsEmpty (Move X) := ⟨fun a => isEmptyElim a.point⟩
example [IsCompletelyMetrizableSpace X] : Strong X := strong_of_completelyMetrizable
example [MetrizableSpace X] [SecondCountableTopology X] (h : Strong X) :
    IsCompletelyMetrizableSpace X := completelyMetrizable_of_strong h
example [MetrizableSpace X] [SecondCountableTopology X] :
    Strong X ↔ IsCompletelyMetrizableSpace X := strong_iff_completelyMetrizable
example [MetrizableSpace X] [SecondCountableTopology X] :
    PolishSpace X ↔ Strong X := polish_iff_strong
end Contracts

section MetricContracts
variable {Y : Type u} [MetricSpace Y]
example [CompleteSpace Y] : Strong Y := strong_of_completeMetric
example [CompleteSpace Y] (U : ℕ → Opens Y) :
    IsCompletelyMetrizableSpace (⋂ n, (U n : Set Y)) := completelyMetrizable_iInter U
example [CompleteSpace Y] {s : Set Y} (hs : IsGδ s) :
    IsCompletelyMetrizableSpace s := completelyMetrizable_of_isGdelta hs
example {X : Type v} [TopologicalSpace X] [SecondCountableTopology Y]
    (f : X → Y) (hf : IsEmbedding f) (h : Strong X) : IsGδ (range f) :=
  isGdelta_range_of_strong f hf h
end MetricContracts

section PointConstraint
local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩
private def marked (b : Bool) : Move Bool := ⟨b, univ, isOpen_univ, mem_univ _⟩
example : IsOpen ({true} : Set Bool) ∧ ({true} : Set Bool).Nonempty ∧
    ({true} : Set Bool) ⊆ (marked false).region ∧
    (marked false).point ∉ ({true} : Set Bool) := by simp [marked, isOpen_discrete]
example : ¬ ∃ σ : Strategy Bool, σ.move (marked false) [] = {true} := by
  rintro ⟨σ, hσ⟩
  have h := σ.contains (marked false) []
  rw [hσ] at h
  simp [marked] at h
private def historySensitive : Strategy Bool where
  move a h := if h.any (fun b => b.point) then a.region ∩ {a.point} else a.region
  isOpen _ _ := isOpen_discrete _
  contains a h := by split <;> simp_all [a.mem]
  subset a h := by split <;> simp_all
example : (marked false) = (marked false) ∧
    [marked false].length = [marked true].length ∧
    historySensitive.move (marked false) [marked false] ≠
      historySensitive.move (marked false) [marked true] := by
  simp only [historySensitive, List.any_cons, List.any_nil, Bool.or_false, marked,
    Bool.false_eq_true, ite_false, ite_true, univ_inter, List.length_cons, List.length_nil, true_and]
  intro h
  have ht : true ∈ ({false} : Set Bool) := h ▸ mem_univ true
  simp at ht
end PointConstraint

section LegalDoesNotMeanWinning
local instance : TopologicalSpace ℕ := ⊥
local instance : DiscreteTopology ℕ := ⟨rfl⟩
private def identity : Strategy ℕ where
  move a _ := a.region
  isOpen a _ := a.isOpen
  contains a _ := a.mem
  subset _ _ := subset_rfl
private def tailMove (n : ℕ) : Move ℕ :=
  ⟨n+1, {k | n < k}, isOpen_discrete _, Nat.lt_succ_self n⟩
private theorem tails_follow : Follows identity tailMove := by
  intro n k hk
  exact lt_trans (Nat.lt_succ_self n) hk
example : ¬ Winning identity := by
  intro h
  obtain ⟨k, hk⟩ := h tailMove tails_follow
  exact (lt_irrefl k) (mem_iInter.mp hk k)
end LegalDoesNotMeanWinning

-- BEGIN material-imported-definition audit
section MaterialDefinitions
variable {X : Type u} [t : TopologicalSpace X]
example (T : TopologicalSpace X) : T.IsOpen Set.univ ∧
    (∀ A B, T.IsOpen A → T.IsOpen B → T.IsOpen (A ∩ B)) ∧
    (∀ S, (∀ A ∈ S, T.IsOpen A) → T.IsOpen (⋃₀ S)) :=
  ⟨T.isOpen_univ, T.isOpen_inter, T.isOpen_sUnion⟩
example (U : Set X) : IsOpen U ↔ TopologicalSpace.IsOpen U := Iff.rfl
example (U : Set X) : IsClosed U ↔ IsOpen Uᶜ :=
  ⟨fun h => h.isOpen_compl, fun h => ⟨h⟩⟩
example (U : Set X) : U.Nonempty ↔ ∃ x, x ∈ U := Iff.rfl
example (s : Set X) : IsGδ s ↔
    ∃ T : Set (Set X), (∀ U ∈ T, IsOpen U) ∧ T.Countable ∧ s = ⋂₀ T := Iff.rfl
example (s : Set X) : IsGδ s ↔
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ s = ⋂ n, U n := isGδ_iff_eq_iInter_nat
example [SecondCountableTopology X] :
    ∃ b : Set (Set X), b.Countable ∧ t = TopologicalSpace.generateFrom b :=
  SecondCountableTopology.is_open_generated_countable
example [SecondCountableTopology X] :
    ∃ b : Set (Set X), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := exists_countable_basis X
example (b : Set (Set X)) (hb : IsTopologicalBasis b) :
    ⋃₀ b = univ ∧ t = TopologicalSpace.generateFrom b := ⟨hb.sUnion_eq, hb.eq_generateFrom⟩
example [PseudoMetrizableSpace X] :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated :=
  PseudoMetrizableSpace.exists_countably_generated
example [MetrizableSpace X] :
    (metrizableSpaceMetric X).toUniformSpace.toTopologicalSpace = t := by
  with_reducible_and_instances rfl
example : IsCompletelyMetrizableSpace X ↔
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
      @CompleteSpace X m.toUniformSpace :=
  ⟨fun h => h.complete, fun h => ⟨h⟩⟩
example [IsCompletelyMetrizableSpace X] :
    (completelyMetrizableMetric X).toUniformSpace.toTopologicalSpace = t := by
  with_reducible_and_instances rfl
example [IsCompletelyMetrizableSpace X] :
    @CompleteSpace X (completelyMetrizableMetric X).toUniformSpace :=
  complete_completelyMetrizableMetric X
example : PolishSpace X ↔ SecondCountableTopology X ∧ IsCompletelyMetrizableSpace X :=
  ⟨fun h => ⟨h.toSecondCountableTopology, h.toIsCompletelyMetrizableSpace⟩,
    fun ⟨h, k⟩ => { h, k with }⟩
example {Y : Type v} [tY : TopologicalSpace Y] (f : X → Y) (hf : IsEmbedding f) :
    Function.Injective f ∧ t = tY.induced f := ⟨hf.injective, hf.eq_induced⟩
example {Y : Type v} [tY : TopologicalSpace Y] (f : X → Y) (U : Set X) :
    @IsOpen X (tY.induced f) U ↔ ∃ V, IsOpen V ∧ f ⁻¹' V = U := Iff.rfl
example {Y : Type v} (f : Y → X) (x : X) : x ∈ range f ↔ ∃ y, f y = x := Iff.rfl
example (U : Opens X) : IsOpen (U : Set X) := U.isOpen
example {Y : Type v} [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Continuous h ∧ Continuous h.symm := ⟨h.continuous_toFun,h.continuous_invFun⟩
example (x : X) (F : Filter X) : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) := Iff.rfl
example (x y : X) : Inseparable x y ↔ 𝓝 x = 𝓝 y := Iff.rfl
example [T0Space X] (x y : X) (h : Inseparable x y) : x = y := T0Space.t0 h
example (s : Set X) : IsLindelof s ↔
    ∀ ⦃F : Filter X⦄ [NeBot F] [CountableInterFilter F],
      F ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x F := Iff.rfl
example (s : Set X) : IsLindelof s ↔ ∀ {ι : Type u} (U : ι → Set X),
    (∀ i, IsOpen (U i)) → s ⊆ ⋃ i, U i →
      ∃ c : Set ι, c.Countable ∧ s ⊆ ⋃ i ∈ c, U i := isLindelof_iff_countable_subcover
example {ι : Type v} [Nonempty ι] (s : Set X) (hs : IsLindelof s)
    (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hc : s ⊆ ⋃ i, U i) :
    ∃ f : ℕ → ι, s ⊆ ⋃ n, U (f n) := hs.indexed_countable_subcover U ho hc
example (s : Set X) : IsHereditarilyLindelof s ↔ ∀ z ⊆ s, IsLindelof z := Iff.rfl
example [SecondCountableTopology X] (s : Set X) : IsLindelof s :=
  HereditarilyLindelofSpace.isLindelof s
example [SeparableSpace X] : ∃ s : Set X, s.Countable ∧ Dense s := exists_countable_dense X
example (s : Set (Set X)) (F : Filter X) [CountableInterFilter F]
    (hs : s.Countable) (h : ∀ z ∈ s, z ∈ F) : ⋂₀ s ∈ F := (countable_sInter_mem hs).mpr h
example (s : Set X) : s.Countable ↔ Countable s := Iff.rfl
example (T : Type v) : Countable T ↔ ∃ f : T → ℕ, Function.Injective f :=
  countable_iff_exists_injective T
example (g : Set (Set X)) (A : Set X) : A ∈ Filter.generate g ↔ Filter.GenerateSets g A := Iff.rfl
example (F : Filter X) [F.IsCountablyGenerated] :
    ∃ s : Set (Set X), s.Countable ∧ F = Filter.generate s := Filter.IsCountablyGenerated.out
example (A : Set X) : Dense A ↔ ∀ x, x ∈ closure A := Iff.rfl
example (A : Set X) : closure A = ⋂₀ {C : Set X | IsClosed C ∧ A ⊆ C} := rfl
example {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : IsClosedEmbedding f) :
    IsEmbedding f ∧ IsClosed (range f) := ⟨hf.isEmbedding,hf.isClosed_range⟩
noncomputable example {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : IsEmbedding f) :
    X ≃ₜ range f := hf.toHomeomorph
example {Y : Type v} [TopologicalSpace Y] [IsCompletelyMetrizableSpace Y]
    (h : X ≃ₜ Y) : IsCompletelyMetrizableSpace X := h.isClosedEmbedding.IsCompletelyMetrizableSpace
example [IsCompletelyMetrizableSpace X] {s : Set X} (hs : IsClosed s) :
    IsCompletelyMetrizableSpace s := hs.isCompletelyMetrizableSpace
example {ι : Type v} [Countable ι] {Y : ι → Type u} [∀ i, TopologicalSpace (Y i)]
    [∀ i, IsCompletelyMetrizableSpace (Y i)] : IsCompletelyMetrizableSpace (∀ i, Y i) := inferInstance
example {ι : Type v} {Y : ι → Type u} [tY : ∀ i, TopologicalSpace (Y i)] :
    (inferInstance : TopologicalSpace (∀ i, Y i)) =
      ⨅ i, TopologicalSpace.induced (fun f => f i) (tY i) := rfl
end MaterialDefinitions

section CompleteCopyMeanings
open Metric UniformSpace
open scoped Uniformity
variable {Y : Type u} [MetricSpace Y]
example (U : Opens Y) (x y : Opens.CompleteCopy U) :
    dist x y = dist x.val y.val +
      |1 / infDist x.val (U : Set Y)ᶜ - 1 / infDist y.val (U : Set Y)ᶜ| :=
  Opens.CompleteCopy.dist_eq x y
example (U : Opens Y) :
    (inferInstance : MetricSpace (Opens.CompleteCopy U)).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace U) := rfl
example [CompleteSpace Y] (U : Opens Y) : CompleteSpace (Opens.CompleteCopy U) := inferInstance
example (y : Y) (s : Set Y) : infDist y s = ENNReal.toReal (infEDist y s) := rfl
example (y : Y) (s : Set Y) : infEDist y s = ⨅ z ∈ s, edist y z := rfl
example (y : Y) : infDist y (∅ : Set Y) = 0 := infDist_empty
example : CompleteSpace (Completion Y) := inferInstance
example : IsEmbedding ((↑) : Y → Completion Y) :=
  (Completion.isUniformEmbedding_coe Y).isEmbedding
example (x y : Y) : dist (x : Completion Y) (y : Completion Y) = dist x y := Completion.dist_eq x y
example [SecondCountableTopology Y] : SeparableSpace Y := inferInstance
example [SecondCountableTopology Y] : SeparableSpace (Completion Y) := inferInstance
example [SecondCountableTopology Y] : SecondCountableTopology (Completion Y) := inferInstance
example : Completion Y = SeparationQuotient (CauchyFilter Y) := rfl
example : CauchyFilter Y = {F : Filter Y // Cauchy F} := rfl
end CompleteCopyMeanings
section MetricMeanings
open Filter Metric
open scoped Uniformity Topology
variable {Y : Type v} [MetricSpace Y]
example : 𝓤 Y = ⨅ ε > (0 : ℝ), 𝓟 {p : Y × Y | dist p.1 p.2 < ε} :=
  PseudoMetricSpace.uniformity_dist
example (y : Y) : 𝓝 y = Filter.comap (Prod.mk y) (𝓤 Y) :=
  UniformSpace.nhds_eq_comap_uniformity y
example (x y z : Y) : dist x x = 0 ∧ dist x y = dist y x ∧
    dist x z ≤ dist x y + dist y z ∧ (dist x y = 0 ↔ x = y) :=
  ⟨dist_self x, dist_comm x y, dist_triangle x y z, dist_eq_zero⟩
example (U : Set Y) : IsOpen U ↔ ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U := Metric.isOpen_iff
example (x : Y) (r : ℝ) : ball x r = {y | dist y x < r} := rfl
example (x : Y) (r : ℝ) : closedBall x r = {y | dist y x ≤ r} := rfl
example (f : Filter Y) : Cauchy f ↔ NeBot f ∧ f ×ˢ f ≤ 𝓤 Y := Iff.rfl
example (s : Set Y) : IsComplete s ↔ ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x := Iff.rfl
example : CompleteSpace Y ↔ ∀ f : Filter Y, Cauchy f → ∃ y, f ≤ 𝓝 y :=
  ⟨fun h _ hf => h.complete hf, fun h => ⟨fun {f} hf => h f hf⟩⟩
example : CompleteSpace Y ↔ IsComplete (univ : Set Y) := completeSpace_iff_isComplete_univ
example (a : ℕ → Y) : CauchySeq a ↔
    ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (a m) (a n) < ε := Metric.cauchySeq_iff
example {Z : Type u} (f : Z → Y) (l : Filter Z) (y : Y) :
    Tendsto f l (𝓝 y) ↔ Filter.map f l ≤ 𝓝 y := Iff.rfl
example (s : Set Y) : Bornology.IsBounded s ↔
    ∃ C : ℝ, ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C := Metric.isBounded_iff
example (s : Set Y) : Metric.diam s = ENNReal.toReal (Metric.ediam s) := rfl
example (s : Set Y) : Metric.ediam s = ⨆ x ∈ s, ⨆ y ∈ s, edist x y := rfl
example (x y : Y) : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
end MetricMeanings
-- END material-imported-definition audit
