module
public import CGSolution

open CategoryGame Set Filter Topology
open scoped Topology

#check CategoryGame.exists_jointPlay
#check CategoryGame.not_both_winning
#check CategoryGame.residual_has_dense_open_sequence
#check CategoryGame.second_winning_of_isMeagre
#check CategoryGame.open_residual_witness
#check CategoryGame.first_winning_of_open_residual
#check CategoryGame.first_winning_of_nonmeagre
#check CategoryGame.determined_of_baireMeasurable
#check CategoryGame.first_winning_iff_nonmeagre
#check CategoryGame.second_winning_iff_isMeagre
#check CategoryGame.OpenMove
#check CategoryGame.history
#check CategoryGame.FollowsFirst
#check CategoryGame.FollowsSecond
#check CategoryGame.FirstWins
#check CategoryGame.SecondWins
#check CategoryGame.Determined

section Contracts
variable {X : Type u} [TopologicalSpace X]
example : OpenMove X = {U : Set X // IsOpen U ∧ U.Nonempty} := rfl
example (a : ℕ → OpenMove X) : history X a 3 = [a 2, a 1, a 0] := rfl
example (a : ℕ → OpenMove X) (n : ℕ) :
    history X a n = (List.range n).reverse.map a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, List.range_succ, ih]
example (a : ℕ → OpenMove X) (n : ℕ) : (history X a n).length = n := history_length a n
example (σ : FirstStrategy X) (b : ℕ → OpenMove X) : FollowsFirst X σ b ↔
    ∀ n, (b n).val ⊆ (σ.move (history X b n)).val := Iff.rfl
example (τ : SecondStrategy X) (a : ℕ → OpenMove X) : FollowsSecond X τ a ↔
    ∀ n, (a (n+1)).val ⊆ (τ.move (a n) (history X a n)).val := Iff.rfl
example (A : Set X) (σ : FirstStrategy X) : FirstWins X A σ ↔
    ∀ b, FollowsFirst X σ b → ∃ x ∈ A, ∀ n, x ∈ (b n).val := by
  simp only [FirstWins, Set.Nonempty, mem_inter_iff, mem_iInter]
example (A : Set X) (τ : SecondStrategy X) : SecondWins X A τ ↔
    ∀ a, FollowsSecond X τ a → ¬ ∃ x ∈ A, ∀ n, x ∈ (a n).val := by
  simp only [SecondWins, Set.Nonempty, mem_inter_iff, mem_iInter]
example (A : Set X) : Determined X A ↔
    (∃ σ, FirstWins X A σ) ∨ ∃ τ, SecondWins X A τ := Iff.rfl
example (σ : FirstStrategy X) (a : OpenMove X) (h : List (OpenMove X)) :
    (σ.move (a::h)).val ⊆ a.val := σ.responds a h
example (τ : SecondStrategy X) (a : OpenMove X) (h : List (OpenMove X)) :
    (τ.move a h).val ⊆ a.val := τ.responds a h
example (σ : FirstStrategy X) (b : ℕ → OpenMove X) (hb : FollowsFirst X σ b) :
    (⋂ n, (σ.move (history X b n)).val) = ⋂ n, (b n).val := first_intersection_eq σ b hb
example (τ : SecondStrategy X) (a : ℕ → OpenMove X) (ha : FollowsSecond X τ a) :
    (⋂ n, (a n).val) = ⋂ n, (τ.move (a n) (history X a n)).val := second_intersection_eq τ a ha
example (σ : FirstStrategy X) (τ : SecondStrategy X) :
    ∃ a b : ℕ → OpenMove X,
      (∀ n, a n = σ.move (history X b n)) ∧
      (∀ n, b n = τ.move (a n) (history X a n)) ∧
      FollowsFirst X σ b ∧ FollowsSecond X τ a ∧
      ∀ n, (b n).val ⊆ (a n).val ∧ (a (n+1)).val ⊆ (b n).val := exists_jointPlay σ τ
example {A : Set X} (σ : FirstStrategy X) (τ : SecondStrategy X) (hσ : FirstWins X A σ) :
    ¬ SecondWins X A τ := not_both_winning σ τ hσ
example {S : Set X} (hS : S ∈ residual X) :
    ∃ D : ℕ → Set X, (∀ n, IsOpen (D n)) ∧ (∀ n, Dense (D n)) ∧ (⋂ n, D n) ⊆ S :=
  residual_has_dense_open_sequence hS
example {A : Set X} (hA : IsMeagre A) : ∃ τ, SecondWins X A τ := second_winning_of_isMeagre hA
example {A : Set X} (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    ∃ U : OpenMove X, ∃ S : Set X, S ∈ residual X ∧ U.val ∩ S ⊆ A :=
  open_residual_witness hA hn
end Contracts
section MetricContracts
variable {X : Type u} [MetricSpace X] [CompleteSpace X]
example {A : Set X} (U : OpenMove X) {S : Set X} (hS : S ∈ residual X) (hSA : U.val ∩ S ⊆ A) :
    ∃ σ, FirstWins X A σ := first_winning_of_open_residual U hS hSA
example {A : Set X} (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    ∃ σ, FirstWins X A σ := first_winning_of_nonmeagre hA hn
example {A : Set X} (hA : BaireMeasurableSet A) : Determined X A := determined_of_baireMeasurable hA
example {A : Set X} (hA : BaireMeasurableSet A) :
    (∃ σ, FirstWins X A σ) ↔ ¬ IsMeagre A := first_winning_iff_nonmeagre hA
example {A : Set X} (hA : BaireMeasurableSet A) :
    (∃ τ, SecondWins X A τ) ↔ IsMeagre A := second_winning_iff_isMeagre hA
end MetricContracts
-- BEGIN material-imported-definition audit
section MaterialDefinitions
variable {X : Type u} [TopologicalSpace X]
example (t : TopologicalSpace X) : t.IsOpen Set.univ ∧
    (∀ A B, t.IsOpen A → t.IsOpen B → t.IsOpen (A ∩ B)) ∧
    (∀ S, (∀ A ∈ S, t.IsOpen A) → t.IsOpen (⋃₀ S)) :=
  ⟨t.isOpen_univ, t.isOpen_inter, t.isOpen_sUnion⟩
example (U : Set X) : IsOpen U ↔ TopologicalSpace.IsOpen U := Iff.rfl
example (A : Set X) : A.Nonempty ↔ ∃ x, x ∈ A := Iff.rfl
example (A : Set X) : Dense A ↔ ∀ x, x ∈ closure A := Iff.rfl
example (A : Set X) : closure A = ⋂₀ {C : Set X | IsClosed C ∧ A ⊆ C} := rfl
example (A : Set X) : Dense A ↔
    ∀ U, IsOpen U → U.Nonempty → (U ∩ A).Nonempty := dense_iff_inter_open
example (A : Set X) : IsMeagre A ↔ Aᶜ ∈ residual X := Iff.rfl
example (A : Set X) : IsMeagre A ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsNowhereDense U) ∧ S.Countable ∧ A ⊆ ⋃₀ S :=
  isMeagre_iff_countable_union_isNowhereDense
example (A : Set X) : IsNowhereDense A ↔ interior (closure A) = ∅ := Iff.rfl
example (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
end MaterialDefinitions
open scoped symmDiff
-- The literal upstream definition, using the canonical Borel sigma-algebra.
example {Z : Type u} [TopologicalSpace Z] (A : Set Z) :
    BaireMeasurableSet A ↔
      @MeasurableSet Z (eventuallyMeasurableSpace (borel Z) (residual Z)) A := Iff.rfl

example {Z : Type u} [TopologicalSpace Z] (A : Set Z) :
    BaireMeasurableSet A ↔
      ∃ B : Set Z, @MeasurableSet Z (borel Z) B ∧ A =ᶠ[residual Z] B := Iff.rfl

-- Open approximation is a proved upstream equivalence, not definitional equality.
private theorem propertyOfBaire_iff_open_symmDiff_isMeagre
    {Z : Type u} [TopologicalSpace Z] (A : Set Z) :
    BaireMeasurableSet A ↔ ∃ O : Set Z, IsOpen O ∧ IsMeagre (A ∆ O) := by
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  constructor
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, ?_⟩
    change ∀ᶠ z in residual Z, z ∉ A ∆ O
    filter_upwards [hAO.mem_iff] with z hz
    simp only [mem_symmDiff]
    tauto
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, Filter.eventuallyEqSet_iff.mpr ?_⟩
    change ∀ᶠ z in residual Z, z ∉ A ∆ O at hAO
    filter_upwards [hAO] with z hz
    simp only [mem_symmDiff] at hz
    tauto

section MeasurableDependencies
variable {X : Type u} [TopologicalSpace X]
example : (borel X) = MeasurableSpace.generateFrom {s | IsOpen s} := rfl
example (S : Set (Set X)) (A : Set X) :
    @MeasurableSet X (MeasurableSpace.generateFrom S) A ↔
      MeasurableSpace.GenerateMeasurable S A := Iff.rfl
example (m : MeasurableSpace X) (l : Filter X) [CountableInterFilter l] (A : Set X) :
    EventuallyMeasurableSet m l A ↔ ∃ B, @MeasurableSet X m B ∧ A =ᶠ[l] B := Iff.rfl
example (l : Filter X) (A B : Set X) :
    Filter.EventuallyEqSet l A B ↔ ∀ᶠ x in l, x ∈ A ↔ x ∈ B := Filter.eventuallyEqSet_iff
example {Z : Type v} (l : Filter X) (f g : X → Z) :
    Filter.EventuallyEq l f g ↔ ∀ᶠ x in l, f x = g x := Iff.rfl
example (l : Filter X) : CountableInterFilter l ↔
    ∀ S : Set (Set X), S.Countable → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l :=
  ⟨fun h => h.countable_sInter_mem, fun h => ⟨h⟩⟩
example (g : Set (Set X)) (A : Set X) : A ∈ Filter.countableGenerate g ↔
    ∃ S : Set (Set X), S ⊆ g ∧ S.Countable ∧ ⋂₀ S ⊆ A := Filter.mem_countableGenerate_iff
example (S : Set (Set X)) : S.Countable ↔ Countable S := Iff.rfl
example (T : Type v) : Countable T ↔ ∃ f : T → ℕ, Function.Injective f :=
  countable_iff_exists_injective T
end MeasurableDependencies
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
section EmptyBoundary
variable {X : Type u} [TopologicalSpace X] [IsEmpty X]
example (σ : FirstStrategy X) : False := isEmptyElim (σ.move []).property.2.choose
example (A : Set X) : ¬ ∃ σ, FirstWins X A σ := by
  rintro ⟨σ, _⟩; exact isEmptyElim (σ.move []).property.2.choose
example (A : Set X) : ∃ τ, SecondWins X A τ := by
  have h : IsMeagre A := by
    have he : A = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x => isEmptyElim x
    simpa [he] using (IsMeagre.empty : IsMeagre (∅ : Set X))
  exact second_winning_of_isMeagre h
end EmptyBoundary
section PayoffBoundary
local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
-- A hit is existential: the same intersection may also contain points outside the target.
example : ∃ a : ℕ → OpenMove Bool,
    ({true} ∩ ⋂ n, (a n).val).Nonempty ∧ ¬ (⋂ n, (a n).val) ⊆ {true} := by
  let U : OpenMove Bool := ⟨univ,isOpen_univ,⟨true,mem_univ _⟩⟩
  refine ⟨fun _ => U, ⟨true,by simp [U]⟩,?_⟩
  intro h; have := h (show false ∈ ⋂ n : ℕ, U.val by simp [U]); simp at this
-- Legal equal moves do not make II winning: repetition loses for the universal target.
example : ∃ τ : SecondStrategy Bool, ¬ SecondWins Bool univ τ := by
  let τ : SecondStrategy Bool := ⟨fun a _ => a,fun _ _ => subset_rfl⟩
  let U : OpenMove Bool := ⟨univ,isOpen_univ,⟨true,mem_univ _⟩⟩
  refine ⟨τ,fun h => h (fun _ => U) (fun _ => subset_rfl) ?_⟩
  exact ⟨true,mem_univ _,mem_iInter.mpr fun _ => mem_univ _⟩
end PayoffBoundary
section FullHistoryBoundary
local instance : TopologicalSpace (Fin 3) := ⊥
local instance : DiscreteTopology (Fin 3) := discreteTopology_bot _
example : ∃ (σ : SecondStrategy (Fin 3)) (U V : OpenMove (Fin 3)),
    U.val ⊆ V.val ∧ U.val ⊆ (σ.move U []).val ∧ U.val ⊆ (σ.move V []).val ∧
    (σ.move U [U]).val ≠ (σ.move U [V]).val := by
  classical
  let U : OpenMove (Fin 3) := ⟨{0,1}, isOpen_discrete _, ⟨0, by simp⟩⟩
  let V : OpenMove (Fin 3) := ⟨univ, isOpen_univ, ⟨0, mem_univ _⟩⟩
  let Z : OpenMove (Fin 3) := ⟨{0}, isOpen_discrete _, ⟨0, by simp⟩⟩
  let O : OpenMove (Fin 3) := ⟨{1}, isOpen_discrete _, ⟨1, by simp⟩⟩
  let f : OpenMove (Fin 3) → List (OpenMove (Fin 3)) → OpenMove (Fin 3) := fun a h =>
    match h with
    | [] => a
    | b :: _ => if a.val = U.val then (if b.val = V.val then Z else O) else a
  have hf : ∀ a h, (f a h).val ⊆ a.val := by
    intro a h
    cases h with
    | nil => exact subset_rfl
    | cons b h =>
      change (if a.val = U.val then (if b.val = V.val then Z else O) else a).val ⊆ a.val
      split
      · next ha => rw [ha]; split <;> simp [U,Z,O]
      · exact subset_rfl
  let σ : SecondStrategy (Fin 3) := ⟨f,hf⟩
  have huv : U.val ≠ V.val := by
    intro h
    have h2 : (2 : Fin 3) ∈ U.val := h.symm ▸ mem_univ _
    simp [U] at h2
  refine ⟨σ,U,V,subset_univ _,subset_rfl,subset_univ _,?_⟩
  change (f U [U]).val ≠ (f U [V]).val
  simp only [f,ite_eq_left rfl,ite_eq_right huv]
  change ({1} : Set (Fin 3)) ≠ {0}
  intro heq
  have : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := heq ▸ (by simp)
  simp at this
end FullHistoryBoundary
