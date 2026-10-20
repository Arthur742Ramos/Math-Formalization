module
public import CPSolution

open ChoquetProduct Set

#check ChoquetProduct.follows_intersection_eq
#check ChoquetProduct.exists_compatiblePlay
#check ChoquetProduct.alphaFavorable_of_isEmpty
#check ChoquetProduct.exists_dense_isGdelta_fiber_witness
#check ChoquetProduct.baireSpace_prod
#check ChoquetProduct.metricStrategy_wins
#check ChoquetProduct.alphaFavorable_of_completeMetric
#check ChoquetProduct.baireSpace_prod_completeMetric
#check ChoquetProduct.OpenMove
#check ChoquetProduct.history
#check ChoquetProduct.Follows
#check ChoquetProduct.SecondWins
#check ChoquetProduct.AlphaFavorable
#check ChoquetProduct.metricStrategy

section Contracts
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
example (σ : SecondStrategy Y) (a : ℕ → OpenMove Y) (ha : Follows Y σ a) :
    (⋂ n, (a n).val) = ⋂ n, (σ.move (a n) (history Y a n)).val := follows_intersection_eq σ a ha
example (σ : SecondStrategy Y) (a₀ : OpenMove Y) :
    ∃ a : ℕ → OpenMove Y, a 0 = a₀ ∧ Follows Y σ a := exists_compatiblePlay σ a₀
example [IsEmpty Y] : AlphaFavorable Y := alphaFavorable_of_isEmpty
example [BaireSpace X] (σ : SecondStrategy Y) (hσ : SecondWins Y σ)
    (D : ℕ → Set (X × Y)) (ho : ∀ n, IsOpen (D n)) (hd : ∀ n, Dense (D n))
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ G : Set X, IsGδ G ∧ Dense G ∧ ∀ x ∈ G, ∃ y ∈ V, ∀ n, (x,y) ∈ D n :=
  exists_dense_isGdelta_fiber_witness σ hσ D ho hd hVo hVn
example [BaireSpace X] (hY : AlphaFavorable Y) : BaireSpace (X × Y) := baireSpace_prod hY
example : OpenMove Y = {U : Set Y // IsOpen U ∧ U.Nonempty} := rfl
example (σ : SecondStrategy Y) (a : ℕ → OpenMove Y) : Follows Y σ a ↔
    ∀ n, (a (n+1)).val ⊆ (σ.move (a n) (history Y a n)).val := Iff.rfl
example (σ : SecondStrategy Y) : SecondWins Y σ ↔
    ∀ a, Follows Y σ a → (⋂ n, (σ.move (a n) (history Y a n)).val).Nonempty := Iff.rfl
example : AlphaFavorable Y ↔ ∃ σ : SecondStrategy Y, SecondWins Y σ := Iff.rfl
example (a : ℕ → OpenMove Y) : history Y a 3 = [a 2, a 1, a 0] := rfl
example (a : ℕ → OpenMove Y) (n : ℕ) : (history Y a n).length = n := history_length a n
example (a : ℕ → OpenMove Y) (n : ℕ) :
    history Y a n = (List.range n).reverse.map a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, List.range_succ, ih]
example (σ : SecondStrategy Y) (a : OpenMove Y) (h : List (OpenMove Y)) :
    (σ.move a h).val ⊆ a.val := σ.responds a h
example (a : ℕ → OpenMove Y) : (⋂ n, (a n).val).Nonempty ↔ ∃ y, ∀ n, y ∈ (a n).val := by
  simp only [Set.Nonempty, mem_iInter]
end Contracts
section MetricContracts
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
example [CompleteSpace Y] : SecondWins Y (metricStrategy (Y := Y)) := metricStrategy_wins
example [CompleteSpace Y] : AlphaFavorable Y := alphaFavorable_of_completeMetric
example [BaireSpace X] [CompleteSpace Y] : BaireSpace (X × Y) := baireSpace_prod_completeMetric
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
example : BaireSpace X ↔ ∀ D : ℕ → Set X,
    (∀ n, IsOpen (D n)) → (∀ n, Dense (D n)) → Dense (⋂ n, D n) :=
  ⟨fun h => h.baire_property, fun h => ⟨h⟩⟩
example : IsEmpty X ↔ ∀ _ : X, False :=
  ⟨fun h => h.false, fun h => ⟨h⟩⟩
example (A : Set X) : Dense A ↔
    ∀ U, IsOpen U → U.Nonempty → (U ∩ A).Nonempty := dense_iff_inter_open
example {ι : Type v} (F : Set ι) (f : ι → Set X) :
    F.PairwiseDisjoint f ↔
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (f i) (f j) := Iff.rfl
example {ι : Type v} (F : Set ι) (f : ι → Set X) :
    F.PairwiseDisjoint f ↔
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ x, x ∈ f i → x ∈ f j → False := by
  simp only [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left]
end MaterialDefinitions

section AdditionalMeanings
open Filter Topology Metric
open scoped Uniformity Topology
variable {X : Type u} [TopologicalSpace X]
example (A : Set X) : IsGδ A ↔ ∃ T : Set (Set X),
    (∀ U ∈ T, IsOpen U) ∧ T.Countable ∧ A = ⋂₀ T := Iff.rfl
example (A : Set X) : IsGδ A ↔ ∃ D : ℕ → Set X,
    (∀ n, IsOpen (D n)) ∧ A = ⋂ n, D n := isGδ_iff_eq_iInter_nat
example {Y : Type v} [TopologicalSpace Y] (S : Set (X × Y)) : IsOpen S ↔
    ∀ x y, (x,y) ∈ S → ∃ U V, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ×ˢ V ⊆ S := isOpen_prod_iff
example {Y : Type v} [TopologicalSpace Y] :
    (inferInstance : TopologicalSpace (X × Y)) =
      TopologicalSpace.induced Prod.fst inferInstance ⊓ TopologicalSpace.induced Prod.snd inferInstance := rfl
end AdditionalMeanings
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
variable [TopologicalSpace Empty]
example : AlphaFavorable Empty := alphaFavorable_of_isEmpty
example (σ : SecondStrategy Empty) : SecondWins Empty σ := by
  intro a _
  exact isEmptyElim ((a 0).property.2.choose)
end EmptyBoundary
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

-- Legal responses alone do not imply a winning strategy.
section LosingStrategyBoundary
local instance : TopologicalSpace ℕ := ⊥
local instance : DiscreteTopology ℕ := discreteTopology_bot _
example : ∃ σ : SecondStrategy ℕ, ¬ SecondWins ℕ σ := by
  let σ : SecondStrategy ℕ := ⟨fun a _ => a, fun _ _ => subset_rfl⟩
  let a : ℕ → OpenMove ℕ := fun n => ⟨{m | n ≤ m}, isOpen_discrete _, ⟨n, by simp⟩⟩
  refine ⟨σ, fun hw => ?_⟩
  have ha : Follows ℕ σ a := fun n _ hm => Nat.le_trans (Nat.le_succ n) hm
  obtain ⟨m, hm⟩ := hw a ha
  have hbad : m + 1 ≤ m := mem_iInter.mp hm (m + 1)
  omega
end LosingStrategyBoundary
