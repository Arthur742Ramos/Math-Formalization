module
public import Mycielski.Scheme

public section
namespace Mycielski
open Set TopologicalSpace Metric CantorScheme Filter Function
open scoped Topology ENNReal

/-- The binary single-Cantor fusion theorem in a complete perfect metric space.
Completeness is kept on the ambient space when localizing inside an open set. -/
theorem exists_independent_metric {X : Type*} [MetricSpace X] [CompleteSpace X]
    [PerfectSpace X] {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty)
    (R : ℕ → Set (X × X)) (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k)) :
    ∃ e : CantorSpace → X, range e ⊆ U ∧ Continuous e ∧ Injective e ∧
      ∀ s t, s ≠ t → ∀ k, (e s, e t) ∈ R k := by
  obtain ⟨u, -, upos, hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  have hupos : ∀ n, 0 < u n := fun n => (upos n).1
  let L := stages hoR hdR hupos hU hneU
  let A : List Bool → Set X := fun l => (L l.length).cell ⟨l, rfl⟩
  have hcell (l : List Bool) (n : ℕ) (h : l.length = n) :
      A l = (L n).cell ⟨l, h⟩ := by
    subst n
    rfl
  have hanti : ClosureAntitone A := by
    intro l a
    exact stages_refine hoR hdR hupos hU hneU l.length ⟨a :: l, rfl⟩
  have hdiam : VanishingDiam A := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hm := (L n).small (⟨PiNat.res x n, PiNat.res_length x n⟩ : Node n) (by omega)
    rw [hcell _ n (PiNat.res_length x n)]
    exact hm
  have hdisj : CantorScheme.Disjoint A := by
    intro l a b hab
    have hnode : (⟨a :: l, rfl⟩ : Node (l.length + 1)) ≠ ⟨b :: l, rfl⟩ := by
      intro h
      apply hab
      exact (List.cons.inj (congrArg Subtype.val h)).1
    exact ((L (l.length + 1)).separate _ _ hnode).mono subset_closure subset_closure
  have hnonempty : ∀ l, (A l).Nonempty := fun l => (L l.length).nonempty_cell _
  have hdom : ∀ x : ℕ → Bool, x ∈ (inducedMap A).1 := by
    intro x
    rw [hanti.map_of_vanishingDiam hdiam hnonempty]
    exact mem_univ x
  let e : (ℕ → Bool) → X := fun x => (inducedMap A).2 ⟨x, hdom x⟩
  have hmem (x : ℕ → Bool) (n : ℕ) :
      e x ∈ (L n).cell ⟨PiNat.res x n, PiNat.res_length x n⟩ := by
    have hm := map_mem (⟨x, hdom x⟩ : (inducedMap A).1) n
    rw [hcell _ n (PiNat.res_length x n)] at hm
    exact hm
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact hmem x 0
  · exact hdiam.map_continuous.comp (by fun_prop)
  · intro s t hst
    simpa only [← Subtype.val_inj] using hdisj.map_injective hst
  · intro s t hst k
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
    let n := max (i + 1) (k + 1)
    have hin : i < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    have hnode : (⟨PiNat.res s n, PiNat.res_length s n⟩ : Node n) ≠
        ⟨PiNat.res t n, PiNat.res_length t n⟩ := by
      intro h
      exact hi (PiNat.res_eq_res.mp (congrArg Subtype.val h) hin)
    exact (L n).relation _ _ hnode k hkn ⟨subset_closure (hmem s n), subset_closure (hmem t n)⟩

/-- **Mycielski's binary Cantor independent-set theorem, localized form.**
Every nonempty open subset of a perfect Polish space contains a Cantor copy
whose ordered distinct pairs lie in each prescribed dense-open binary relation.
No symmetry, diagonal-membership or fusion-existence hypothesis is imposed. -/
theorem exists_cantor_independent {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [PerfectSpace X] {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty)
    (R : ℕ → Set (X × X)) (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k)) :
    ∃ e : CantorSpace → X, Topology.IsClosedEmbedding e ∧ range e ⊆ U ∧
      ∀ s t, s ≠ t → ∀ k, (e s, e t) ∈ R k := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  obtain ⟨e, heU, hcont, hinj, hrel⟩ := exists_independent_metric hU hneU R hoR hdR
  exact ⟨e, hcont.isClosedEmbedding hinj, heU, hrel⟩

end Mycielski
