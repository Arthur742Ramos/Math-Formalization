module
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Tactic


public section
namespace Mycielski
open Set TopologicalSpace Metric
open scoped Topology
open scoped ENNReal

abbrev CantorSpace := ℕ → Bool

variable {X : Type*} [MetricSpace X]

/-- Joint evaluation at two distinct coordinates is an open map. -/
theorem pair_eval_open {I : Type*} (i j : I) (hij : i ≠ j) :
    IsOpenMap (fun z : I → X => (z i, z j)) := by
  classical
  let j' : {k : I // k ≠ i} := ⟨j, hij.symm⟩
  let e := Homeomorph.funSplitAt (Y := X) i
  have h := ((IsOpenMap.id : IsOpenMap (id : X → X)).prodMap
    (isOpenMap_eval (X := fun _ : {k : I // k ≠ i} => X) j')).comp e.isOpenMap
  convert h using 1
  ext z <;> simp [e, j', Homeomorph.funSplitAt, Homeomorph.piSplitAt, Equiv.piSplitAt]

theorem open_exists_mem_ne [PerfectSpace X] {V : Set X}
    (hV : IsOpen V) (hne : V.Nonempty) (a : X) : ∃ b ∈ V, b ≠ a := by
  obtain ⟨v, hv⟩ := hne
  by_cases h : v = a
  · subst v
    obtain ⟨b, hb, hba⟩ := (preperfect_iff_nhds.mp hV.preperfect) a hv V (hV.mem_nhds hv)
    exact ⟨b, hb.1, hba⟩
  · exact ⟨v, hv, h⟩

theorem off_diagonal_dense [PerfectSpace X] :
    Dense {p : X × X | p.1 ≠ p.2} := by
  apply dense_iff_inter_open.mpr
  intro W hW hneW
  obtain ⟨⟨a, b⟩, hab⟩ := hneW
  obtain ⟨U, V, hU, hV, ha, hb, hsub⟩ := isOpen_prod_iff.mp hW a b hab
  obtain ⟨c, hc, hca⟩ := open_exists_mem_ne hV ⟨b, hb⟩ a
  exact ⟨(a, c), hsub ⟨ha, hc⟩, hca.symm⟩

/-- Simultaneously choose finitely many independent points in prescribed opens.
All ordered distinct coordinate pairs satisfy the relation. -/
theorem finite_good_tuple [CompleteSpace X] [PerfectSpace X]
    {I : Type*} [Fintype I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    {W : Set (X × X)} (hW : IsOpen W) (hdW : Dense W) :
    ∃ z : I → X, (∀ i, z i ∈ U i) ∧
      ∀ i j, i ≠ j → (z i, z j) ∈ W ∧ z i ≠ z j := by
  classical
  let P := {p : I × I // p.1 ≠ p.2}
  let D : Set (X × X) := W ∩ {p | p.1 ≠ p.2}
  have hneDiag : IsOpen {p : X × X | p.1 ≠ p.2} :=
    (isClosed_eq continuous_fst continuous_snd).isOpen_compl
  have hD : IsOpen D := hW.inter hneDiag
  have hdD : Dense D := hdW.inter_of_isOpen_right off_diagonal_dense
    hneDiag
  let B : Set (I → X) := ⋂ p : P, (fun z => (z p.val.1, z p.val.2)) ⁻¹' D
  have hoB : IsOpen B := isOpen_iInter_of_finite fun p =>
    hD.preimage ((continuous_apply p.val.1).prodMk (continuous_apply p.val.2))
  have hdB : Dense B := dense_iInter_of_isOpen
    (fun p => hD.preimage ((continuous_apply p.val.1).prodMk (continuous_apply p.val.2)))
    (fun p => hdD.preimage (pair_eval_open p.val.1 p.val.2 p.property))
  have hoU : IsOpen {z : I → X | ∀ i, z i ∈ U i} := by
    convert isOpen_iInter_of_finite (fun i => (hU i).preimage (continuous_apply i)) using 1
    ext z
    simp
  choose u hu using hne
  obtain ⟨z, hzB, hzU⟩ := hdB.exists_mem_open hoU ⟨u, hu⟩
  refine ⟨z, hzU, fun i j hij => ?_⟩
  exact Set.mem_iInter.mp hzB (⟨(i, j), hij⟩ : P)

/-- Coordinated shrinking of finitely many cells. Cross-relations are imposed
on every ordered pair of distinct cells, including cells with different parents. -/
theorem finite_refinement [CompleteSpace X] [PerfectSpace X]
    {I : Type*} [Fintype I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    {W : Set (X × X)} (hW : IsOpen W) (hdW : Dense W)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : I → Set X,
      (∀ i, IsOpen (T i) ∧ (T i).Nonempty ∧ closure (T i) ⊆ U i ∧ ediam (T i) ≤ ε) ∧
      ∀ i j, i ≠ j → Disjoint (closure (T i)) (closure (T j)) ∧
        closure (T i) ×ˢ closure (T j) ⊆ W := by
  classical
  obtain ⟨z, hzU, hzW⟩ := finite_good_tuple U hU hne hW hdW
  let P := {p : I × I // p.1 ≠ p.2}
  let D : Set (X × X) := W ∩ {p | p.1 ≠ p.2}
  let G : Set (I → X) := (⋂ i, (fun w => w i) ⁻¹' U i) ∩
    ⋂ p : P, (fun w => (w p.val.1, w p.val.2)) ⁻¹' D
  have hG : IsOpen G :=
    (isOpen_iInter_of_finite fun i => (hU i).preimage (continuous_apply i)).inter
      (isOpen_iInter_of_finite fun p =>
        (hW.inter (isClosed_eq continuous_fst continuous_snd).isOpen_compl).preimage
          ((continuous_apply p.val.1).prodMk (continuous_apply p.val.2)))
  have hzG : z ∈ G := ⟨mem_iInter.mpr hzU,
    mem_iInter.mpr fun p => hzW p.val.1 p.val.2 p.property⟩
  obtain ⟨J, Q, hQ, hbox⟩ := isOpen_pi_iff.mp hG z hzG
  let V : I → Set X := fun i => if i ∈ J then Q i else univ
  have hV : ∀ i, IsOpen (V i) ∧ z i ∈ V i := by
    intro i
    by_cases hi : i ∈ J
    · simpa [V, hi] using hQ i hi
    · simp [V, hi]
  have hall (w : I → X) (hw : ∀ i, w i ∈ V i) :
      (∀ i, w i ∈ U i) ∧ ∀ i j, i ≠ j → (w i, w j) ∈ W ∧ w i ≠ w j := by
    have hwG : w ∈ G := hbox fun i hi => by
      change i ∈ J at hi
      simpa [V, hi] using hw i
    exact ⟨fun i => mem_iInter.mp hwG.1 i,
      fun i j hij => mem_iInter.mp hwG.2 (⟨(i, j), hij⟩ : P)⟩
  have hshrink : ∀ i, ∃ S : Set X, IsOpen S ∧ z i ∈ S ∧ closure S ⊆ V i := by
    intro i
    exact isTopologicalBasis_opens.exists_closure_subset ((hV i).1.mem_nhds (hV i).2)
  choose S hSo hzS hSV using hshrink
  let T : I → Set X := fun i => S i ∩ Metric.eball (z i) (ε / 2)
  have hTV : ∀ i, closure (T i) ⊆ V i := fun i =>
    (closure_mono inter_subset_left).trans (hSV i)
  have hupdate (i : I) (x : X) (hx : x ∈ closure (T i)) :
      ∀ k, Function.update z i x k ∈ V k := by
    intro k
    by_cases hk : k = i
    · subst k; simpa using hTV i hx
    · simpa [Function.update, hk] using (hV k).2
  have hcross (i j : I) (hij : i ≠ j) {x y : X}
      (hx : x ∈ closure (T i)) (hy : y ∈ closure (T j)) :
      (x, y) ∈ W ∧ x ≠ y := by
    have hm : ∀ k, Function.update (Function.update z i x) j y k ∈ V k := by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using hTV j hy
      · simpa [Function.update, hkj] using hupdate i x hx k
    have hc := (hall _ hm).2 i j hij
    simpa [Function.update, hij, hij.symm] using hc
  refine ⟨T, fun i => ⟨(hSo i).inter Metric.isOpen_eball, ?_, ?_, ?_⟩,
    fun i j hij => ⟨?_, ?_⟩⟩
  · refine ⟨z i, hzS i, Metric.mem_eball_self ?_⟩
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt hε, by norm_num⟩
  · intro x hx
    have hm := (hall _ (hupdate i x hx)).1 i
    simpa using hm
  · calc
      ediam (T i) ≤ ediam (Metric.eball (z i) (ε / 2)) := ediam_mono inter_subset_right
      _ ≤ 2 * (ε / 2) := Metric.ediam_eball_le
      _ = ε := by rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num
  · exact Set.disjoint_left.mpr fun x hxi hxj => (hcross i j hij hxi hxj).2 rfl
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact (hcross i j hij hx hy).1

end Mycielski


public section
namespace Mycielski
open Set TopologicalSpace Metric CantorScheme Filter Function
open scoped Topology ENNReal

abbrev Node (n : ℕ) := List.Vector Bool n

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [PerfectSpace X]

structure Stage (R : ℕ → Set (X × X)) (u : ℕ → ℝ≥0∞) (n : ℕ) where
  cell : Node n → Set X
  open_cell : ∀ s, IsOpen (cell s)
  nonempty_cell : ∀ s, (cell s).Nonempty
  separate : ∀ s t, s ≠ t → Disjoint (closure (cell s)) (closure (cell t))
  small : ∀ s, 0 < n → ediam (cell s) ≤ u n
  relation : ∀ s t, s ≠ t → ∀ k < n, closure (cell s) ×ˢ closure (cell t) ⊆ R k

@[expose] def initialStage (R : ℕ → Set (X × X)) (u : ℕ → ℝ≥0∞)
    {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty) : Stage R u 0 where
  cell _ := U
  open_cell _ := hU
  nonempty_cell _ := hneU
  separate s t h := (h (Subsingleton.elim s t)).elim
  small _ h := by omega
  relation _ _ _ _ h := by omega

theorem stage_refinement {R : ℕ → Set (X × X)} {u : ℕ → ℝ≥0∞}
    (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k))
    (hu : ∀ n, 0 < u n) {n : ℕ} (S : Stage R u n) :
    ∃ T : Stage R u (n + 1), ∀ s : Node (n + 1), closure (T.cell s) ⊆ S.cell s.tail := by
  let W : Set (X × X) := ⋂ k : Fin (n + 1), R k
  have hoW : IsOpen W := isOpen_iInter_of_finite fun k => hoR k
  have hdW : Dense W := dense_iInter_of_isOpen (fun k => hoR k) (fun k => hdR k)
  obtain ⟨T, hT, hcross⟩ := finite_refinement (fun s : Node (n + 1) => S.cell s.tail)
    (fun s => S.open_cell s.tail) (fun s => S.nonempty_cell s.tail) hoW hdW (hu (n + 1))
  refine ⟨⟨T, fun s => (hT s).1, fun s => (hT s).2.1,
    fun s t hst => (hcross s t hst).1,
    fun s _ => (hT s).2.2.2, ?_⟩, fun s => (hT s).2.2.1⟩
  intro s t hst k hk p hp
  exact mem_iInter.mp ((hcross s t hst).2 hp) (⟨k, hk⟩ : Fin (n + 1))

@[expose] noncomputable def stages {R : ℕ → Set (X × X)} {u : ℕ → ℝ≥0∞}
    (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k)) (hu : ∀ n, 0 < u n)
    {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty) : ∀ n, Stage R u n
  | 0 => initialStage R u hU hneU
  | n + 1 => (stage_refinement hoR hdR hu (stages hoR hdR hu hU hneU n)).choose

theorem stages_refine {R : ℕ → Set (X × X)} {u : ℕ → ℝ≥0∞}
    (hoR : ∀ k, IsOpen (R k)) (hdR : ∀ k, Dense (R k)) (hu : ∀ n, 0 < u n)
    {U : Set X} (hU : IsOpen U) (hneU : U.Nonempty) (n : ℕ) (s : Node (n + 1)) :
    closure ((stages hoR hdR hu hU hneU (n + 1)).cell s) ⊆
      (stages hoR hdR hu hU hneU n).cell s.tail :=
  (stage_refinement hoR hdR hu (stages hoR hdR hu hU hneU n)).choose_spec s

end Mycielski


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
