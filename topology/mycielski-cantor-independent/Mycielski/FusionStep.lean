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
