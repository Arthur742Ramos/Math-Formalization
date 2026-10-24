module
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Tactic

/-! A direct pointwise metric Auslander–Yorke argument. Minimal's literal dense-orbit
definition is retained from campaign source2fae123, WeakMixingMinimal.lean.
No compactness or uniform-equicontinuity assertion is used. -/
@[expose] public section
open Set Function Metric
namespace AuslanderYorke

/-- Every forward natural orbit, including time zero, is dense. -/
def Minimal {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ x, Dense (range (fun n : ℕ => f^[n] x))

/-- One positive constant separates some pair in every nonempty open set.
On an empty space this open-set convention is vacuously true. -/
def Sensitive {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ U : Set X, IsOpen U → U.Nonempty →
    ∃ n : ℕ, ∃ a ∈ U, ∃ b ∈ U, δ < dist (f^[n] a) (f^[n] b)

/-- Stable open sets propagate to every point using dense orbits and finitely many early times. -/
theorem equicontinuous_of_stable_open_sets {X : Type*} [MetricSpace X]
    (f : X → X) (hf : Continuous f) (hm : Minimal f)
    (hstable : ∀ ε : ℝ, 0 < ε → ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∀ n : ℕ, ∀ a ∈ U, ∀ b ∈ U, dist (f^[n] a) (f^[n] b) ≤ ε) :
    Equicontinuous (fun n : ℕ => f^[n]) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨U, hU, hnU, hsmall⟩ := hstable (ε/2) (by positivity)
  obtain ⟨z, hzU, k, rfl⟩ := (hm x).inter_open_nonempty U hU hnU
  let V : Set X := (f^[k]) ⁻¹' U ∩
    ⋂ j ∈ Finset.range k, (f^[j]) ⁻¹' ball (f^[j] x) ε
  have hV : IsOpen V := (hU.preimage (hf.iterate k)).inter
    (isOpen_biInter_finset fun j _ => isOpen_ball.preimage (hf.iterate j))
  have hxV : x ∈ V := by
    refine ⟨hzU, ?_⟩
    simp only [mem_iInter, mem_preimage, mem_ball, dist_self]
    exact fun _ _ => hε
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
  refine ⟨δ, hδ, ?_⟩
  intro y hy n
  have hyV := hδV hy
  by_cases hn : n < k
  · have hearly := mem_iInter.mp (mem_iInter.mp hyV.2 n) (Finset.mem_range.mpr hn)
    simpa only [mem_preimage, mem_ball, dist_comm] using hearly
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k ≤ n)
    have htail := hsmall r (f^[k] x) hzU (f^[k] y) hyV.1
    have hbound : dist (f^[k+r] x) (f^[k+r] y) ≤ ε/2 := by
      rw [Nat.add_comm k r]
      simpa only [iterate_add_apply] using htail
    linarith

/-- The unrestricted disjunction; on an empty space both alternatives hold. -/
theorem minimal_dichotomy {X : Type*} [MetricSpace X]
    (f : X → X) (hf : Continuous f) (hm : Minimal f) :
    Sensitive f ∨ Equicontinuous (fun n : ℕ => f^[n]) := by
  by_cases hs : Sensitive f
  · exact Or.inl hs
  · right
    apply equicontinuous_of_stable_open_sets f hf hm
    unfold Sensitive at hs
    push Not at hs
    exact hs

/-- Nonemptiness makes sensitivity exactly the failure of equicontinuity in a minimal system. -/
theorem minimal_not_sensitive_iff_equicontinuous {X : Type*} [MetricSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hm : Minimal f) :
    ¬ Sensitive f ↔ Equicontinuous (fun n : ℕ => f^[n]) := by
  constructor
  · intro hs
    exact (minimal_dichotomy f hf hm).resolve_left hs
  · intro he hs
    obtain ⟨δ, hδ, hsep⟩ := hs
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨η, hη, hηbound⟩ := Metric.equicontinuousAt_iff.mp (he x) (δ/2) (by positivity)
    obtain ⟨n, a, ha, b, hb, hab⟩ := hsep (ball x η) isOpen_ball (nonempty_ball.mpr hη)
    have ha' := hηbound a ha n
    have hb' := hηbound b hb n
    have ht := dist_triangle (f^[n] a) (f^[n] x) (f^[n] b)
    rw [dist_comm (f^[n] a) (f^[n] x)] at ht
    linarith

end AuslanderYorke
