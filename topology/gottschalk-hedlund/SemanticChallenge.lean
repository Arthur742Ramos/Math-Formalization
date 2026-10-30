module
public import GHChallenge

open Function Set GottschalkHedlund

example {X : Type*} [TopologicalSpace X] [IsEmpty X] (T : X → X) (g : X → ℝ) :
    HasTransfer T g := by
  refine ⟨fun _ => 0, continuous_const, ?_⟩
  intro x
  exact isEmptyElim x

example {X : Type*} [TopologicalSpace X] [IsEmpty X] (T : X → X) (g : X → ℝ) :
    ¬ BoundedOrbitSums T g := by
  rintro ⟨x, _⟩
  exact isEmptyElim x

example : HasTransfer (id : PUnit → PUnit) (fun _ => 0) := by
  refine ⟨fun _ => 0, continuous_const, ?_⟩
  intro x
  simp

example : ¬ HasTransfer (id : PUnit → PUnit) (fun _ => 1) := by
  rintro ⟨h, _, hgh⟩
  have h := hgh PUnit.unit
  norm_num at h

example {X : Type*} [TopologicalSpace X] (T : X → X) (g : X → ℝ) (x : X) :
    birkhoffSum T g 0 x = 0 := by simp

example {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (T : X → X) (g : X → ℝ) (hT : Continuous T) (hg : Continuous g)
    (hm : ForwardMinimal T) (hb : BoundedOrbitSums T g) :
    ∃ h : X → ℝ, Continuous h ∧ (∀ x, h (T x) - h x = g x) ∧
      ∃ H : X × ℝ ≃ₜ X × ℝ, (∀ p, H p = fiberTranslation h p) ∧
        ∀ p, H (skew T g p) = (T (H p).1, (H p).2) :=
  bounded_sums_skew_conjugacy T g hT hg hm hb

example : ForwardMinimal (id : PUnit → PUnit) := by
  intro x
  change Dense (Set.range (fun n : ℕ => ((id : PUnit → PUnit)^[n]) x))
  have hrange : Set.range (fun n : ℕ => ((id : PUnit → PUnit)^[n]) x) = Set.univ := by
    ext y
    constructor
    · intro _
      exact Set.mem_univ y
    · intro _
      exact ⟨0, Subsingleton.elim _ _⟩
  rw [hrange]
  exact dense_univ

example : BoundedOrbitSums (id : PUnit → PUnit) (fun _ => 0) := by
  refine ⟨PUnit.unit, 0, le_rfl, ?_⟩
  intro n
  simp [birkhoffSum]

example : ¬ BoundedOrbitSums (id : PUnit → PUnit) (fun _ => 1) := by
  intro hb
  have hm : ForwardMinimal (id : PUnit → PUnit) := by
    intro x
    change Dense (Set.range (fun n : ℕ => ((id : PUnit → PUnit)^[n]) x))
    have hrange : Set.range (fun n : ℕ => ((id : PUnit → PUnit)^[n]) x) = Set.univ := by
      ext y
      constructor
      · intro _
        exact Set.mem_univ y
      · intro _
        exact ⟨0, Subsingleton.elim _ _⟩
    rw [hrange]
    exact dense_univ
  obtain ⟨h, _, hgh⟩ := (bounded_sums_iff_transfer (id : PUnit → PUnit)
    (fun _ => 1) continuous_id continuous_const hm).mp hb
  have contradiction := hgh PUnit.unit
  norm_num at contradiction

-- BEGIN material-imported-definition audit
example {X : Type*} [TopologicalSpace X] (T : X → X) :
    ForwardMinimal T ↔ ∀ x, Dense (Set.range (fun n : ℕ => (T^[n]) x)) := Iff.rfl

example {X : Type*} [TopologicalSpace X] (T : X → X) (g : X → ℝ) (n : ℕ) (x : X) :
    birkhoffSum T g n x = ∑ k ∈ Finset.range n, g ((T^[k]) x) := rfl

example {X : Type*} [TopologicalSpace X] (T : X → X) (g : X → ℝ) :
    HasTransfer T g ↔ ∃ h : X → ℝ, Continuous h ∧ ∀ x, h (T x) - h x = g x := Iff.rfl

example {X : Type*} [TopologicalSpace X] (T : X → X) (g : X → ℝ) :
    BoundedOrbitSums T g ↔ ∃ x : X, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |birkhoffSum T g n x| ≤ C := Iff.rfl

example {X : Type*} [TopologicalSpace X] (T : X → X) (g : X → ℝ) (p : X × ℝ) :
    skew T g p = (T p.1, p.2 + g p.1) := rfl

example {X : Type*} [TopologicalSpace X] (h : X → ℝ) (p : X × ℝ) :
    fiberTranslation h p = (p.1, p.2 - h p.1) := rfl

example {X : Type*} [TopologicalSpace X] (H : X ≃ₜ X) (x : X) :
    H.symm (H x) = x := H.symm_apply_apply x

example {X : Type*} [TopologicalSpace X] (H : X ≃ₜ X) (x : X) :
    H (H.symm x) = x := H.apply_symm_apply x

example {X : Type*} [TopologicalSpace X] (H : X ≃ₜ X) : Continuous H := H.continuous_toFun
-- END material-imported-definition audit
