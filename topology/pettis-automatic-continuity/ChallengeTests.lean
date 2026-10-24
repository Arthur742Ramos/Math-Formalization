module
public import PettisChallenge
public section
open Set Filter TopologicalSpace
open scoped Topology Pointwise symmDiff
#check PettisAutomatic.mul_inv_mem_nhds_one
#check PettisAutomatic.continuous_of_baire_preimages
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
    {A : Set G} (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    A * A⁻¹ ∈ 𝓝 (1 : G) := PettisAutomatic.mul_inv_mem_nhds_one hA hn
example {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SeparableSpace H]
    (f : G →* H) (h : ∀ U : Set H, IsOpen U → BaireMeasurableSet (f ⁻¹' U)) :
    Continuous f := PettisAutomatic.continuous_of_baire_preimages f h
-- BEGIN material-imported-definition audit
example {G H : Type*} [TopologicalSpace G] [TopologicalSpace H] (f : G → H) :
    PettisAutomatic.BPPreimages f ↔ ∀ U : Set H, IsOpen U → BaireMeasurableSet (f ⁻¹' U) := Iff.rfl
example {G H : Type*} [Group G] [Group H] (f : G →* H) :
    f 1 = 1 ∧ ∀ x y, f (x*y) = f x * f y := ⟨f.map_one, f.map_mul⟩
example {G : Type*} [Group G] : ∀ x : G, x⁻¹*x=1 := inv_mul_cancel
example {G : Type*} [Group G] : ∀ x y z : G, (x*y)*z=x*(y*z) := mul_assoc
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Continuous (fun p : G × G => p.1*p.2) ∧ Continuous (fun x : G => x⁻¹) :=
  ⟨continuous_mul, continuous_inv⟩
example {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] :
    (inferInstance : TopologicalSpace (X × Y)) =
      TopologicalSpace.induced Prod.fst tX ⊓ TopologicalSpace.induced Prod.snd tY := rfl
example {H : Type*} [TopologicalSpace H] [SeparableSpace H] :
    ∃ D : Set H, D.Countable ∧ Dense D := exists_countable_dense H
example {G : Type*} [Group G] (A : Set G) (z : G) :
    z ∈ A*A⁻¹ ↔ ∃ a ∈ A, ∃ b ∈ A, a*b⁻¹=z := by
  simp only [Set.mem_mul, Set.mem_inv]
  constructor
  · rintro ⟨a, ha, c, hc, hz⟩
    exact ⟨a, ha, c⁻¹, hc, by simpa using hz⟩
  · rintro ⟨a, ha, b, hb, hz⟩
    exact ⟨a, ha, b⁻¹, by simpa, hz⟩
example {X : Type*} [TopologicalSpace X] (A : Set X) (x : X) :
    A ∈ 𝓝 x ↔ ∃ U ⊆ A, IsOpen U ∧ x ∈ U := mem_nhds_iff
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X : Type*} [TopologicalSpace X] [BaireSpace X] {U : Set X}
    (ho : IsOpen U) (hne : U.Nonempty) : ¬ IsMeagre U := not_isMeagre_of_isOpen ho hne
example {X : Type*} [TopologicalSpace X] (A : Set X) : IsMeagre A ↔ Aᶜ ∈ residual X := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : IsNowhereDense A ↔ interior (closure A) = ∅ := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
example {X : Type*} [TopologicalSpace X] (A : Set X) :
    BaireMeasurableSet A ↔
      @MeasurableSet X (eventuallyMeasurableSpace (borel X) (residual X)) A := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) :
    BaireMeasurableSet A ↔ ∃ O : Set X, IsOpen O ∧ IsMeagre (A ∆ O) := by
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  constructor
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, ?_⟩
    change ∀ᶠ x in residual X, x ∉ A ∆ O
    filter_upwards [hAO.mem_iff] with x hx
    simp only [mem_symmDiff]
    tauto
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, Filter.eventuallyEqSet_iff.mpr ?_⟩
    change ∀ᶠ x in residual X, x ∉ A ∆ O at hAO
    filter_upwards [hAO] with x hx
    simp only [mem_symmDiff] at hx
    tauto
-- END material-imported-definition audit
