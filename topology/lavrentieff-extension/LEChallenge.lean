/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0 license.
Substantive formalization and proof engineering: OpenAI Codex.
Classical result: M. M. Lavrentieff (1924); modern complete-metric formulation.
-/
module
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section
open Set Filter Topology Metric TopologicalSpace
namespace Lavrentieff
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Points admitting an open neighborhood on which the image has small diameter. -/
def smallOscillation (s : Set X) (f : X → Y) (ε : ℝ) : Set X :=
  ⋃ (U : Set X) (_ : IsOpen U)
    (_ : ∀ a ∈ U ∩ s, ∀ b ∈ U ∩ s, dist (f a) (f b) < ε), U

lemma isOpen_smallOscillation (s : Set X) (f : X → Y) (ε : ℝ) :
    IsOpen (smallOscillation s f ε) := by
  apply isOpen_iUnion; intro U
  apply isOpen_iUnion; intro hU
  apply isOpen_iUnion; intro _
  exact hU

lemma mem_smallOscillation_iff {s : Set X} {f : X → Y} {ε : ℝ} {x : X} :
    x ∈ smallOscillation s f ε ↔
      ∃ U, IsOpen U ∧ x ∈ U ∧
        ∀ a ∈ U ∩ s, ∀ b ∈ U ∩ s, dist (f a) (f b) < ε := by
  simp only [smallOscillation, mem_iUnion]
  aesop

/-- The zero-oscillation locus inside the original domain's closure. -/
def extensionDomain (s : Set X) (f : X → Y) : Set X :=
  closure s ∩ ⋂ n : ℕ, smallOscillation s f ((n + 1 : ℝ)⁻¹)

lemma extensionDomain_isGδ (s : Set X) (f : X → Y) : IsGδ (extensionDomain s f) :=
  isClosed_closure.isGδ.inter (IsGδ.iInter_of_isOpen fun _ => isOpen_smallOscillation _ _ _)

lemma subset_extensionDomain {s : Set X} {f : X → Y} (hf : ContinuousOn f s) :
    s ⊆ extensionDomain s f := by
  intro x hx
  refine ⟨subset_closure hx, mem_iInter.2 fun n => ?_⟩
  have he : 0 < (n + 1 : ℝ)⁻¹ := inv_pos.2 (by positivity)
  obtain ⟨U, ⟨hxU, hU⟩, hUf⟩ :=
    (nhdsWithin_basis_open x s).tendsto_left_iff.1 (hf x hx)
      (ball (f x) ((n + 1 : ℝ)⁻¹ / 2)) (ball_mem_nhds _ (by positivity))
  apply mem_smallOscillation_iff.2 ⟨U, hU, hxU, ?_⟩
  intro a ha b hb
  have ha' := mem_ball.1 (hUf ha)
  have hb' := mem_ball.1 (hUf hb)
  calc dist (f a) (f b) ≤ dist (f a) (f x) + dist (f b) (f x) := dist_triangle_right ..
       _ < (n + 1 : ℝ)⁻¹ := by linarith

lemma cauchy_at_extensionDomain {s : Set X} {f : X → Y} {x : X}
    (hx : x ∈ extensionDomain s f) : Cauchy (map f (𝓝[s] x)) := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx.1
  refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hn' : (n + 1 : ℝ)⁻¹ < ε := by simpa [one_div] using hn
  obtain ⟨U, hU, hxU, hUf⟩ := mem_smallOscillation_iff.1 (mem_iInter.1 hx.2 n)
  refine ⟨f '' (U ∩ s), ?_, ?_⟩
  · exact mem_map.2 (mem_of_superset (inter_mem_nhdsWithin s (hU.mem_nhds hxU))
      fun a ha => mem_preimage.2 (mem_image_of_mem f ⟨ha.2, ha.1⟩))
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (hUf a ha b hb).trans hn'

/-- Every continuous map to a complete metric space extends to a Gδ superset
of its arbitrary domain, contained in that domain's closure. -/
theorem continuous_extension [CompleteSpace Y] {s : Set X} {f : X → Y}
    (hf : ContinuousOn f s) :
    ∃ D : Set X, IsGδ D ∧ s ⊆ D ∧ D ⊆ closure s ∧
      ∃ F : X → Y, ContinuousOn F D ∧ EqOn F f s := by
  refine ⟨extensionDomain s f, extensionDomain_isGδ s f, subset_extensionDomain hf,
    fun _ hx => hx.1, extendFrom s f, ?_, extendFrom_extends hf⟩
  apply continuousOn_extendFrom (fun _ hx => hx.1)
  intro x hx
  have := mem_closure_iff_nhdsWithin_neBot.1 hx.1
  exact cauchy_map_iff_exists_tendsto.1 (cauchy_at_extensionDomain hx)

/-- A relative Gδ preimage under a map continuous only on a Gδ domain is
Gδ in the ambient space. -/
theorem isGδ_inter_preimage {D : Set X} {E : Set Y} {F : X → Y}
    (hD : IsGδ D) (hE : IsGδ E) (hF : ContinuousOn F D) :
    IsGδ (D ∩ F ⁻¹' E) := by
  obtain ⟨U, hU, rfl⟩ := hE.eq_iInter_nat
  choose V hV heq using fun n => continuousOn_iff'.1 hF (U n) (hU n)
  have he : D ∩ F ⁻¹' (⋂ n, U n) = D ∩ ⋂ n, V n := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iInter]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun n => (show x ∈ V n ∩ D from (heq n) ▸ ⟨h n, hx⟩).1⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun n => (show x ∈ F ⁻¹' U n ∩ D from (heq n).symm ▸ ⟨h n, hx⟩).1⟩
  rw [he]
  exact hD.inter (IsGδ.iInter_of_isOpen hV)

/-- Gluing two continuous extensions recovers mutually inverse maps on
ambient Gδ domains. No uniform continuity or separability is assumed. -/
theorem extend_inverse_maps [CompleteSpace X] [CompleteSpace Y]
    {s : Set X} {t : Set Y} {f : X → Y} {g : Y → X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g t)
    (hft : MapsTo f s t) (hgs : MapsTo g t s)
    (hgf : LeftInvOn g f s) (hfg : LeftInvOn f g t) :
    ∃ (B : Set X) (C : Set Y) (hsB : s ⊆ B), IsGδ B ∧ IsGδ C ∧ t ⊆ C ∧
      B ⊆ closure s ∧ C ⊆ closure t ∧
      ∃ H : B ≃ₜ C, ∀ x : s, (H ⟨x, hsB x.property⟩ : Y) = f x := by
  obtain ⟨D, hD, hsD, hDs, F, hF, hFf⟩ := continuous_extension hf
  obtain ⟨E, hE, htE, hEt, G, hG, hGg⟩ := continuous_extension hg
  let B := D ∩ F ⁻¹' E
  let C := E ∩ G ⁻¹' D
  have hsB : s ⊆ B := fun x hx => ⟨hsD hx, by change F x ∈ E; rw [hFf hx]; exact htE (hft hx)⟩
  have htC : t ⊆ C := fun y hy => ⟨htE hy, by change G y ∈ D; rw [hGg hy]; exact hsD (hgs hy)⟩
  have hBF : MapsTo F B E := fun _ hx => hx.2
  have hCG : MapsTo G C D := fun _ hy => hy.2
  have hGF : EqOn (G ∘ F) id B := by
    apply Set.EqOn.of_subset_closure (s := s) _
      (hG.comp (hF.mono inter_subset_left) hBF) continuousOn_id hsB
      (fun _ hx => hDs hx.1)
    intro x hx
    simp only [Function.comp_apply, id_eq, hFf hx, hGg (hft hx)]
    exact hgf hx
  have hFG : EqOn (F ∘ G) id C := by
    apply Set.EqOn.of_subset_closure (s := t) _
      (hF.comp (hG.mono inter_subset_left) hCG) continuousOn_id htC
      (fun _ hy => hEt hy.1)
    intro y hy
    simp only [Function.comp_apply, id_eq, hGg hy, hFf (hgs hy)]
    exact hfg hy
  have hFC : MapsTo F B C := fun x hx => ⟨hx.2, by
    change G (F x) ∈ D
    rw [show G (F x) = x from hGF hx]
    exact hx.1⟩
  have hGB : MapsTo G C B := fun y hy => ⟨hy.2, by
    change F (G y) ∈ E
    rw [show F (G y) = y from hFG hy]
    exact hy.1⟩
  let H : B ≃ₜ C :=
    { toFun := fun x => ⟨F x, hFC x.property⟩
      invFun := fun y => ⟨G y, hGB y.property⟩
      left_inv := fun x => Subtype.ext (hGF x.property)
      right_inv := fun y => Subtype.ext (hFG y.property)
      continuous_toFun := (hF.mono inter_subset_left).mapsToRestrict hFC
      continuous_invFun := (hG.mono inter_subset_left).mapsToRestrict hGB }
  exact ⟨B, C, hsB, isGδ_inter_preimage hD hE hF, isGδ_inter_preimage hE hD hG,
    htC, fun _ hx => hDs hx.1, fun _ hy => hEt hy.1,
    H, fun x => hFf x.property⟩

/-- Lavrentieff's extension theorem in complete metric spaces, including empty
subsets. The extension agrees pointwise with the supplied homeomorphism. -/
theorem homeomorph_extension [CompleteSpace X] [CompleteSpace Y]
    {s : Set X} {t : Set Y} (h : s ≃ₜ t) :
    ∃ (B : Set X) (C : Set Y) (hsB : s ⊆ B),
      IsGδ B ∧ IsGδ C ∧ t ⊆ C ∧ B ⊆ closure s ∧ C ⊆ closure t ∧
      ∃ H : B ≃ₜ C, ∀ x : s, (H ⟨x, hsB x.property⟩ : Y) = (h x : Y) := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hs
    let f : X → Y := fun x => if hx : x ∈ s then (h ⟨x, hx⟩ : Y) else (h ⟨x₀, hx₀⟩ : Y)
    let g : Y → X := fun y => if hy : y ∈ t then (h.symm ⟨y, hy⟩ : X) else x₀
    have hfx (x : s) : f x = (h x : Y) := by simp [f, x.property]
    have hgy (y : t) : g y = (h.symm y : X) := by simp [g, y.property]
    have hf : ContinuousOn f s := by
      apply continuousOn_iff_continuous_domRestrict.2
      have he : s.domRestrict f = fun x => (h x : Y) := funext hfx
      rw [he]
      exact continuous_subtype_val.comp h.continuous
    have hg : ContinuousOn g t := by
      apply continuousOn_iff_continuous_domRestrict.2
      have he : t.domRestrict g = fun y => (h.symm y : X) := funext hgy
      rw [he]
      exact continuous_subtype_val.comp h.symm.continuous
    have hft : MapsTo f s t := fun x hx => by rw [hfx ⟨x, hx⟩]; exact (h ⟨x, hx⟩).property
    have hgs : MapsTo g t s := fun y hy => by rw [hgy ⟨y, hy⟩]; exact (h.symm ⟨y, hy⟩).property
    have hgf : LeftInvOn g f s := by
      intro x hx
      change g (f (⟨x, hx⟩ : s)) = x
      rw [hfx, hgy]
      exact congrArg Subtype.val (h.symm_apply_apply ⟨x, hx⟩)
    have hfg : LeftInvOn f g t := by
      intro y hy
      change f (g (⟨y, hy⟩ : t)) = y
      rw [hgy, hfx]
      exact congrArg Subtype.val (h.apply_symm_apply ⟨y, hy⟩)
    obtain ⟨B, C, hsB, hB, hC, htC, hBs, hCt, H, hH⟩ :=
      extend_inverse_maps hf hg hft hgs hgf hfg
    exact ⟨B, C, hsB, hB, hC, htC, hBs, hCt, H, fun x => (hH x).trans (hfx x)⟩
  · have hs' : s = ∅ := not_nonempty_iff_eq_empty.1 hs
    have ht' : t = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro y hy
      have := (h.symm ⟨y, hy⟩).property
      simp [hs'] at this
    refine ⟨s, t, Subset.rfl, ?_, ?_, Subset.rfl, subset_closure, subset_closure,
      h, fun _ => rfl⟩ <;> simp [hs', ht']
end Lavrentieff

namespace Lavrentieff
/-- The topological, metric-independent form: compatible complete metrizability
is sufficient; a complete metric need not have been chosen in advance. -/
theorem completely_metrizable_extension {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace X] [IsCompletelyMetrizableSpace Y]
    {s : Set X} {t : Set Y} (h : s ≃ₜ t) :
    ∃ (B : Set X) (C : Set Y) (hsB : s ⊆ B),
      IsGδ B ∧ IsGδ C ∧ t ⊆ C ∧ B ⊆ closure s ∧ C ⊆ closure t ∧
      ∃ H : B ≃ₜ C, ∀ x : s, (H ⟨x, hsB x.property⟩ : Y) = (h x : Y) := by
  let := upgradeIsCompletelyMetrizable X
  let := upgradeIsCompletelyMetrizable Y
  exact homeomorph_extension h
end Lavrentieff
