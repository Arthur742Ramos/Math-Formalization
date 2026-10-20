/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. Released under Apache 2.0.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
Material Lean proof authorship: OpenAI Codex.
Strategy lifting follows Dorais–Mummert, arXiv:0907.4126v2, Proposition 3.2.
Polish image conclusion: Chen, Notes on quasi-Polish spaces, Section 10,
recalling Kechris 8.19. No novelty or priority claimed.
-/
module
public import StrongChoquetFoundation
public import Mathlib.Topology.Metrizable.Urysohn
public section
open Set Topology TopologicalSpace
namespace OpenPolish
open StrongChoquet

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : X → Y) (hc : Continuous f) (ho : IsOpenMap f)
  (hs : Function.Surjective f) (σ : Strategy X)

private def trap : List (Move X) → Set X
  | [] => univ
  | b :: h => σ.move b h

private theorem trap_open (h : List (Move X)) : IsOpen (trap σ h) := by
  cases h with
  | nil => exact isOpen_univ
  | cons b h => exact σ.isOpen b h

private noncomputable def liftRegion (a : Move Y) (h : List (Move X)) : Set X := by
  classical
  exact f ⁻¹' a.region ∩ if a.point ∈ f '' trap σ h then trap σ h else univ

include hc in
private theorem liftRegion_open (a : Move Y) (h : List (Move X)) :
    IsOpen (liftRegion f σ a h) := by
  unfold liftRegion
  apply (a.isOpen.preimage hc).inter
  split_ifs
  · exact trap_open σ h
  · exact isOpen_univ

include hs in
private theorem exists_lift (a : Move Y) (h : List (Move X)) :
    ∃ x, x ∈ liftRegion f σ a h ∧ f x = a.point := by
  classical
  by_cases ha : a.point ∈ f '' trap σ h
  · have havail := ha
    obtain ⟨x, hx, he⟩ := ha
    exact ⟨x, by simp only [liftRegion, ite_eq_left havail, mem_inter_iff, mem_preimage];
                  exact ⟨he ▸ a.mem, hx⟩, he⟩
  · obtain ⟨x, he⟩ := hs a.point
    exact ⟨x, by simp only [liftRegion, ite_eq_right ha, inter_univ, mem_preimage];
                  exact he ▸ a.mem, he⟩

private noncomputable def liftMove (a : Move Y) (h : List (Move X)) : Move X where
  point := (exists_lift f hs σ a h).choose
  region := liftRegion f σ a h
  isOpen := liftRegion_open f hc σ a h
  mem := (exists_lift f hs σ a h).choose_spec.1

private theorem liftMove_point (a : Move Y) (h : List (Move X)) :
    f (liftMove f hc hs σ a h).point = a.point :=
  (exists_lift f hs σ a h).choose_spec.2

private theorem liftMove_preimage (a : Move Y) (h : List (Move X)) :
    (liftMove f hc hs σ a h).region ⊆ f ⁻¹' a.region :=
  inter_subset_left

private theorem liftMove_trap (a : Move Y) (h : List (Move X))
    (ha : a.point ∈ f '' trap σ h) :
    (liftMove f hc hs σ a h).region ⊆ trap σ h := by
  classical
  change f ⁻¹' a.region ∩ (if _ then _ else _) ⊆ _
  rw [ite_eq_left ha]
  exact inter_subset_right

/-- Reconstruct the source history from oldest to newest. When a marked point cannot be lifted into the preceding source response, the
lift falls back to the full preimage, making the strategy total on arbitrary histories. -/
private noncomputable def liftHistory : List (Move Y) → List (Move X)
  | [] => []
  | b :: h => liftMove f hc hs σ b (liftHistory h) :: liftHistory h

/-- The image of the source response, with coherent lifts of all earlier moves.
The image is open and retains the actual marked target point. -/
noncomputable def imageStrategy : Strategy Y where
  move a h := f '' σ.move (liftMove f hc hs σ a (liftHistory f hc hs σ h))
    (liftHistory f hc hs σ h)
  isOpen _ _ := ho _ (σ.isOpen _ _)
  contains a h := ⟨_, σ.contains _ _, liftMove_point f hc hs σ a _⟩
  subset a h := by
    rintro y ⟨x, hx, rfl⟩
    exact liftMove_preimage f hc hs σ a _ (σ.subset _ _ hx)

/-- A legal target play lifts to a single coherent legal source play.
We map an actual common source point; images are not commuted with intersections. -/
theorem imageStrategy_winning (hw : Winning σ) :
    Winning (imageStrategy f hc ho hs σ) := by
  classical
  intro a ha
  let b (n : ℕ) := liftMove f hc hs σ (a n) (liftHistory f hc hs σ (history a n))
  have hh (n : ℕ) : liftHistory f hc hs σ (history a n) = history b n := by
    induction n with
    | zero => rfl
    | succ n ih => change b n :: liftHistory f hc hs σ (history a n) = _
                   rw [ih]; rfl
  have hr (n : ℕ) :
      (imageStrategy f hc ho hs σ).move (a n) (history a n) =
        f '' σ.move (b n) (history b n) := by
    change f '' σ.move (b n) (liftHistory f hc hs σ (history a n)) = _
    rw [hh]
  have hb : Follows σ b := by
    intro n
    have hm : (a (n+1)).point ∈ f '' trap σ (liftHistory f hc hs σ (history a (n+1))) := by
      change (a (n+1)).point ∈ f '' σ.move (b n)
        (liftHistory f hc hs σ (history a n))
      rw [hh, ← hr]
      exact ha n (a (n+1)).mem
    have ht := liftMove_trap f hc hs σ (a (n+1)) _ hm
    change (b (n+1)).region ⊆ σ.move (b n)
      (liftHistory f hc hs σ (history a n)) at ht
    rwa [hh] at ht
  obtain ⟨x, hx⟩ := hw b hb
  refine ⟨f x, mem_iInter.mpr fun n => ?_⟩
  rw [hr]
  exact ⟨x, mem_iInter.mp hx n, rfl⟩

include f hc ho hs

/-- Continuous open surjections preserve the strong Choquet property, without
separation, countability or metrizability assumptions on either space. -/
theorem strong_image (hX : Strong X) : Strong Y := by
  obtain ⟨σ, hw⟩ := hX
  exact ⟨imageStrategy f hc ho hs σ, imageStrategy_winning f hc ho hs σ hw⟩

/-- Second countability descends from the source; no separate countability
hypothesis on the metrizable target is required. -/
theorem completelyMetrizable_image [SecondCountableTopology X]
    [IsCompletelyMetrizableSpace X] [MetrizableSpace Y] :
    IsCompletelyMetrizableSpace Y := by
  let : SecondCountableTopology Y :=
    (show IsOpenQuotientMap f from ⟨hs, hc, ho⟩).secondCountableTopology
  exact completelyMetrizable_of_strong
    (strong_image f hc ho hs strong_of_completelyMetrizable)

/-- A continuous open metrizable image of a Polish space is Polish. This gives
a compatible complete metric, not completeness of an arbitrary supplied metric. -/
theorem polish_image [PolishSpace X] [MetrizableSpace Y] : PolishSpace Y := by
  let : SecondCountableTopology Y :=
    (show IsOpenQuotientMap f from ⟨hs, hc, ho⟩).secondCountableTopology
  let : IsCompletelyMetrizableSpace Y := completelyMetrizable_image f hc ho hs
  infer_instance

/-- A regular Hausdorff open continuous image is metrizable by inherited second
countability and Urysohn, hence Polish. Mere Hausdorffness is not substituted. -/
theorem polish_image_of_t3 [PolishSpace X] [T3Space Y] : PolishSpace Y := by
  let : SecondCountableTopology Y :=
    (show IsOpenQuotientMap f from ⟨hs, hc, ho⟩).secondCountableTopology
  exact polish_image f hc ho hs

end OpenPolish
