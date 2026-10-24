module
public import HittingThicknessCore
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic

@[expose] public section
open Set Function Metric
namespace ThickSensitive

/-- A pair in the same source set separates at this time; pairs may depend on time. -/
def SensitiveAtTime {X : Type*} [MetricSpace X] (f : X → X) (δ : ℝ) (U : Set X)
    (n : ℕ) : Prop := ∃ x ∈ U, ∃ y ∈ U, δ < dist (f^[n] x) (f^[n] y)

/-- Two fixed open target balls have a uniform positive mutual separation. -/
theorem separated_open_targets {X : Type*} [MetricSpace X] [Nontrivial X] :
    ∃ δ : ℝ, 0 < δ ∧ ∃ A B : Set X, IsOpen A ∧ A.Nonempty ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ x ∈ A, ∀ y ∈ B, δ < dist x y := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  have hd : 0 < dist a b := dist_pos.mpr hab
  let δ := dist a b / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ball a δ, ball b δ, isOpen_ball, nonempty_ball.mpr hδ,
    isOpen_ball, nonempty_ball.mpr hδ, ?_⟩
  intro x hx y hy
  have hx' : dist a x < δ := by simpa only [mem_ball, dist_comm] using hx
  have hy' : dist y b < δ := hy
  have h1 := dist_triangle a x b
  have h2 := dist_triangle x y b
  dsimp [δ] at *
  linarith

/-- A single refining open pair makes the common finite-family hitting set thick. -/
theorem finite_hitting_thick {X ι : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hs : Surjective f) (hw : Furstenberg.WeakMixing f)
    (s : Finset ι) (U V : ι → Set X) (hU : ∀ i ∈ s, IsOpen (U i) ∧ (U i).Nonempty)
    (hV : ∀ i ∈ s, IsOpen (V i) ∧ (V i).Nonempty) :
    WeakMinimal.Thick {n | ∀ i ∈ s, Furstenberg.Hit f (U i) (V i) n} := by
  obtain ⟨W, Z, hW, hnW, hZ, hnZ, href⟩ :=
    Furstenberg.finite_refinement f hf hw s U V hU hV
  intro L N
  obtain ⟨m, hm, hblock⟩ := WeakMinimal.hitting_thick f hf hs hw W Z hW hnW hZ hnZ L N
  exact ⟨m, hm, fun j hj => href (m+j) (hblock j hj)⟩

/-- One separation constant gives common positive thick blocks for every finite open family. -/
theorem weakMixing_thick_multisensitive {X : Type*} [MetricSpace X] [Nontrivial X]
    (f : X → X) (hf : Continuous f) (hs : Surjective f) (hw : Furstenberg.WeakMixing f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, ∀ U : Fin k → Set X,
      (∀ i, IsOpen (U i) ∧ (U i).Nonempty) →
      WeakMinimal.Thick {n | 0 < n ∧ ∀ i, SensitiveAtTime f δ (U i) n} := by
  obtain ⟨δ, hδ, A, B, hA, hnA, hB, hnB, hsep⟩ := separated_open_targets (X := X)
  refine ⟨δ, hδ, ?_⟩
  intro k U hU
  have ht := finite_hitting_thick f hf hs hw (Finset.univ : Finset (Fin k × Bool))
    (fun q => U q.1) (fun q => if q.2 then A else B) (fun q _ => hU q.1)
    (by intro q _; cases q.2 <;> simp [hA, hnA, hB, hnB])
  intro L N
  obtain ⟨m, hm, hblock⟩ := ht L (N+1)
  refine ⟨m, by omega, ?_⟩
  intro j hj
  refine ⟨by omega, ?_⟩
  intro i
  obtain ⟨x, hx, hfx⟩ := hblock j hj (i, true) (Finset.mem_univ _)
  obtain ⟨y, hy, hfy⟩ := hblock j hj (i, false) (Finset.mem_univ _)
  exact ⟨x, hx, y, hy, hsep _ (by simpa using hfx) _ (by simpa using hfy)⟩

end ThickSensitive
