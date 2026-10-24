module
public import WeakMixingCore
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic

@[expose] public section
open Set Function Metric
namespace MixingFactor

/-- Equicontinuity at one point of the actual forward iterate family, including time zero. -/
def OrbitEquicontinuousAt {X : Type*} [MetricSpace X] (f : X → X) (x : X) : Prop :=
  EquicontinuousAt (fun n : ℕ => f^[n]) x

/-- Weak mixing is inherited by continuous surjective semiconjugate factors. -/
theorem weakMixing_factor {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (g : Y → Y) (π : X → Y) (hπ : Continuous π)
    (hs : Surjective π) (hc : Semiconj π f g) (hw : Furstenberg.WeakMixing f) :
    Furstenberg.WeakMixing g := by
  intro U V A B hU hnU hV hnV hA hnA hB hnB
  obtain ⟨n, ⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := hw
    (π ⁻¹' U) (π ⁻¹' V) (π ⁻¹' A) (π ⁻¹' B)
    (hU.preimage hπ) (hnU.preimage hs) (hV.preimage hπ) (hnV.preimage hs)
    (hA.preimage hπ) (hnA.preimage hs) (hB.preimage hπ) (hnB.preimage hs)
  refine ⟨n, ⟨π x, hx, ?_⟩, ⟨π y, hy, ?_⟩⟩
  · simpa only [mem_preimage, hc.iterate_right n x] using hfx
  · simpa only [mem_preimage, hc.iterate_right n y] using hfy

/-- A single equicontinuity point is incompatible with nontrivial metric weak mixing. -/
theorem subsingleton_of_equicontinuousAt {X : Type*} [MetricSpace X]
    (f : X → X) (hw : Furstenberg.WeakMixing f) (x : X)
    (he : OrbitEquicontinuousAt f x) : Subsingleton X := by
  constructor
  intro a b
  by_contra hab
  have hd : 0 < dist a b := dist_pos.mpr hab
  let ε := dist a b / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.equicontinuousAt_iff.mp he ε hε
  obtain ⟨n, ⟨u, hu, hfu⟩, ⟨v, hv, hfv⟩⟩ := hw
    (ball x δ) (ball a ε) (ball x δ) (ball b ε)
    isOpen_ball (nonempty_ball.mpr hδ) isOpen_ball (nonempty_ball.mpr hε)
    isOpen_ball (nonempty_ball.mpr hδ) isOpen_ball (nonempty_ball.mpr hε)
  have hcu : dist (f^[n] u) (f^[n] x) < ε := by
    simpa only [dist_comm] using hclose u hu n
  have hcv : dist (f^[n] x) (f^[n] v) < ε := hclose v hv n
  have hua : dist a (f^[n] u) < ε := by simpa only [mem_ball, dist_comm] using hfu
  have hvb : dist (f^[n] v) b < ε := hfv
  have h1 := dist_triangle a (f^[n] u) b
  have h2 := dist_triangle (f^[n] u) (f^[n] x) b
  have h3 := dist_triangle (f^[n] x) (f^[n] v) b
  dsimp [ε] at *
  linarith

/-- Every equicontinuous metric factor of a weakly mixing topological map is subsingleton. -/
theorem equicontinuous_factor_subsingleton {X Y : Type*} [TopologicalSpace X]
    [MetricSpace Y] (f : X → X) (g : Y → Y) (π : X → Y)
    (hπ : Continuous π) (hs : Surjective π) (hc : Semiconj π f g)
    (hw : Furstenberg.WeakMixing f) (he : Equicontinuous (fun n : ℕ => g^[n])) :
    Subsingleton Y := by
  have hgw := weakMixing_factor f g π hπ hs hc hw
  constructor
  intro a b
  have hsub := subsingleton_of_equicontinuousAt g hgw a (he a)
  exact @Subsingleton.elim Y hsub a b

end MixingFactor
