/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.Clopen

@[expose] public section
open Set Topology TopologicalSpace Filter
universe u v
namespace WhitneyReversibility
variable {X : Type u} [mX : MetricSpace X] [cX : CompactSpace X]

abbrev Continuum (X : Type u) [tX : TopologicalSpace X] :=
  {K : NonemptyCompacts X // IsConnected (K : Set X)}


def singleton (x : X) : Continuum X := ⟨{x}, isConnected_singleton⟩


def whole [cnX : ConnectedSpace X] : Continuum X :=
  ⟨⟨⟨univ, isCompact_univ⟩, Set.univ_nonempty⟩, isConnected_univ⟩


def IsWhitneyMap (μ : Continuum X → ℝ) : Prop :=
  Continuous μ ∧ (∀ x, μ (singleton x) = 0) ∧
    ∀ A B : Continuum X, A.val < B.val → μ A < μ B


def IsSizeMap (σ : Continuum X → ℝ) : Prop :=
  Continuous σ ∧ (∀ x, σ (singleton x) = 0) ∧
    ∀ A B : Continuum X, A.val ≤ B.val → σ A ≤ σ B


def relativeLevel (σ : Continuum X → ℝ) (Y : Continuum X) (t : ℝ) :
    Set (Continuum X) := {K | K.val ≤ Y.val ∧ σ K = t}


def familyUnion (S : Set (Continuum X)) : Set X :=
  ⋃ (K : Continuum X) (_hK : K ∈ S), (K.val : Set X)


def IsDecomposable {A : Type v} [tA : TopologicalSpace A] (K : Set A) : Prop :=
  ∃ P Q : Set A, IsCompact P ∧ IsConnected P ∧ IsCompact Q ∧ IsConnected Q ∧
    P ⊆ K ∧ Q ⊆ K ∧ P ≠ K ∧ Q ≠ K ∧ P ∪ Q = K


def IsHereditarilyDecomposable {A : Type v} [tA : TopologicalSpace A] (S : Set A) : Prop :=
  ∀ K : Set A, K ⊆ S → IsCompact K → IsConnected K → K.Nontrivial → IsDecomposable K


theorem isCompact_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) (t : ℝ) : IsCompact (relativeLevel σ Y t) := by sorry

theorem isConnected_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) {t : ℝ} (ht : 0 ≤ t) (htY : t ≤ σ Y) :
    IsConnected (relativeLevel σ Y t) := by sorry

theorem familyUnion_relativeLevel {σ : Continuum X → ℝ} (hσ : IsSizeMap σ)
    (Y : Continuum X) {t : ℝ} (ht : 0 ≤ t) (htY : t ≤ σ Y) :
    familyUnion (relativeLevel σ Y t) = (Y.val : Set X) := by sorry

theorem exists_indecomposable_covering_family {μ : Continuum X → ℝ}
    (hμ : IsWhitneyMap μ) (Y : Continuum X)
    (_hYnt : (Y.val : Set X).Nontrivial) (hi : ¬ IsDecomposable (Y.val : Set X))
    {t : ℝ} (ht : 0 < t) (htY : t < μ Y) :
    ∃ S : Set (Continuum X), S ⊆ relativeLevel μ Y t ∧ IsCompact S ∧
      IsConnected S ∧ S.Nontrivial ∧ ¬ IsDecomposable S ∧
      familyUnion S = (Y.val : Set X) := by sorry

theorem sequential_strong_whitney_reversibility [cnX : ConnectedSpace X]
    {μ : Continuum X → ℝ} (hμ : IsWhitneyMap μ) (t : ℕ → ℝ)
    (ht : ∀ n, 0 < t n ∧ t n < μ whole)
    (htend : Tendsto t atTop (nhds 0))
    (hlevels : ∀ n, IsHereditarilyDecomposable {K : Continuum X | μ K = t n}) :
    IsHereditarilyDecomposable (univ : Set X) := by sorry

end WhitneyReversibility
