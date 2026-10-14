module
import Solution

open Set Function Topology
universe u v

/- The empty domain is allowed, and inverse transfer does not assume surjectivity. -/
example (Y : Type v) [TopologicalSpace Y] [ParacompactSpace Y] :
    ParacompactSpace Empty :=
  PerfectParacompact.paracompact_preimage (f := Empty.elim)
    continuous_of_discreteTopology (fun S _ => by
      have he : S = ∅ := Set.eq_empty_of_isEmpty S
      simpa only [he, image_empty] using (isClosed_empty : IsClosed (∅ : Set Y)))
    (fun _ => by
      rw [Set.eq_empty_of_isEmpty (Empty.elim ⁻¹' {_})]
      exact isCompact_empty)

/- Arbitrary independent universes and a compact factor with no separation assumption.
This exercises genuine infinite-fibre maps, rather than only embeddings. -/
example (K : Type u) (Y : Type v) [TopologicalSpace K] [TopologicalSpace Y]
    [CompactSpace K] [ParacompactSpace Y] : ParacompactSpace (K × Y) := by
  have hp : IsProperMap (Prod.snd : K × Y → Y) := isProperMap_snd_of_compactSpace
  exact PerfectParacompact.paracompact_preimage hp.continuous hp.isClosedMap
    (fun y => hp.isCompact_preimage isCompact_singleton)

/- Proper maps with regular targets need no separation assumption on the domain. -/
example (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [RegularSpace Y] [ParacompactSpace X] (f : X → Y) (hp : IsProperMap f)
    (hs : Surjective f) : ParacompactSpace Y :=
  PerfectParacompact.paracompact_image hp.continuous hp.isClosedMap
    (fun _ => hp.isCompact_preimage isCompact_singleton) hs
