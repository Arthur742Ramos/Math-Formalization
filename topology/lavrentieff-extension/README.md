# Lavrentieff's Gδ homeomorphism extension theorem

For arbitrary subsets `s ⊆ X`, `t ⊆ Y` of completely metrizable spaces, every
homeomorphism `s ≃ₜ t` extends to a homeomorphism between Gδ sets `B`, `C`
with `s ⊆ B ⊆ closure s` and `t ⊆ C ⊆ closure t`. Agreement with the supplied
homeomorphism is pointwise. Empty subsets and empty ambient spaces are included.
There is no separability, closedness or uniform-continuity assumption.

The proof constructs open small-image-diameter loci, intersects countably many
of them inside the domain closure, proves the image neighborhood filters Cauchy,
and uses completeness to obtain extension limits. Mathlib's `extendFrom` then
gives continuous extensions. Restricting the forward and inverse extensions to
`B = D ∩ F ⁻¹' E` and `C = E ∩ G ⁻¹' D` gives mutually inverse maps, by equality
on dense subsets. Compatible complete metrics preserve the supplied topologies.

Selected contracts in namespace `Lavrentieff`:

- `extensionDomain_isGδ`: the constructed domain is Gδ.
- `subset_extensionDomain`: a continuous map's original domain is included.
- `cauchy_at_extensionDomain`: the restricted image neighborhood filter is Cauchy.
- `continuous_extension`: continuous extension to a Gδ superset inside the closure.
- `isGδ_inter_preimage`: relative preimages preserve ambient Gδ status.
- `extend_inverse_maps`: glues two extensions on the correct restricted domains.
- `homeomorph_extension`: full complete-metric homeomorphism extension.
- `completely_metrizable_extension`: metric-independent version for supplied topologies.

`LEChallenge.lean` is an independent, fully proved copy of `Lavrentieff.lean`;
`LESolution.lean` imports the proof. No holes, custom axioms or definition holes.
The standard axiom allowlist is `propext`, `Quot.sound`, `Classical.choice`.
Only pinned Mathlib imports are used; other project packages are not dependencies.

Build from this directory with `lake build`, using Lean4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Package source/configuration hashes,
independent review and machine results belong to immutable external receipts;
see [VERIFICATION.md](VERIFICATION.md). Native checks do not replace canonical
sandbox verification or rendering. No registry submission is initiated by this package.

[Source mapping](SOURCE-MAPPING.md) separates the original Euclidean theorem,
the modern general form and research applications. [Material definitions](MATERIAL-DEFINITIONS.md)
retain exact pinned excerpts and semantic dependencies. Independent review scopes
are described in [REVIEW.md](REVIEW.md).

Campaign-authorized authors and responsible maintainers (separate roles):
Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz.
OpenAI Codex supplied substantive formal proofs, proof engineering and packaging.
Independent internal AI review is identified separately; no human proof contribution,
human review or external peer review is inferred from the author names.
Apache-2.0; upstream authorship and source headers retained in definition evidence.
