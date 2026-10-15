# Perfect images of metrizable spaces

Every continuous closed surjection with compact fibers from a metrizable space
has a metrizable codomain. The domain and codomain may have arbitrary cardinality
and independent universes. No second countability, separability, compact domain,
local compactness, completeness, finite-fiber or nonemptiness assumption is used.
Separation of the codomain is derived from the registered perfect-map results.

`FiberNeighborhoods.lean` constructs the open set of values whose entire fiber
lies within radius `r` of a prescribed fiber. Its main estimate says that, for
each open neighborhood of a target point, every sufficiently small such set
containing that point lies inside the prescribed neighborhood. The radius is
uniform over the centers of those sets. Compactness of the distinguished fiber
is used twice; the triangle inequality relates the two radii.

`PerfectImage.lean` takes locally finite open refinements at reciprocal radii.
The new estimate proves that their union is a basis. The registered full
Nagata–Smirnov theorem supplies metrizability. The package also provides the
ordinary Mathlib `IsProperMap` interface and an actual `MetricSpace` whose
induced topology equals the supplied topology.

Source: Katsuro Sakai, *Geometric Aspects of General Topology*, second-edition
author manuscript dated November 2, 2023, Proposition 2.4.5(1), printed pp.50–51.
The actual author-uploaded manuscript was checked independently. The source
uses the Alexandroff–Urysohn cover criterion; this proof uses the registered
paracompact-image and Nagata–Smirnov results after the same fiber-neighborhood
argument. The theorem applies to noninjective metrizable quotient constructions
and compact decompositions. The source's locally finite closed gluing corollary
is a downstream application outside this package's selected scope.

Build from this directory with `lake build`. Exact toolchain:
`leanprover/lean4:v4.35.0-rc2`; Mathlib:
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

Previously registered support is reused with attribution:

- Full Nagata–Smirnov, PALOMAR-2026-10-14-000001 v1, source
  `6aa68b2cb67719a187e64de29567443575eb560e`: four modules in
  `NagataSmirnovSupport/`, with adapted import paths.
- Perfect surjections and paracompactness, PALOMAR-2026-10-13-000004 v1,
  source `984a610395e195b8d3ca0cd88282ef343e74d33d`:
  `PerfectParacompactSupport.lean`, with an attribution comment only.

All substantive support declarations and proofs are unchanged. Provenance
hashes are in `verification/registered-support-provenance.json`.
`PerfectImageChallenge.lean` includes this credited support and the new proofs
using canonical Mathlib imports only. `PerfectImageSolution.lean` exports the
reusable modules. Comparator selects five new theorems and the two new
definitions listed in `comparator.json`; no registered prerequisite is selected
as a new result.

Authors and responsible maintainers: Arthur Freitas Ramos, David Barros Hulak,
and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex authored substantive proofs
and packaging under Arthur's authorization. Internal AI review and machine
verification are distinguished from human review; no human review is claimed.
This formalizes classical mathematics without claiming new mathematics,
first-formalization priority, or registry acceptance. Apache-2.0 license.

See `AUDIT.md`, `DEFINITIONS.md`, `REVIEW.md` and `verification/` for statement,
reuse and verification evidence. Publication alone does not establish
registration; no registration is claimed without a public receipt.
