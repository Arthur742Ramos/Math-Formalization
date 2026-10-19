# Baire products with locally compact R1 factors

The product `X × Y` is Baire if `X` is Baire and `Y` is locally compact and
R1 (preregular). The first factor has no countability, metrizability, regularity,
quasi-regularity or separation premise. Both factors may be empty. The Lean
universes of the factors and of refinement labels are independent.

A stronger supporting statement makes the construction visible: if `D` is a
dense Gδ subset of `X × Y` and `V` is a **fixed nonempty open** subset of `Y`,
then `Prod.fst '' (D ∩ (Set.univ ×ˢ V))` contains a dense Gδ subset of `X`.
The parameter witness set depends on `V`. This does not say that every generic
section is dense, or that one parameter set works simultaneously for all open
fiber regions. No countable pi-base, general pseudocomplete-space theorem,
Choquet characterization or unrestricted product of Baire spaces is claimed.

## Genuine proof construction

The proof first applies Zorn's lemma to labelled open subsets of the parameter
space. Maximality gives a pairwise-disjoint admissible family whose union is
dense in the chosen open domain. No cardinality bound is imposed on that family.
At each natural-number stage, labels carry positive compact subsets of `Y`.
Density of the next product open set and compact-neighborhood shrinking give
children with closure inside their parent's fiber interior and product rectangle
inside that open set. Only openness is used on `X`; all closure shrinking is in `Y`.

The countable intersection of the dense open parameter unions is a dense Gδ by
Baireness of `X`. For a parameter in that set, disjointness gives coherent parent
choices. The closed fiber sets are nested, nonempty and contained in one compact
set, so compactness supplies a common fiber point. The arbitrary dense-Gδ
projection follows by its open-intersection representation. Testing each nonempty
open rectangle then proves product Baireness without a circular product instance.

R1 is weaker than Hausdorffness. Compact sets are not silently treated as closed:
the argument uses their closures, whose compactness follows from the exact R1
infrastructure in Mathlib. `LocallyCompactSpace` is the actual Lean compact-neighborhood-basis hypothesis:
every neighborhood of a point contains a compact neighborhood of that point.
No unproved identification with a differently named compactness convention is used.

## Pinned hypotheses and dependency meanings

[MATERIAL-DEFINITIONS.md](MATERIAL-DEFINITIONS.md) retains the exact pinned definitions
and dependency chain for BaireSpace, R1Space, LocallyCompactSpace, CompactSpace,
IsCompact, Dense, IsGδ, IsOpen, closure and indexed Set.PairwiseDisjoint, with literal excerpts,
source and excerpt hashes, immutable line links and upstream Apache attribution.
It also records the compact-to-weak-local-to-R1-local instance chain, compact
closures under R1, positive compact shrinking and closed nested intersections.
The six-contract audit keeps quantifiers, independent universes, empty factors
and the fixed nonempty fiber region explicit. Distinct labels with equal
inhabited images are still constrained by indexed pairwise disjointness.

Class-to-field equivalences are constructor/projection proofs; they are not
claimed to be definitional equalities. Challenge and Solution compile the literal
predicate expansions and proved classical characterizations independently.
Static inventory consistency, exact pinned-source authentication, actual Lean
compilation and independent mathematical interpretation have distinct scopes.

## Source and research scope

[Aarts–Lutzer, *Pseudo-completeness and the product of Baire spaces*](https://msp.org/pjm/1973/48-1/pjm-v48-n1-p01-p.pdf),
Pacific Journal of Mathematics 48(1), 1973, printed pp.8–9 Section 4.1, supplies the
projection/refinement mechanism. Printed p.9 Section 4.2 and its corollary assume
quasi-regular Baire `X` and include locally compact Hausdorff `Y`. This formalization
adapts that construction and explicitly proves the arbitrary-`X`/R1 specialization;
it does not claim to formalize the full pseudocomplete theorem or reproduce all
of the paper's hypotheses. The consulted PDF SHA256 is
`538268e9276a75184874f44e4c7d79a64c5f1415caaaa5cd1f2da12de7651ceb`.

[Li–Zsilinszky, *More on products of Baire spaces*, arXiv:1702.06197v3](https://arxiv.org/pdf/1702.06197v3),
printed pp.1–2, gives modern research context in productive category and
completeness. Its stronger game and hereditary-Baire results are outside scope.
PDF SHA256: `e289b7691238657b2d686f21b2cb2bf0900a569e7db0bdd41045e501523ef47f`.
Original Oxtoby 1961 and White 1975 full texts were not consulted. No novelty,
priority or first-formalization claim is made. The audience is general topologists
studying productive Baire spaces, completeness and topological games. The compact-fiber
projection is a substantive formal bridge beyond the existing single-space category
theorem, complementary to the sibling countable-pi-base Kuratowski–Ulam development.

The bounded audit found no equivalent in the pinned Mathlib, the target-selection inventory of 21 prior
packages and 36 then-current remote branches with no open PR, or the complete
598-entry revision 332 registry snapshot captured 2026-10-17. Current registry reads were unavailable; dated public absence
does not establish absence of private or subsequent work.

## Selected declarations and verification

`comparator.json` selects six theorems:

- `LocallyCompactBaire.exists_maximal_pairwiseDisjoint_refinement`
- `LocallyCompactBaire.exists_pairwiseDisjoint_dense_refinement`
- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`
- `LocallyCompactBaire.baireSpace_prod`
- `LocallyCompactBaire.baireSpace_prod_of_compact`

No definitions are selected. Challenge contains the full proof and canonical
Mathlib imports only; Solution imports the byte-identical proof module. The
package owns its Lean 4.35.0-rc2 toolchain and all nine locked dependency revisions,
including Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
[VERIFICATION.md](VERIFICATION.md) describes source-bound stages;
[REVIEW.md](REVIEW.md) records review scopes. Exact-source canonical full,
rendering, actual artifact inspection and service outcomes require their separate
immutable receipts. Later source or metadata edits require affected verification;
no claim about those stages is inferred from local compilation alone.

## Attribution and roles

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers, separately preserved under the authorized campaign:
Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Material proof, test and package authorship: OpenAI Codex. Internal independent AI
review is distinct from human mathematical review, external peer review and a
Palomar editorial decision; none of those human/editorial outcomes is invented.
Apache-2.0. Classification: math.GN; MSC2020 54E52, 54B10.
