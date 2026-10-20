# The Baire product theorem for Choquet spaces

For arbitrary topological spaces X and Y, if X is Baire and the second player
has a winning full-history Banach–Mazur strategy on Y, then X × Y is Baire.
No separation, countability, metric or nonemptiness assumption is imposed on X.
The complete metric specialization is proved by an actual shrinking-ball
winning strategy, not by importing a product theorem.

## Statements and proof

- `ChoquetProduct.follows_intersection_eq`
- `ChoquetProduct.exists_compatiblePlay`
- `ChoquetProduct.alphaFavorable_of_isEmpty`
- `ChoquetProduct.exists_dense_isGdelta_fiber_witness`
- `ChoquetProduct.baireSpace_prod`
- `ChoquetProduct.metricStrategy_wins`
- `ChoquetProduct.alphaFavorable_of_completeMetric`
- `ChoquetProduct.baireSpace_prod_completeMetric`

The main construction refines a countable dense-open product family with
pairwise-disjoint X-labelled rectangles. A Baire point selects a coherent
branch; the full Y-history on that branch follows the winning second strategy.
For every prescribed nonempty open V in Y, a dense Gδ set G of parameters has
a witness y in V in all the product sets. G depends on V and the input family;
this is not a claim of dense entire sections or one G working for all V.
The metric strategy uses closed balls of radius at most2^-n inside each first
move. Completeness supplies a common point, and each later closed trap lies
inside the preceding open response. Closed balls are not assumed compact.

## Fixed game model and boundaries

`OpenMove` means any nonempty open set. `SecondStrategy.move` receives the
current opponent move and all earlier opponent moves, most recent first.
`Follows` requires the next first move to refine the current response;
`SecondWins` requires a single point in every response for every compatible
play. `AlphaFavorable` is existence of that actual strategy. The five model
definitions, strategy structure and explicit metric strategy (with public,
module-independent shrinking dependencies) stay fixed:
Comparator selects eight theorem proofs and zero definition holes.

On nonempty spaces this is the usual Choquet/alpha-favorable condition.
For empty Y it is an explicit vacuous extension: no legal initial move exists.
The compatible-play theorem is quantified over an actual legal initial move.
The product theorem includes empty factors. No determinacy, strong Choquet,
complete-metrizability equivalence or arbitrary-product claim is made.

## Attribution and source fidelity

Li–Zsilinszky, *More on products of Baire spaces*,
[arXiv:1702.06197v3](https://arxiv.org/pdf/1702.06197v3), printed p.2, recalls
the classical product theorem and cites H.E.White1975. Section2 pp.2–3
specifies the game conventions. White's original proof was not consulted;
this is not Li–Zsilinszky Theorem1.1. No novelty or priority is claimed.
The two Zorn/refinement helpers and rectangle-tree architecture credit
[the prior Apache-2.0 development](https://github.com/Arthur742Ramos/Math-Formalization/tree/d972b3cb0637c0e962c04384f16ec2b3e033d768/topology/locally-compact-baire).
The game-history convention also credits the earlier Oxtoby package. There
are no cross-project proof imports. All upstream attribution is preserved.

Authors: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers, separately authorized: Arthur Freitas Ramos;
David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
OpenAI Codex authored substantive proofs, tests and packaging. Reviews are
independent internal AI reviews; human/external peer review is not asserted.
License: Apache-2.0. Classifications: math.GN; MSC54E52,54B10,91A44.

## Definition and verification evidence

[MATERIAL-DEFINITIONS.md](MATERIAL-DEFINITIONS.md) retains literal pinned
imported meanings, dependency expansions and compiled Challenge/Solution
bridges. [CORE-DEFINITIONS.md](CORE-DEFINITIONS.md) audits exact Lean List and
length infrastructure. [VERIFICATION.md](VERIFICATION.md) separates immutable
verification stages. [REVIEW.md](REVIEW.md) states review scope and limits.
Run the package-owned toolchain and lockfile from this directory:

```sh
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

Each completed verification stage requires an immutable receipt for the exact
source, metadata and Comparator bytes. Ordinary compilation, protected full
verification, rendering, browser inspection, editorial review and registration
are distinct. No service action or acceptance is inferred from preparation.
