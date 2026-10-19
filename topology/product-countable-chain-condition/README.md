# Countable cellularity of arbitrary products via finite subproducts

For arbitrary topological factors, if every finite subproduct has the countable
chain condition (CCC), then the full product has CCC. With nonempty factors this
is an equivalence. In particular, every product of separable spaces has CCC,
with no index-cardinality bound. This is classical mathematics, formalized from
Nina M. Roy's published exposition, printed p.176, Theorem 2.2 and Corollary 2.3.

## Exact scope

`ProductCCC.HasCCC X` means that every set-family of pairwise disjoint nonempty
open subsets of X is countable. `HasCCC.countable_index` proves its independently
universe-polymorphic indexed form. `ProductCCC.IsDeltaSystem s J r` means that
any distinct indices in J have supports intersecting exactly in r; supports
need not be distinct, and the common root may be empty or the whole support.

| Selected theorem | Contract |
| --- | --- |
| `ProductCCC.uncountable_delta_system` | Every uncountable indexed finite-support family contains an uncountable delta-system, including repeated supports. |
| `ProductCCC.hasCCC_pi_of_finite` | All finite subproducts CCC implies the full product CCC, without nonemptiness or separation assumptions. |
| `ProductCCC.hasCCC_pi_iff` | For nonempty factors, full-product CCC iff every finite subproduct is CCC. |
| `ProductCCC.hasCCC_pi_of_separable` | Arbitrarily many separable factors give CCC; empty factors are allowed. |
| `ProductCCC.HasCCC.of_continuous_surjective` | Continuous surjections preserve CCC. |
| `ProductCCC.hasCCC_discrete_iff` | A discrete space has CCC iff its underlying type is countable. |

Index and factor universes are independent. Empty index types are permitted.
The iff converse needs nonempty factors: an empty factor makes the full product
empty and CCC even if another finite subproduct is an uncountable discrete space.
No Hausdorff, compactness, first-countability or continuum-bound hypothesis is
used in the forward criterion or separable corollary. Arbitrary CCC factors
alone do not suffice. Stronger productively-CCC, Knaster/caliber, forcing
independence and nearby MA/CH results are outside scope.

## Source, proof and overlap

[Roy (1989)](https://ddd.uab.cat/pub/pubmat/pubmat_a1989v33n2/pubmat_a1989v33n2p173.pdf)
provides the delta-system argument on printed pp.174–175 and the exact product
statements on p.176. Her exposition tentatively traces the criterion to
Noble–Ulmer (1972); that original paper is not claimed directly consulted.
The rare-coordinate case is implemented by Zorn maximality rather than an
omega-one recursion. The finite common-root projection and gluing argument is
the substantive product proof. The nonempty-factor equivalence, image theorem
and discrete boundary are companion results. No novelty or priority claimed.

[Mezabarba–Aurichi–Junqueira (2020)](https://arxiv.org/pdf/2005.10325v3),
Introduction and Section 4, supplies current research context in productive
cellularity. Its stronger productively-CCC theorem and poset spectra are not
claimed formalized. Audience: general and set-theoretic topology, cellularity
and chain conditions.

Mathlib supplies Zorn, countability and finite-set infrastructure, actual product
topology, finite separable products and the existing disjoint-open-family
countability theorem for separable spaces. Those are credited upstream.
The prior HMP campaign package proves separability under a continuum index bound;
this package proves the finite-subproduct cellularity criterion for arbitrary
indices. No prior campaign package is imported. Bounded searches of the pinned
Mathlib, all 19 prior packages, 32 remote branches and zero open PRs found no
equivalent target at selection. The complete saved public registry snapshot
(revision 332, 598 entries, captured 2026-10-17 16:05 UTC) also supplied no equivalent.
Live registry/protocol reads were unavailable; this is not current global/private
intake clearance or a promise of eligibility or acceptance.

## Verification account

The package owns its toolchain and nine-record lockfile: Lean
`leanprover/lean4:v4.35.0-rc2`, Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Proof and Challenge are byte-identical
standalone modules; Solution imports the proof. Tests separately import Challenge
and Solution, check every selected contract and both literal definition values,
and exercise empty cases, repeated/empty roots and larger universes.

```sh
lake build
lake env lean AxiomAudit.lean > /tmp/product-ccc-axioms.txt
python3 scripts/check_package.py --axiom-log /tmp/product-ccc-axioms.txt
```

See [VERIFICATION.md](VERIFICATION.md) and [REVIEW.md](REVIEW.md) for the exact
meaning of these stages. Completed canonical full and rendering evidence is
established only by immutable external receipts naming the exact source, config,
metadata, toolchain and reports. Local checks and internal review do not imply
those receipts, browser visual inspection, editorial acceptance or registration.
This source keeps provenance stable while separately bound receipts record later
outcomes; earlier dated checkpoints do not override later actual observations.

## Attribution

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz. These are separately campaign-authorized roles.
OpenAI Codex authored substantive proofs, tests and packaging. Reviews are internal
AI reviews; no human proof contribution or external peer review is invented.
License: Apache-2.0, as recorded in the repository root LICENSE.
