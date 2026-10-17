# Countable-density Hewitt–Marczewski–Pondiczery theorem

For any family of separable topological spaces indexed by a set of cardinality
at most continuum, the product is separable. No separation, compactness,
metrizability or second-countability assumptions are used. Empty factors are
allowed (then the full product is empty), as is the empty index set (a one-point
product). For discrete Boolean cubes the continuum bound is also necessary.

This formalizes the **countable-density case** of classical HMP, not its
arbitrary-cardinal generalization. No new mathematical theorem or priority is
claimed. It complements the earlier compact-product metrizability development:
uncountable Boolean cubes can be separable even when they are not metrizable.

## Proof and exact contracts

`HMP.RowCode = Σ n : ℕ, (Fin n → Bool) → ℕ` is countable. An injection of the
index set into binary sequences assigns coordinate codes. On any finite set of
indices a sufficiently long prefix separates these codes. Extending a finite
lookup table then realizes all prescribed natural-number labels on that set.
The literal `HMP.row` definition applies those labels to a dense sequence in
each factor. Every nonempty basic product cylinder contains one coded row.
The general theorem splits off the empty-product-space case before choosing
factor sequences; it never assumes nonempty factors implicitly.

For the converse, a dense sequence in a discrete Boolean cube assigns each
coordinate its binary value sequence. Distinct coordinates are distinguished
by the nonempty open cylinder prescribing false at one and true at the other.
Thus the coordinate set injects into binary sequences and has size at most
continuum. The proof handles universe lifts explicitly, without assuming CH.

Comparator selects seven theorems in namespace `HMP`:
`finite_interpolation`, `denseRange_rows`, `continuum_bound_iff`,
`separable_product_of_embedding`, `separable_product`,
`coordinate_patterns_injective`, `boolean_cube_separable_iff`;
and the literal definition `row`. The helper's nonempty-factor assumption is
explicit; the main theorem has none. No converse for arbitrary factors, no
sequential-density assertion, and no effective enumeration is claimed.

`HMPChallenge.lean` is a byte-identical, fully proved copy of the proof module
and imports only Mathlib. `HMPSolution.lean` publicly imports the proof module.
Challenge and Solution import tests are built separately. `AxiomAudit.lean`
prints fresh transitive dependencies for every selected declaration: the seven
theorems use only `propext`, `Classical.choice`, `Quot.sound`; `row` uses none.
Semantic tests cover the continuum-sized cube, a larger nonseparable cube,
empty factors, empty indices, singleton factors and a lifted index universe.

## Primary source, audience and overlap

Dikranjan and Shakhmatov, [arXiv:0912.0497v1](https://arxiv.org/pdf/0912.0497v1),
introduction printed pp.1–2, recalls full HMP and studies algebraic analogues
for dense images in large torus powers and Markov potential density. This is
concrete general-topology and topological-group research context. Their new
group results are not formalized here. The historical originals were
identified bibliographically, not directly consulted. Our finite-table proof
is independent; the discrete-cube converse is a proved companion.

Pinned Mathlib already provides countable-index separable products and the
credited topological/cardinal infrastructure. No equivalent continuum-index
result was found in its source audit or in the saved complete public registry
snapshot: revision332,598activeentries, checked2026-10-17T16:05UTC. This is dated
public coverage, not an absolute novelty claim or a private-attempt search.
The documented current results API returnedHTTP403 at19:08UTC; no denied route
was retried or bypassed. Canonical verification, rendering and fresh registry
clearance remain obligations, and no Palomar intake or registration is claimed.

## Attribution, toolchain and status

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
These are separately confirmed roles under the campaign authorization.
OpenAI Codex materially authored the proofs, tests and packaging; no human review is claimed,
and internal independent AI review is not external peer review.
Apache-2.0; math.GN; MSC2020 54B10,54D65,54A25.

Run from this directory with its own `lean-toolchain` and `lake-manifest.json`:
Lean4.35.0-rc2, compiler11acb17, Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.
In the saved cloud environment use `/workspace/palomar-tools/run lake build`.
The local Comparator is blocked by the host user-namespace UID map; do not
bypass it. A full canonical check and rendering on disposable CI runners need
fresh specific approval for their conditional pinned AppArmor installer.
Prior targets' runner approvals do not apply. See [REVIEW.md](REVIEW.md).
