# Omega-bounded Sigma-products and a sharp compactness criterion

A space is **ω-bounded** when the closure of each countable subset is compact.
We prove that the countable-support Σ-product of arbitrary T₁ ω-bounded
factors is ω-bounded and hence countably compact. No first countability,
separability, countable index, or compact-factor premise is added to this theorem.

For compact Hausdorff factors we prove a sharp companion: the Σ-product is
compact **if and only if** only countably many factors have a value different
from the chosen basepoint. Thus an uncountable index of singleton factors is
allowed, while every uncountable discrete Boolean Σ-product is countably
compact but not compact.

The Σ-product uses the subtype topology of the **ordinary product**, not the
box topology. Support is countable, not finite. A basepoint is supplied
explicitly; we do not assert its existence for a product with an empty factor.
Index and factor universes are independent. The empty index and the empty
countable subset are included in the proofs.

## Proof content and contracts

For a countable family `s` of Σ-points, form the countable union `J` of their
deviation supports. Each coordinate image of `s` is countable, so its closure
is compact by the factor hypothesis. The product `K` of these closures is
closed and compact by Tychonoff's theorem and contains `closure s`. Outside
`J`, coordinate images lie in the closed basepoint singleton, so every point
of `K` is countably supported. Compactness then transports into the Σ-subtype.
The empty-family proof does not falsely equate an empty coordinate closure
with a basepoint singleton.

Countable compactness uses Mathlib's canonical sequence-cluster-point
criterion, applied to the compact closure of the sequence range. It does
not assert that arbitrary sequences have convergent subsequences.

For the sharp compactness criterion, finite-coordinate replacement makes
the Σ-subspace dense. If it is compact, its image in the Hausdorff product
is closed, hence the whole product. Choosing a nonbasepoint simultaneously
at every coordinate where this is possible forces that set of coordinates
to be countable. Conversely, if that set is countable, every product point
has countable support; the Σ-product is the whole compact product.

Selected theorems:

- `SigmaCompact.exists_compact_trap`
- `SigmaCompact.omegaBounded_sigmaProduct`
- `SigmaCompact.countablyCompactSpace_sigmaProduct`
- `SigmaCompact.omegaBounded_sigmaProduct_of_compact`
- `SigmaCompact.compactSpace_sigmaProduct_iff`
- `SigmaCompact.boolean_sigma_countablyCompact_not_compact`

Selected literal definitions are `SigmaCompact.OmegaBounded`,
`SigmaCompact.deviationSupport` and `SigmaCompact.activeCoordinates`.
Their bodies are recorded in [DEFINITIONS.md](DEFINITIONS.md) and tested under
independent Challenge and Solution imports. The proof module and Challenge
are identical and import only Mathlib. Solution imports the proof module;
the two declaration sets are never imported together.

## Mathematical source, audience and overlap

Gutik and Ravsky, [*On old and new classes of feebly compact spaces*,
arXiv:1804.07454v3](https://arxiv.org/pdf/1804.07454v3), printed p.1 defines
ω-boundedness, and printed p.4 defines countable-support Σ-products.
Proposition 2.4 on printed p.5 proves the more general ω-bounded-pracompact
product theorem, with T₁ required for its Σ-version. Our ω-bounded
specialization takes the dense core to be each whole factor and follows
the coordinate-closure argument. The directly consulted PDF has SHA256
`7e040ba18193c87cb789c178cb74fbc3733bf4b3dc55a4eed719b8f6305d653f`.

We do **not** formalize the full dense-core pracompactness theorem. The sharp
compactness criterion and Boolean contrast are separately proved companions;
we do not attribute their statements to Proposition 2.4. Example 2.5 on
printed pp.5–6 gives a non-T₁ compact-factor Σ-example preventing omission
of the T₁ premise; that counterexample is not formalized here. Printed pp.2
and 4 explain applications in topological algebra and productivity questions.
No novelty, original priority, pseudocompactness, or group theorem is claimed.

The earlier [Fréchet–Urysohn Σ-product package](../sigma-product-frechet)
proves sequential convergence under first countability and countable closure
support under T₁. Its definition/support bookkeeping and finite-coordinate
density argument are credited and reused in standalone form. The compact
coordinate trap, compactness transport and sharp criterion are additional
proofs; no earlier campaign package is imported. Canonical compactness,
product topology and countable compactness machinery remain Mathlib's work.

No equivalent was found in the eighteen preexisting project scopes, the dated
target-selection branch/open-PR inventory, pinned Mathlib, or complete revision-332 public
snapshot of 598 entries captured 2026-10-17 at 16:05 UTC. Fresh global registry
access and private-attempt clearance are not established by this dated audit.
Unknown or pending entries remain occupied work, not available targets.

## Reproducible checks and evidence boundaries

This independent package owns Lean `leanprover/lean4:v4.35.0-rc2`, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`, and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` with its own nine-record lockfile.
Run commands from this directory, using the verified cloud launcher:

```bash
/workspace/palomar-tools/run lake build
/workspace/palomar-tools/run lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

Six modules check genuine proofs, independent module contracts, every selected
transitive axiom closure and semantic edge cases: empty index and subset,
uncountable Boolean indices, independent universes, infinite countable support,
arbitrarily many singleton factors, and a nonzero compact-interval basepoint.
Only the standard axioms `propext`, `Classical.choice`, `Quot.sound` are allowed.

Verification receipts certify only their named immutable source and metadata.
Local builds, internal AI review, full protected comparison, independent kernels,
rendering, browser inspection, editorial decisions and registration are distinct
stages. Later exact-source outcomes belong in external receipts; this stable
source account does not infer them or require permanent pending-status prose.
Before any verified intake handoff, run the root exact-source release guard
against the original full report and exact source archive. See
[REVIEW.md](REVIEW.md) for review scope and limits. The cloud-host namespace
restriction is respected. Any fresh runner security exception requires its own
specific user approval.

## Attribution

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
These separately approved campaign roles do not invent human proof contributions.
OpenAI Codex authored the substantive proofs, tests and packaging. Independent
reviews are internal AI reviews; no human or external peer review is claimed.
Classical sources, earlier formalizations and upstream Lean/Mathlib retain
attribution. License: Apache-2.0.
