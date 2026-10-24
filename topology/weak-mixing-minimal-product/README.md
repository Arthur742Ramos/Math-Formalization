# Weak mixing times minimality: transitivity of the product

A continuous weakly mixing map f on a nonempty compact Hausdorff space X,
paired with a continuous map g on a nonempty compact space Y whose every
natural forward orbit is dense, has transitive actual product dynamics.
No separation or metric assumption is required on Y. Natural time includes0.

The new proof derives surjectivity of f, constructs arbitrarily late inclusive
blocks0..L in open hitting sets, uses compact finite preimage covers to bound
minimal hitting gaps0..K, and intersects these sets before combining actual
product-coordinate witnesses. Zero gap bounds are included. The thickness
helper uses explicit surjectivity without compactness/separation; the main
theorem proves it. The syndetic helper needs a nonempty source, not its openness.
No converse, product minimality, product weak mixing, dense-orbit product claim,
measure mixing or disjointness statement is made.

Michael Hochman, Notes on Topological Dynamics, June15 2022, Lemma1.15 and
Propositions6.10–6.11 were directly inspected:
https://math.huji.ac.il/~mhochman/courses/TD2022/notes-v3.pdf
The compact metric source is generalized explicitly to the hypotheses above.
Finite simultaneous hitting and square equivalence are retained with credit
in WeakMixingCore from immutable source9e5b57dba2ba9423cc8f12ff934bd07d86394c47;
these inherited proofs are not new work here.

Five selected declarations are in comparator.json. ProductChallenge merges
the credited core and new proof with Mathlib-only imports; ProductSolution
imports the implementation. Every definition is fixed, no holes or added
axioms. Exact-source readiness is recorded by immutable external local native,
canonical, rendering, visual and independent review receipts; a build alone
is not full certification. No intake or registration is claimed.

Authors and responsible maintainers: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex proof development and separate
internal AI reviews disclosed; no human proof contribution, external review
or novelty inferred. Retained material/core provenance supplies exact pins.
Run lake build, python3 scripts/check_package.py and root local AGENTS.md gates.
No author-hosted CI is added. Bounded equivalent-statement/public-registry
checks found no matching target; editorial significance remains external.
