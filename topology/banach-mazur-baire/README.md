# Oxtoby’s Banach–Mazur characterization of Baire spaces

For any topological space X, X is Baire iff the first player has no winning full-history strategy in the Banach–Mazur game. Players alternate arbitrary nonempty open sets with non-strict nesting. The second player wins when there is one point in every move. The first-player strategy is a function on every finite opponent history; its preceding own moves are reconstructible. This is not a stationary strategy restriction or an assertion of determinacy.

The constructive proof mechanism is substantial: maximal disjoint strategy-response levels have open dense domains in the initial open set. A Baire point chooses a coherent history branch because disjointness forces unique parents. Its opponent moves form a legal play with a common point. Conversely a failed dense-open intersection supplies an initial open region and successive dense-open cuts defining a winning first-player strategy. Every strategy admits at least one legal play (equality of moves is allowed), and both players’ intersections are proved equal. The empty space has no legal initial move and no first strategy; the equivalence includes it explicitly.

## Scope and provenance

The consulted primary sources recall this classical criterion: Li–Zsilinszky (2017), printed p.2 and Section2 pp.2–3; Aurichi–Bonanzinga–Medina (2021), printed p.1 and Corollary3.3 p.6. The original Oxtoby1957 text and Kechris8.11 were not consulted. No novelty, priority or original-proof correspondence is claimed. Strong Choquet games, productive-Baire theorems and finite/countable-family variants are outside scope. The package builds a reusable category/game bridge for general topology and productive-Baire research rather than asserting a new research theorem.

The Zorn/disjoint-dense-refinement helpers are reused with Apache-2.0 attribution from the earlier locally-compact-baire package at d972b3cb0637c0e962c04384f16ec2b3e033d768. Challenge imports canonical Mathlib only. The new game definitions, coherent strategy-response proof and converse are genuine package code.

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
These are the separately preserved campaign-authorized roles. Substantive proof/test/package authorship is OpenAI Codex; reviews are independent internal AI reviews. No human proof contribution or human/external peer review is inferred.

## Exact meanings and checks

[MATERIAL-DEFINITIONS.md](MATERIAL-DEFINITIONS.md) retains eight material Mathlib declarations, exact pinned source/excerpt hashes, original headers, meanings and dependency expansions. [CORE-DEFINITIONS.md](CORE-DEFINITIONS.md) retains exact Lean-core List/length infrastructure. ChallengeTests and SemanticTests independently compile literal model definitions, class-field bridges, the dense-open characterization, exact selected contracts and empty/indiscrete boundaries. Literal definitions, class fields and proved equivalences are distinguished.

Lean: leanprover/lean4:v4.35.0-rc2, compiler11acb17ec6b07a8f9e9173e6845197929540936b. Mathlib:065356127b1dc0016f66b7283ce0ce2c4055aa55. The nine dependency revisions are frozen in this package’s own lake-manifest.json. The seven theorems are Comparator targets; definition_names is empty. The four fixed game definitions and FirstStrategy structure are compared transitively as non-target dependencies, preserving their bodies rather than allowing definition holes. All four literal values also have separately compiled semantic tests. Fresh transitive reports are retained in verification/local-axioms.txt; only approved standard axioms may occur, and the four literal definitions plus empty-space theorem have empty closures.

Build with the package’s own toolchain and lockfile:

```sh
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

See [VERIFICATION.md](VERIFICATION.md) and [REVIEW.md](REVIEW.md). Local/ordinary checks, protected Comparator and independent kernels, canonical rendering, browser-runtime inspection, editorial review and registration are separate stages. Each completed stage requires its own immutable exact-source external receipt. Frozen source remains stable while later receipts identify their actual tested commit. No intake, editorial acceptance or registration is inferred from proof checks.
