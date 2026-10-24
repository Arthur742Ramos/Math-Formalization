# Mycielski Cantor independent set — local development

The sole target is: in a nonempty perfect Polish space X, given countably many
dense-open subsets R_n of X × X, construct a continuous injective map e from
the usual Cantor space Nat → Bool into X such that every ordered pair of
distinct image points belongs to every R_n. The target may be localized inside
a prescribed nonempty open set. This is one Cantor independent set, not a dense
sigma-Cantor union, arbitrary arity, or invariant dynamical conclusion.

The full theorem `Mycielski.exists_cantor_independent` is proved in
`Mycielski/Independent.lean`. Exact-source release readiness is established by
immutable external verification/render/review receipts; a Lean build alone is
not full release certification. No fusion-existence premise is assumed.

Jan Mycielski, Independent sets in topological algebras, Fundamenta Mathematicae
55 (1964), 139–147, https://eudml.org/doc/213780 supplies the classical source.
The original scan returned403, so direct inspection is not claimed. Jian Li,
Jie Lu and Yuanfen Xiao, A dynamical version of Kuratowski–Mycielski theorem
and invariant chaotic sets, https://arxiv.org/abs/1801.10266v1, introduction,
directly states the stronger dense-Gdelta binary-relation theorem and explains
its use in constructing uncountable scrambled sets. Our limited target is
explicitly distinguished from that stronger theorem. No novelty is claimed.

Bounded campaign and pinned-Mathlib searches found no equivalent theorem.
Initial public API queries returned403. Supported browser searches then found
two unrelated graph-theory Mycielski entries and no Cantor-independent match.
This bounded public search is not a universal equivalence or priority claim. Independent internal AI scope
review approves this precise target for genuine proof development.

The proof constructs finite coordinated refinements with disjoint
closures and shrinking diameters, satisfying all earlier ordered-pair relation
requirements. Mathlib's CantorScheme limit/continuity infrastructure is
credited; existence of the compatible fusion is proved in this package.

Campaign authors and responsible maintainers: Arthur Freitas Ramos, David
Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex performs the
formalization; no human proof contribution or human/external review is inferred.
All necessary validation runs locally under root AGENTS.md. Lean4.35.0-rc2 and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain exactly pinned.

## Proof and verification interface

`FusionStep` proves joint evaluation openness and simultaneously refines every
ordered pair of distinct finite cells. `Scheme` iterates the coordinated
refinement, scheduling all earlier relations. `Independent` proves totality,
continuity, injectivity, localization, relation membership and the Polish
closed-embedding statement. No compactness of closed balls is assumed.

`MycielskiChallenge` contains the complete standalone proof from Mathlib imports;
`MycielskiSolution` imports the separate project modules. Comparator selects the
final theorem with zero definition holes. The `CantorSpace` abbreviation remains
protected in its statement dependency closure. Separate semantic entrypoints
check the literal Nat→Bool product topology, absence of isolated points, Polish
compatible completeness, closed-embedding fields, actual range and density.
Only propext, Quot.sound and Classical.choice are permitted axioms.
