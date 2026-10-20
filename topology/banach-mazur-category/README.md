# Banach–Mazur determinacy for Baire-property targets

Let X be a complete metric space and A a subset with the property of Baire.
Players alternate arbitrary nonempty open sets with non-strict nesting.
The first player wins precisely when a point of A belongs to every move;
the second wins otherwise. Both strategies receive full opponent histories.
The game is determined: I has a winning strategy iff A is nonmeagre, and
II has a winning strategy iff A is meagre. No separability or absence of
isolated points is assumed.

The ten Comparator-selected declarations are:

- `CategoryGame.exists_jointPlay`
- `CategoryGame.not_both_winning`
- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

The seven exposed game definitions and two strategy structures have fixed
literal values. `definition_names` is empty. Full-history strategies are not
restricted to stationary responses. The exact joint-play theorem returns both
strategy equations and every alternating inclusion, establishing nonvacuity
whenever a first strategy exists. Separate intersection-equality lemmas identify
the I-move, II-move and all-moves payoffs. On an empty space there is no initial
legal move or first strategy; the second-player predicate is explicitly vacuous.

The meagre-target avoidance theorem uses only a topology. A countable family of dense open sets whose intersection lies in the target
complement gives II a move-counting avoidance strategy.
For I, a nonmeagre Baire-property target contains U intersect S for a nonempty
open U and residual S. Intersecting each response with its next dense-open
requirement and a shrinking metric ball yields bounded nested closed traps.
Completeness supplies their common point; the next trap lies in the preceding
open response. No closed ball is assumed compact. Exact joint execution rules
out simultaneous winners and yields the two iff statements by category dichotomy.

This formalizes the classical recall in Grädel–Leßenich, [CSL2012](https://doi.org/10.4230/LIPIcs.CSL.2012.305),
printed p.306, Theorem1.1/Corollary1.2. Our explicit complete-metric/Baire-property
scope is narrower than their broad informal topological wording. Their graph,
Muller, positional and strategy-memory results are not formalized. The original
Banach/Oxtoby proof was not consulted. No novelty or priority is claimed.
The result is useful infrastructure for researchers in descriptive set theory,
general topology and infinite games: it exposes the category criterion behind
winning strategies while separating target regularity from general determinacy.
It supplies a reusable formally checked classical research-note development,
not a claimed new theorem or an automated graph-game solver.

Full-history conventions credit the existing Oxtoby and Choquet sources; the
closed-trap argument is adapted from Choquet source51def6feb5e4469cce2396dfa4c9fa4f3b933d82
under Apache-2.0. All proof code needed here is local or canonical Mathlib;
Challenge imports no other project-specific module. This target adds target-set
payoffs and determinacy beyond prior unrestricted-game/product packages.

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
These established project-authorized roles are separate. OpenAI Codex authored
substantive proof, test and packaging code. Reviews are independent internal AI
reviews; no human or external peer review is claimed. License: Apache-2.0.
Classification: math.GN; MSC2020 54E52,91A44,03E15.

The package owns its Lean v4.35.0-rc2 toolchain and exact Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55
lock. Run `lake build` inside this directory through the verified launcher.
[Material imported meanings](MATERIAL-DEFINITIONS.md) retain exact pinned source,
upstream attribution, Borel/category and metric/uniform dependency expansions.
[Lean core evidence](CORE-DEFINITIONS.md) retains the exact List/length meanings.
Both ChallengeTests and SemanticTests independently compile literal contracts,
proved semantic bridges and payoff/empty/history boundary examples.
See [verification scope](VERIFICATION.md) and [review scope](REVIEW.md).
Every completed build, axiom audit, protected full check, renderer and final review
must be supported by its own immutable external exact-source receipt. Static
checks do not establish semantic completeness or editorial decisions. Current
private attempts and public registration remain unconfirmed. This task prepares
manual fields and performs no registry intake or registration.
