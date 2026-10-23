# Sierpiński's characterization of the rationals

Every nonempty countable metrizable space without isolated points is
homeomorphic to `ℚ` with its usual topology. The main statement quantifies
over an arbitrary supplied `TopologicalSpace X`. The necessary direction is
also proved: these four properties characterize spaces homeomorphic to `ℚ`.

`Countable X` means at most countable. Nonemptiness is explicit because
`PerfectSpace` permits the empty space. Its exact upstream meaning is
equivalent to all punctured neighborhood filters being nontrivial.
`MetrizableSpace X` requires a metric compatible with the supplied topology.
Neither a compatible order nor a clopen basis is assumed in the main result.
A compiled semantic bridge identifies the existing topology of `ℚ` with the
one induced by its standard coercion into `ℝ`.

This is classical mathematics: Michael Francis, *Two Topological Uniqueness
Theorems for Spaces of Real Numbers*, arXiv:1210.1008v1, Theorem 2, printed
page 2, with proof on printed page 9. No mathematical novelty or
first-formalization priority is claimed. [SOURCE-MAPPING.md](SOURCE-MAPPING.md)
records the exact source, proof divergence, bounded overlap audit and audience.

## Construction and selected contracts

Countability and metrizability first give a clopen basis. Enumerate this basis
and the points. Every nonempty clopen cell admits a genuine two-piece clopen
partition while keeping a prescribed finite set of points in either chosen
child. The proof chooses an additional point to keep both children nonempty,
including cells that miss the protected finite set.

A full binary tree schedules three tasks at each round: decide the next basis
set; send the first finitely many points to the false child; send them to the
true child. Every point's address therefore has both bits arbitrarily far
out, and every finite word labels a nonempty cell. Basis decisions separate
points. The order pulled back from lexicographic addresses is dense and has
neither a minimum nor a maximum.

The substantive topology step proves that strict rays are open by finite
first-difference witnesses. Inside each prefix cell, later bits give points
on both sides of its center; the interval between them stays in the cell.
Thus order intervals refine every original open neighborhood, proving
**equality with the original topology**. Only then is Mathlib's countable
dense-order isomorphism theorem applied to obtain the homeomorphism with `ℚ`.
No compactness of the source, completion or realization of every infinite
binary branch is assumed.

The six Comparator names, all in `SierpinskiRationals`, are:

- `countable_hasClopenBasis`: the clopen basis follows from countability and metrizability;
- `exists_binary_scheme`: constructs the full covering, deciding and protected scheme;
- `BinaryScheme.code_has_both_bits`: an exhaustive point enumeration forces both bits arbitrarily far out;
- `BinaryScheme.codeOrder_topology`: the constructed order generates the original topology;
- `nonempty_homeomorph`: the sufficient direction for nonempty countable metrizable perfect spaces;
- `nonempty_homeomorph_iff`: the full intrinsic characterization.

`definition_names` is empty. The local predicates, scheme, address and order
are fixed definitions, with no unspecified value. Challenge and proof contain
identical bytes and import only pinned Mathlib; Solution imports the proof.
The Challenge exceeds the preferred 300-line surface but is below the hard
1,000-line and 100 KiB limits and contains no proof holes.

## Attribution and verification

Project authors: Arthur Freitas Ramos, David Barros Hulak, and
Ruy Jose Guerra Barretto de Queiroz. The separately recorded responsible
maintainers are the same three people under the established campaign roles.
OpenAI Codex contributed substantive proof, tests, source audit and packaging.
Independent internal reviews are AI reviews; no human proof contribution,
human review, external peer review or registry endorsement is inferred.

Binary splitting, enumeration and address infrastructure are adapted with
Apache-2.0 attribution from the campaign's Cantor package at
`ea2e84471cdd230fd133a9e2e3b0dfc25e1a7f0f`. The present proof adds finite
protected splits, the three-stage schedule, two-sided addresses and topology
equality. There are no cross-project imports or assumed registered results.

Lean `4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned, along with all transitive
Git dependencies. Only `propext`, `Quot.sound` and `Classical.choice` are
permitted. [MATERIAL-DEFINITIONS.md](MATERIAL-DEFINITIONS.md) retains literal
upstream meanings and source hashes. ChallengeTests and SemanticTests compile
separately; they exercise `ℚ × ℚ`, the empty space and an isolated singleton.

[VERIFICATION.md](VERIFICATION.md) defines the evidence scopes. Actual tested
commits, source/configuration/metadata hashes and outcomes belong to external
immutable receipts. Native compilation and kernel checks do not establish
canonical full verification, rendering, editorial approval or registration.
No registry submission or registration is authorized by this package.
