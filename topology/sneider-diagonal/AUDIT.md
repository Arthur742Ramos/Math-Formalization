# Proof and contract audit

The selected theorem types use ordinary `Set.diagonal`, `IsGδ`, `𝓝ˢ`,
`CompactSpace`, `NormalSpace`, `T2Space` and `MetrizableSpace` from the pinned
canonical Mathlib. No alternative topology or custom metric predicate is used.

The general basis theorem explicitly proves three facts: each `V n` is a
closed neighborhood, its total intersection equals `K`, and finite
intersections are cofinal in the entire neighborhood filter. The last fact
uses compactness and is essential. The empty finite intersection is `univ`;
no nonempty-index or nonempty-space premise is introduced.

For the diagonal, compact Hausdorffness makes the square compact and normal,
and its diagonal closed. `uniformSpaceOfCompactR1` defines its uniformity to
be exactly `𝓝ˢ (diagonal X)` and retains the supplied topology. Countable
neighborhood generation therefore implies uniform metrizability. The chosen
metric's topology equality is definitional and checked in semantic probes.

`AxiomAudit.lean` prints every selected declaration's transitive axiom
closure. `SemanticTests.lean` checks empty/full closed sets, empty spaces,
arbitrary universes, product topology and exact metric topology, and an
indiscrete compact example. `ChallengeTests.lean` checks the Challenge's
selected signatures separately from the Solution import. No file combines
those duplicate declarations.

The package checker validates pins, contract names, author/maintainer
metadata, frozen source hashes, source module/line limits, hole-free source
and the transitive axiom allowlist. It performs no build, network access,
security step, Comparator or registry operation.

A local Lean build and ordinary hosted Lean CI establish only the checks they
actually execute. Full canonical Comparator/NanoDa/con-ron verification and
Challenge rendering are outstanding until their immutable reports pass.
The host UID-map restriction is preserved; no local Comparator bypass is
attempted. The pinned hosted installer conditionally loads a path-specific AppArmor
profile granting user namespaces to its temporary bubblewrap executable. The
user approved exactly that operation on the disposable verification runner.
Other security changes remain excluded. Full preflight uses one exact source
and pipeline pin, with existing runs reconciled before launch.
