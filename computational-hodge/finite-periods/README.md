# Harmonic representatives and computational-path periods

This project proves a degree-one discrete Hodge theorem for the user's scoped,
endpoint-changing computational-path model. It constructs actual cochains,
coboundaries, quotient cohomology and harmonic representatives, and relates
them to additive periods on actual rewrite classes of paths. It is separate
from the conditional algebraic double-complex pilot.

## Mathematical contract

Let `S` be a continuous geometric step system on any topological space `A`,
with a **finite** primitive-step type `E`. A step has specified source and
target and an actual continuous interval path between them. `GeometricTrace`
builds finite computational paths by identity, primitive steps, composition
and reversal. A presentation `P` declares parallel-trace rewrite generators,
each with an endpoint-fixed geometric homotopy witness. All fourteen upstream
scoped rewrite constructors are retained literally.

The real degree-one space is `C1 = EuclideanSpace R E`, with its actual standard
inner product. Signed path periods are defined by recursion:

```
period(1_a) = 0,     period(e) = omega(e),
period(p;q) = period(p) + period(q),
period(p^-1) = -period(p).

d0(f)(e) = f(target(e)) - f(source(e)),
d1(omega)(p ~ q) = period(p) - period(q).
```

`Cell P` includes **every** named rule witness, not merely a selected finite
list. The rule set and `A` may be infinite. No inner product on `A -> R` or on
the degree-two function space is assumed. Telescoping proves `d1 o d0 = 0`.
With `Z = ker d1` and `B = range d0`, the actual quotient is
`H1 = Z / (B.comap Z.subtype)`. Harmonic cochains are `Z` intersected with the
orthogonal complement of `B`. Finite dimensionality of `C1` supplies the
orthogonal projection; no Hodge decomposition is inserted as a hypothesis.

The constructed representative is `omega - projection_B(omega)`. It is unique
in its class and gives an actual linear equivalence from `H1` to harmonic
cochains. Its periods equal those of the original closed representative.
Periods descend independently through scoped path rewriting and the cochain
quotient, and are additive under the actual descended path composition.

The separation result quantifies over **all basepoints**: a cochain is exact
if and only if every computational loop period vanishes. The reverse direction
constructs a potential from trace integrals, one component at a time, using
classical choice. No connectivity, nonemptiness or assumed potential is added.
Thus all-basepoint loop periods determine cohomology and harmonic representatives.

## Selected results

The literal contracts and required definition values are fixed by
`comparator.json` (sixteen theorems and twenty-five definitions).

| Theorem suffix | Meaning |
| --- | --- |
| `period_d0` | Actual coboundary integrals telescope to endpoint values. |
| `d1_d0` | Consecutive actual coboundaries compose to zero. |
| `closed_iff_rewrite_invariant` | Closedness is equivalent to period invariance under the whole scoped rewrite relation. |
| `quotientPeriod_compose` | Closed periods are additive on actual path quotient composition. |
| `unique_harmonic_representative` | Each closed cochain has exactly one harmonic representative modulo actual boundaries. |
| `hodgeEquiv_preserves_periods` | The constructed cohomology/harmonic linear equivalence preserves loop periods. |
| `periodPairing_compose` | The pairing on both quotient spaces is additive in path composition. |
| `exact_iff_zero_loop_periods` | Every loop period vanishes exactly for actual coboundaries. |
| `harmonic_determined_by_periods` | All-basepoint loop periods determine a harmonic cochain. |
| `periodPairing_separates` | The actual period pairing separates cohomology classes. |
| `ParallelEdges.omega_harmonic` | The concrete anti-diagonal cochain is harmonic. |
| `ParallelEdges.omega_loop_period` | Its two-edge loop period is exactly two. |
| `ParallelEdges.omega_not_exact` | That cochain is not a coboundary. |
| `ParallelEdges.loop_geometrically_null` | The same loop is geometrically null-homotopic in the real line. |
| `ParallelEdges.parallel_harmonic_zero` | Adding the named parallel-edge rewrite forces every harmonic cochain to zero. |
| `ParallelEdges.rewrite_changes_periods` | The named rewrite holds in the enlarged presentation and fails in the free one. |

## Nonvacuity and boundary

Two distinct generators both realize the actual straight segment from zero to
one in the real line. Without a named identification, `(1,-1)` is harmonic and
has period two on the first edge followed by the inverse second edge. Adding
the geometrically sound named identification kills that harmonic space. This
tests dependence on the rewrite presentation, rather than on a decorative
step count.

The nonzero loop is nevertheless geometrically null-homotopic. The free
presentation is therefore not geometrically complete. Its cohomology must
**not** be identified with ambient de Rham or singular cohomology of the real
line. Geometric completeness and a suitable cohomology comparison remain
additional theorems. Smooth forms, Hodge stars, Laplacian operators, analytic
Hodge theory, compact Kahler manifolds and continuum limits are not proved here.
No mathematical novelty or editorial acceptance is claimed.

## Source, proof visibility and validation

`SourcePaths.lean` is a minimal literal port of three definition excerpts from
`TopologicalComputationalPaths` at
`ea1367d99c7d2f3794f1299cce5b18379e9093a7`. The exact source/excerpt hashes,
namespace-closure adaptation and original Lean4.32 pin are recorded in
`source-provenance.json`. Upstream MIT attribution is retained in
`SOURCE-LICENSE.txt`; the new development follows the repository's Apache-2.0
license. The same definitions were also checked against
`ComputationalPathsLean` at `257c659b7973aeda900d86a5da73b208712c7523`.
Raw equality-indexed trace metadata and existing degree-shadow Hodge
certificates are not used as form or cochain operator laws.

The modular files contain complete proofs. `scripts/make_surface.py` copies
every declaration and complete proof to separately compiled, Mathlib-only
`Challenge.lean` and `Solution.lean`. They share one disclosed implementation,
not independent proofs. Nothing is pruned to hide mathematical content.
`surface-manifest.json` fixes the ordered source hashes and generated bytes.

The pins are Lean4.35.0-rc2 (compiler11acb17) and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Run locally:

```sh
lake build
python3 scripts/make_surface.py --check
python3 scripts/check_package.py
```

Separate Challenge/Solution semantic bridges and three axiom-audit entrypoints
are built by default. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. Exact-source native, protected-comparison, independent-kernel,
rendering, visual and final review stages are certified by their own external
immutable receipts. Source prose alone does not certify any stage or registry
acceptance. All author-side validation is local; no hosted CI is included.

## Attribution and sources

Human author and responsible-maintainer role names continue the established
Hodge campaign assignments: Arthur Freitas Ramos, Ruy Jose Guerra Barretto de
Queiroz and David Barros Hulak. OpenAI Codex supplied the substantive new proofs
and packaging. Internal AI review is disclosed; no human proof contribution,
human mathematical review or external peer review is inferred from those roles.

The path model follows [Topological Semantics for Scoped Computational Paths,
v3](https://arxiv.org/abs/2608.04228v3), especially its separation of declared
rewrites from all geometric homotopies. The harmonic-representative argument
adapts the classical finite-dimensional construction in [Lim, Hodge Laplacians
on Graphs, v4](https://arxiv.org/abs/1507.05379v4), sections2 and5.
[Jiang-Lim-Yao-Ye, v2](https://arxiv.org/abs/0811.1067v2), sections4.2-4.3,
supplies broader cochain-Hodge context. No full graph-ranking or manifold
theorem from those papers is claimed formalized.
