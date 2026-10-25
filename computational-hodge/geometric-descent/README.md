# Geometric realization kernel and computational-path period descent

This connects presentation homology to actual geometric realization. It proves
which classes are lost when a scoped computational-path presentation is enlarged
to identify every pair of traces whose realized paths are endpoint-fixed homotopic.

## The proved kernel

Let `S` be the user's continuous geometric step system on a topological space
`A`, with finite generator type `E`, and let `P` be a sound scoped presentation.
The actual endpoint-changing traces and all fourteen rewrite constructors are
retained. Vertices and named-rule witnesses may be infinite. No connectedness or
nonempty assumption is imposed.

`geometricPresentation S`, written `G` below, uses exactly
`Path.Homotopic (realize p) (realize q)` as its named rule predicate.
Its soundness is immediate from that concrete predicate. The complete upstream
induction proves realization soundness for every scoped rewrite derivation.

The map from `PathClass G a b` to Mathlib's actual
`Path.Homotopic.Quotient a b` is injective. `representedEquiv` identifies its
domain with the range of realized traces. This is an equivalence of types over
**represented** path-homotopy classes, not a homeomorphism or a claim that every
ambient path is represented. The upstream universal-presentation construction
and represented-class comparisons are attributed setup, not the new result.

The main geometric argument proves

```
Relations G = span_R { wordChain(loop) | realize(loop) ~ constant_path }
```

For homotopic traces `p,q`, the actual loop `p;reverse(q)` is nullhomotopic by
horizontal composition and path cancellation. Its word chain is precisely the
difference `wordChain p - wordChain q`. Conversely, each actual nullhomotopy is
a named `G` rule relating its loop to the identity. Both inclusions of the span
equality are proved from these witnesses.

Since every `P` rule is geometrically sound, the literal relation subspace of
`P` lies in that span. This constructs

```
pi : ChainH1 P ->_linear ChainH1 G
```

and proves surjectivity. Its kernel is **exactly** the real linear span of the
original `P` homology classes of all nullhomotopic computational loops.
These are actual cycle/boundary quotients from PR60. Finite support of each chain
does not impose finiteness on vertices or named rules.

## Period and cohomology descent

Periods respect all geometric homotopies between represented traces if and only
if they vanish on every nullhomotopic computational loop. The same condition is
equivalent to being closed for `G`.

Cohomology goes in the opposite direction:

```
iota : H1 G ->_linear H1 P
```

It is injective and is literally identity on underlying closed-cochain
representatives. The coefficient pairing satisfies
`pairing_P(iota(c),z) = pairing_G(c,pi(z))`.
The image of `iota` consists exactly of the classes whose period functional
annihilates `ker pi`. This is proved on the actual two quotients, without
assuming a geometric-completeness or duality bridge.

A harmonic cochain for `P` already descends unchanged precisely when its periods
on nullhomotopic computational loops vanish. A general orthogonal correction can
change its old cohomology class; this project does not claim otherwise.

The checked constant-path example makes the distinction concrete. The one-vertex,
one-generator free presentation has a nonzero real homology generator. That
generator realizes the actual constant path and maps to zero under `pi`.
Its unit-period cohomology class is outside the image of `iota`.

## Scope and source identity

This proves a geometric realization **kernel and descent criterion**. A zero
homology kernel only identifies real relation spans; it does not establish
path-level geometric completeness. No ambient singular/de Rham identification,
integral homology or raw-loop abelianization theorem, analytic/Kahler Hodge
theorem, numerical solver, novelty or registry acceptance is claimed.

The predecessor is exact verified source
`4e31c311d97be4e2eb8c8fe6b8f5ec1ffc3c2956` from PR60.
`base-provenance.json` records a dependency-closed subset of its complete
declarations and proofs, including literal source ranges, file/excerpt hashes
and explicit adaptations. One inherited boundary proof keeps its exact statement
and replaces normalization automation with public additive identities so strict
cross-module comparison can check it; both full proof versions and their hashes
are recorded. Unused predecessor theorem families
are outside this package; all used definitions and complete proofs remain.
The earlier packages and receipts are preserved.

`source-provenance.json` binds the three original upstream definition excerpts.
`realization-provenance.json` binds the complete literal `ScopedRwEq.sound`
proof. MIT attribution remains in `SOURCE-LICENSE.txt`. The new development is
Apache-2.0. `MATERIAL-DEFINITIONS.md` retains exact pinned imported definitions
and explains the semantic and compiler-infrastructure boundaries.

`scripts/make_surface.py` copies every declaration and complete proof from all ten
ordered mathematical modules into each standalone interface, removing only
module/import/visibility directives. There is no further source pruning.
Challenge and Solution share one disclosed implementation; they are not
independent proofs. Their exact bytes are bound by `surface-manifest.json`.

The exact toolchain is Lean4.35.0-rc2, compiler11acb17, with Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Comparator selects twenty-four
theorems and twenty-one definitions. Three transitive axiom audits permit only
`propext`, `Classical.choice` and `Quot.sound`. Separate semantic modules check
the actual imported predicates and quotient computations through Challenge and
Solution. No holes or new axioms are used.

Run author-side validation locally:

```sh
lake build
python3 scripts/make_surface.py --check
python3 scripts/check_package.py
python3 scripts/check_interfaces.py
```

Native, protected canonical, independent-kernel, renderer, browser and review
outcomes belong to separate immutable source-bound receipts. Source prose
certifies no publication stage or registry decision. Author-hosted CI remains
retired.

## Attribution and context

Human author and responsible-maintainer roles continue the established campaign
assignments: Arthur Freitas Ramos, Ruy Jose Guerra Barretto de Queiroz and David
Barros Hulak. OpenAI Codex supplied the substantive new proofs and packaging,
with separate internal AI scope/source/evidence review. These roles do not infer
human proof contributions or human/external peer review.

The definitions and existing realization setup follow
[Topological Semantics for Scoped Computational Paths, v3](https://arxiv.org/abs/2608.04228v3)
and its pinned implementation. The predecessor supplies actual presentation
chain homology and its coefficient pairing. Classical context is
[Hatcher, section1.1 and Theorem2A.1](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf);
the ambient topological identifications there are not claimed here.
