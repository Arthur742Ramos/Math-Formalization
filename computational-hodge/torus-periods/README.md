# Ambient torus characters from computational harmonic periods

For a finite discrete coordinate type `E`, this project connects the user's
actual geometric computational paths in `E → AddCircle (1 : ℝ)` to all ordinary
algebraic real characters of the ambient fundamental group. It extends PR63's
represented-subgroup correspondence by proving that the actual coordinate-loop
system represents every ambient loop class.

The primitives are the continuous unit-winding coordinate loops at zero.
Their realizations travel through the ambient torus, rather than a one-point
endpoint subspace. `GeometricTrace` retains actual composition and reversal;
`traceClass` is its realized endpoint-fixed path-homotopy class. `representedGroup`
is the actual subgroup of the existing ambient fundamental group with such
representatives. It contains genuine finite trace witnesses, including when
closure under integer powers is used. No generation certificate is assumed.

## Proved bridge

Circle winding is the real endpoint of the actual lift beginning at zero under
the real-to-circle covering. Pinned Mathlib's covering/monodromy theorems, with
the proved simply connectedness of the real line, give injectivity. Quotient
membership gives integral winding. Product path-class extensionality then
proves injectivity of the ambient torus winding vector. Each actual coordinate
primitive has exactly its unit coordinate winding.

Finite products of integer powers of these actual represented loops realize
every integral winding vector. This includes negative powers, zero powers and
the empty product. Applying winding injectivity proves
`every_ambient_class_represented` and `torus_represented_eq_top`.

Let `G` contain all actual endpoint-fixed homotopies between realized traces.
In the finite Euclidean coefficient space, `Closed G = ker d1`,
`Exact S = range d0`, and `Harmonic G = Closed G ⊓ (Exact S)ᗮ`.
The actual endpoint-difference operator is zero because each primitive begins
and ends at zero. All cochains satisfy all actual geometric homotopy relations:
each is reconstructed from its weighted ambient winding character using the
retained rooted-edge reconstruction proof, including its inactive-point case.
Thus `Exact = ⊥`, `Closed = ⊤` and `Harmonic = ⊤` are proved.

`harmonicAmbientEquiv` is a real linear equivalence from these actual harmonic
cochains to **all** ambient real algebraic characters. On every computational
loop its forward map equals the actual signed edge period. Every ambient
character has a unique harmonic cochain with those loop periods. Its coefficient
at `e` is precisely the character's value on the actual coordinate loop, and
for every ambient group element `g`:

```text
χ(g) = ∑ e, χ([coordinateLoop e]) * windingVector(g)(e).
```

These results require no nonempty-index hypothesis. The empty-index character
is explicitly proved zero. Finiteness is essential: a finite word cannot encode
nonzero windings in infinitely many coordinates. Unit-winding generators are
also essential; replacing them by higher winding loops can leave a proper
ambient represented subgroup. Discreteness of the primitive-index topology is
explicit, rather than inferred from finiteness of an arbitrary chosen topology.

## Scope and attribution

This is a finite degree-one computational harmonic/ambient-character bridge.
The user's pinned `FiniteTorusWinding.lean` already develops extensive finite
torus classification and matrix naturality. Neither classification, arbitrary
finite indexing nor classical topology is claimed as new. The contribution
here is the complete connection from actual computational trace realization
and actual coefficient operators to all ambient characters, with proved
ambient completeness and explicit inverse coefficients.

The path model is attributed to [Topological Semantics for Scoped Computational
Paths, version 3](https://arxiv.org/abs/2608.04228v3) and the user's
TopologicalComputationalPaths repository. The four paper authors are distinct
from this project's recorded authors/maintainers. Classical context is credited
to [Hatcher, Sections 2.A and 3.1](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)
and [Jiang–Lim–Yao–Ye](https://arxiv.org/abs/0811.1067v2).
The focused audience is computational-path semantics, discrete periods and
formalized geometric topology. No novelty or editorial acceptance is promised.

There is no identification with ambient singular or de Rham cohomology,
continuous-character theorem, analytic/Kähler Hodge theorem, higher-degree
result, matrix isometry or numerical algorithm. Classical lifts and inverse
equivalences are noncomputable. All geometric relations are actual ambient
homotopies, with their obligations proved rather than supplied as a bridge.

## Source and checks

Lean `4.35.0-rc2`, compiler `11acb17ec6b07a8f9e9173e6845197929540936b`,
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned.
`source-provenance.json` records literal upstream trace, continuous-system and
scoped-presentation excerpts. Unused scoped rewrite closure is omitted; this
package does not claim to retain its fourteen constructors.
`base-provenance.json` maps all retained predecessor declarations and complete
proof slices, including reconstruction and circle winding, with explicit
import/namespace adaptations. MIT source attribution and Apache-2.0 dependency
attribution are retained.

Nine ordered mathematical modules contain all proofs. `make_surface.py` copies
every declaration and proof into `Challenge.lean` and `Solution.lean`, removing
only module/import/visibility directives. They share one implementation and
are not independent proofs. The comparator selects 26 theorems and 25
definitions; only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Material imported definitions and separate semantic audits expose the actual
operators, ambient group, quotient, character laws and forward integration map.

Validation is local under repository policy: native build, exact interfaces
and definition values, dependency provenance, four negative controls, random
module alias, standard axiom closure, independent kernels, original canonical
CLI, unmodified rendering, browser inspection and final packet/review outcomes
have separate immutable receipts. Hard source/output limits remain unchanged.
Source hashes and compilation alone do not establish all acceptance gates.
AI contributions are disclosed; internal AI review is distinguished from human
or external peer review. Existing projects, receipts and intakes are preserved.
