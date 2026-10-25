# Harmonic characters of represented computational loops

This project connects the user's actual endpoint-changing computational paths
to algebraic real characters of their realized loops in the ambient fundamental
group. It continues the finite Hodge bridge from PR59–62 with a period
correspondence and a concrete nonzero circle example.

Let `S` be a continuous geometric step system with finite primitive generator
type `E`. The ambient space `A` is arbitrary. Fix a root `a`. An active point is
the root or a source or target of a primitive generator. `Rooting S a` supplies
a computational trace from `a` to every active point, normalized at the root.
It supplies no trace to arbitrary ambient points. Realized paths and homotopies
remain in **ambient `A`** and may leave the finite active endpoint set.

The rooting hypothesis requires all computational endpoints to lie in the root
component. Other ambient points may be unreachable. Without this hypothesis,
characters at one root could miss harmonic cycles in another computational
component, so the global uniqueness assertion would be false.

## Actual subgroup and ordinary characters

`traceClass p` is the endpoint-fixed homotopy class of the realized trace `p`.
`representedGroup S a` is the actual subgroup of `FundamentalGroup A a` whose
elements have a computational-loop representative. Closure under identity,
multiplication and inverse is proved using actual trace operations.

`Characters S a` consists of functions `χ : representedGroup S a → ℝ` with
`χ 1 = 0` and `χ (g*h) = χ g + χ h`, using ordinary pointwise vector operations.
`characterEquivHom` identifies these explicitly with usual group homomorphisms
to `Multiplicative ℝ`, which tags **real addition** as multiplication. These are
algebraic characters; continuity is neither required nor inferred. The subgroup
may be infinite and nonabelian. Mathlib's fundamental-group multiplication
reverses path concatenation, and the proofs explicitly use real commutativity.

## Period correspondence

Let `G` be the complete geometric presentation: a generating relation is an
actual endpoint-fixed homotopy between realized traces. In the finite Euclidean
edge space, `Closed G = ker d1`, `Exact S = range d0`, and
`Harmonic G = Closed G ∩ (Exact S)ᗮ`. The coboundary is the actual endpoint
difference `d0 f(e) = f(tgt e) - f(src e)`.

The complete proofs establish:

- A geometrically closed cochain gives a well-defined character of the actual
  represented subgroup. On **every** computational loop `p` at `a`, its value is
  the actual signed edge period `period p ω`.
- Every character is obtained from the explicit coefficients
  `ωχ(e) = χ([T(src e) · e · T(tgt e)⁻¹])`. The reconstructed cochain respects
  all actual geometric homotopies, not merely a supplied list of rewrites.
- All based computational-loop periods vanish exactly when the cochain is an
  actual endpoint gradient. The proof constructs a potential from connector
  periods on active points, with value zero elsewhere. Traces between inactive
  points have zero period; no inaccessible connector is silently assumed.
- Integration is a linear equivalence
  `harmonicCharacterEquiv T : Harmonic G ≃ₗ[ℝ] Characters S a`.
  Its forward map is actual loop integration. Every character has a unique
  harmonic representative, and the equivalence is independent of `T`.

Harmonic representatives are constructed using finite-dimensional orthogonal
projection. Existence, exactness and the period bridge are proved rather than
assumed. The inverse is classical/noncomputable, not a numerical procedure.

## Concrete circle witness

The ambient space is `AddCircle (1 : ℝ) = ℝ / ℤ`. The only primitive generator
is the actual continuous loop `t ↦ (t : AddCircle 1)`, based at zero. Its active
endpoint set is a singleton, but its realized path travels through the circle.

The ordinary quotient map `ℝ → AddCircle 1` is a covering map, proved in pinned
Mathlib. Define winding to be the endpoint of the path lift starting at zero.
Lift uniqueness proves translation of lifts; lift concatenation proves
additivity, and homotopy lifting proves invariance. The standard loop lifts to
`t ↦ t`, so its winding is **exactly one**. Restricting this constructed ambient
character to the actual represented subgroup yields a nonzero character and
therefore a nonzero harmonic representative. No nonzero character is supplied
as a hypothesis. A full `π₁(circle) ≃ ℤ` classification is not claimed.

## Scope, sources and audience

This is a discrete degree-one period correspondence for represented
computational loops. Classical fundamental-group/cohomology and finite Hodge
ideas are credited to [Hatcher, Sections 2.A and 3.1](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)
and [Jiang–Lim–Yao–Ye](https://arxiv.org/abs/0811.1067v2). The precise scoped
path model comes from [Topological Semantics for Scoped Computational Paths,
version 3](https://arxiv.org/abs/2608.04228v3); its four paper authors are distinct
from this project's explicitly recorded authors and maintainers.

The concrete connection between trace realization, actual ambient loop
characters and finite harmonic representatives is relevant to researchers in
computational path semantics, discrete cohomology and formalized algebraic
topology. Its value is the complete source-faithful bridge and the exposed
connectivity boundary, rather than novelty of generic linear algebra or group
character theory. No novelty or registry/editorial acceptance is promised.

There is no assertion that every ambient fundamental-group class has a
computational representative. There is no identification with ambient singular
or de Rham cohomology, analytic/Kähler Hodge theory, higher-degree result,
continuous-character classification, numerical algorithm or geometric rewrite
completeness theorem. No such bridge is assumed in a disguised hypothesis.

## Source and verification

Lean `4.35.0-rc2`, compiler `11acb17ec6b07a8f9e9173e6845197929540936b`,
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned.
`SourcePaths`, `Periods` and the complete retained `Harmonic` declarations are
mapped to immutable predecessor Git bytes in `base-provenance.json`.
`source-provenance.json` and `SOURCE-LICENSE.txt` retain exact upstream MIT
attribution. Mathlib remains Apache-2.0; its covering and lifting results are
credited alongside the prior computational-path circle-lifting strategy.

The eight ordered mathematical modules contain all proofs.
`scripts/make_surface.py` copies every declaration and complete proof into
`Challenge.lean` and `Solution.lean`, removing only module/import/visibility
directives. They share one implementation and are not independent proofs.
Comparator selects 28 theorems and 21 definitions, with only `propext`,
`Classical.choice`, and `Quot.sound` permitted. The material imported-definition
inventory and separately compiled semantic audits expand the actual predicates.

All required validation is local under repository policy. Exact-source native,
interface and definition-value checks, dependency provenance, negative controls,
independent kernels, original canonical rendering, browser inspection and final
packet/independent review outcomes have separate immutable receipts. Compilation
or source hashes alone establish neither all gates nor registration. The
preferred surface-size warning remains visible; the hard limits are unchanged.

AI proof and tooling contributions are disclosed in `formalization.yaml`.
Internal AI review is distinguished from human or external peer review.
Existing projects, historical receipts and registry intakes are unchanged.

The inherited harmonic projection keeps every retained declaration statement and
operator formula. Its two record-law tactic proofs are replaced by explicit
`congrArg` equality chains, `add_sub_add_comm` and `smul_sub`. This avoids a
module-dependent generated helper proof detected by the unchanged strict
comparator. The old failure is preserved; `base-provenance.json` records both
complete source adaptations. No comparison rule, proof contract or resource
limit is weakened.
