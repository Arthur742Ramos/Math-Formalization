# Analytic circle Hodge decomposition and computational periods

This project connects genuine ordinary line integrals on the flat real circle
to the user's actual geometric computational paths and finite harmonic cochains.
It extends the finite ambient-character bridge with nonconstant continuous
coefficients and a constructed analytic potential. It is an explicit
one-dimensional coefficient model relative to the standard flat coordinate.

For an actual continuous function `α : C(AddCircle (1 : ℝ), ℝ)`, let its cover
pullback be `f(x) = α([x])` and mean `m = ∫₀¹ f`. The proof constructs
`P(x) = ∫₀ˣ f - x*m`, proves `P` is C1 and 1-periodic, and descends it through
the actual quotient to a normalized continuous circle potential. Its cover
derivative is `f-m`. Thus every coefficient decomposes as a constant harmonic
coefficient plus an actual potential derivative. Analytic exactness is
equivalent to mean zero; differentiability together with derivative zero is
equivalent to constancy. The harmonic constant is unique modulo analytic
exactness. Ordinary integral orthogonality gives

```text
∫₀¹ f(x)^2 dx = m^2 + ∫₀¹ (f(x)-m)^2 dx.
```

For every globally C1 real lift `ℓ` with `ℓ(0)=0` and `[ℓ(1)]=0`, the actual
ordinary line integral is defined as `∫₀¹ f(ℓ(t))*ℓ'(t) dt`. Chain-rule FTC,
the periodic primitive and actual covering-lift uniqueness prove that this
equals `m` times the winding of its projected ambient loop class. Every
ambient circle loop class has a C1 straight integer-lift representative;
existence is proved using actual winding integrality and injectivity.

The primitive computational system is the actual unit-winding circle loop.
Its finite traces retain actual composition/reversal and are realized as
ambient paths, with actual endpoint-fixed homotopy. The harmonic cochain is
constructed using the retained rooted-loop reconstruction applied to the
weighted ordinary winding character. For every computational trace, every C1
representative of its actual class has line integral equal to its signed
computational period. This harmonic cochain is unique with those periods.
Every finite harmonic cochain occurs, and two continuous coefficients yield
the same cochain exactly when their difference is analytically exact.

`ExactCoefficient` uses an actual circle potential with C1 real cover. It is
distinct from the finite endpoint-difference space `Exact circleSystem`,
which is proved zero. Their relationship is the proved kernel of the mean
harmonic-cochain map, not an equality between these spaces. Harmonicity
explicitly includes differentiability: Lean's derivative is totalized to zero
outside its differentiability domain. All integral uses have proved
integrability; no conclusion is obtained from the integral's default zero.

## Scope and attribution

The user's [computational-path paper](https://arxiv.org/abs/2608.04228v3)
and pinned TopologicalComputationalPaths source supply the actual path model.
Existing circle/torus classification is credited prior work. The four paper
authors are distinct from the project's recorded authors and maintainers.
Classical degree-one/discrete context is credited to
[Hatcher](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) and
[Jiang–Lim–Yao–Ye](https://arxiv.org/abs/0811.1067v2).
Pinned Mathlib supplies actual ordinary Bochner integration, calculus,
quotient descent, covering and finite Euclidean algebra. Complete literal
source mappings, upstream headers and critical imported contracts are retained.
The focused audience is formalized calculus, computational-path semantics
and degree-one Hodge theory; novelty or editorial acceptance is not promised.

Raw concatenated trace paths may have corners. This package proves existence
of C1 representatives and independence among such representatives; it does
not directly integrate every raw trace realization. There is no manifold
cotangent bundle, full differential-form/de Rham complex or comparison,
Laplacian, higher-dimensional/Kähler theorem, L2 quotient norm construction
or numerical algorithm. Classical lifts and inverse constructions are
noncomputable. No assumed analytic/computational bridge is introduced.

## Source and checks

Lean `4.35.0-rc2`, compiler `11acb17ec6b07a8f9e9173e6845197929540936b`,
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned.
Ten ordered mathematical modules contain every proof. `make_surface.py`
copies every declaration and complete proof into both Challenge and Solution,
removing only module/import/visibility directives. They share one
implementation, not independent proofs. The comparator selects 38 theorems
and 28 definitions, with literal definition values, closure comparisons,
random aliases and four negative controls. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted. Source-provenance and material-definition
consistency checks complement separately compiled semantic audits.

All required validation runs locally, with no author-hosted CI. Run
`lake build`, `python3 scripts/check_package.py --upstream-root PATH`, and
`python3 scripts/check_interfaces.py` in this package; run the repository's
full test suite and unchanged exact-commit canonical CLI according to root
AGENTS.md. Independent review, fresh kernel replay, canonical full and render,
browser review and final packet checks remain separate source-bound gates.
Their outcomes belong in immutable external receipts; this source document
does not claim complete release or registry acceptance.
