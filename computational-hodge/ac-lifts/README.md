# Absolutely continuous computational circle periods

This project extends ordinary integration from finite computational traces to
arbitrary absolutely continuous real lifts of based loops on the explicit flat
unit circle. No finite or countable exceptional set, global Lipschitz bound or
supplied-integrability hypothesis appears in the lift contract.

`ACLift` is the actual subtype of real functions that are absolutely continuous
on `[0,1]`, begin at zero, and end at an integer modulo one. Regularity outside
that interval is unrestricted. `projectedLoop` is their actual continuous circle
projection. Covering uniqueness proves equality with its actual covering lift
on the interval; local equality proves derivative agreement in the interior.
Global equality with the clamped covering lift is neither needed nor claimed.

`lineIntegral` is the ordinary interval integral of the coefficient on this actual
projected loop times the derivative of the real lift. Equality with the integral
using the actual covering-lift derivative is proved. The integral is not defined
as a period sum or by choosing a smooth representative.

For a continuous real circle coefficient α, its ordinary real primitive is globally
Lipschitz by compact coefficient boundedness and the mean value theorem.
Composition with any admitted AC lift remains AC. Its derivative is integrable;
an a.e. chain rule identifies it with the weighted integrand. The genuine AC
fundamental theorem of calculus then proves

```text
lineIntegral α L = ∫₀^(L(1)) α([x]) dx = mean(α) * L(1).
```

This derives integrability and the period formula without a finite-corner
argument. The square-root primitive `rootCurve(t) = ½ ∫₀ᵗ x^(-½) dx` is proved
AC, equal to `Real.sqrt` and not Lipschitz on `[0,1]`. Its projected loop has
ordinary integral `mean α`, demonstrating a strict extension beyond Lipschitz
lifts rather than just repackaging PR66's regularity proof.

Every actual finite `GeometricTrace` in the user's unit-winding circle system
embeds using its actual covering lift, without smoothing. Its projected path
is proved literally equal to the original realization, and the new ordinary
integral equals PR66's `rawIntegral`. It equals the period of the retained actual
finite harmonic cochain `meanHarmonic`, in `Closed ∩ Exactᗮ`. If an arbitrary
AC projected loop is homotopic to a supplied computational trace, the same
harmonic-period equality follows. This homotopy is an explicit hypothesis of
that theorem; a new universal finite-trace classification is not asserted.
Harmonic uniqueness and zero-mean detection are nonvacuous via the actual unit
trace. All-AC-integral vanishing is equivalent to mean zero.

## Scope and attribution

The nonduplicate extension is AC analytic integration, not ambient circle
classification: PR64 already proves ambient torus/circle representation and
harmonic-character reconstruction. This project retains the actual endpoint
indices, binary composition/reversal and realization from the user's
[computational-path paper](https://arxiv.org/abs/2608.04228v3) and pinned source.
It builds on [PR66](https://github.com/Arthur742Ramos/Math-Formalization/tree/4891b2c040ae03aa91fa66c8e7f7075bc2643a6f/computational-hodge/trace-integrals).
Exact predecessor fragments retain complete used proofs and immutable mappings;
the unused finite-corner FTC and duplicate raw-period corollaries are omitted.

Classical AC calculus is credited to
[Rong Jia's Math418 notes, Chapter3](https://sites.ualberta.ca/~rjia/Math418/Notes/chap3.pdf)
and pinned Mathlib's actual AC predicate, composition, a.e. differentiability,
derivative integrability and FTC. Generic classical calculus is infrastructure;
the actual circle/computational/harmonic bridge is proved here. The audience is
verified nonsmooth integration and computational-path semantics. Novelty or
editorial acceptance is not promised. Upstream MIT and Mathlib Apache-2.0
attributions remain; established project authors and responsible maintainers
are recorded separately from the four paper authors. Substantive new proofs
and packaging were supplied by OpenAI Codex; independent review here is internal
AI review, not human mathematical or external peer review.

No arbitrary continuous/nonrectifiable-path integral, all-rectifiable-loop lifting
theorem, arbitrary reparameterization, general manifold/de Rham/Kähler Hodge,
Laplacian or numerical algorithm is asserted. Analytic potential/exactness belongs
to PR65. Choices of covering lifts remain noncomputable.

## Source and validation

Lean4.35.0-rc2/compiler11acb17ec6b07a8f9e9173e6845197929540936b and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 are pinned. Eleven ordered
modules generate proof-complete Challenge/Solution surfaces by removing only
module/import/visibility directives. They share one implementation, not
independent proofs. Original rendering limits and selected-panel behavior remain
unchanged; complete dependencies remain in public source and static HTML.

Run `lake build`, `python3 scripts/check_package.py --upstream-root PATH`, and
`python3 scripts/check_interfaces.py`. Native exact interfaces, literal values,
complete definition-value closure, random aliases and four rejected negative
controls supplement the unchanged protected canonical verifier. The 33 selected theorems comprise 27 new AC results and six retained predecessor
contracts used by proof fields. Selected theorem proofs retain the comparator's
normal freedom; all selected definition bodies and computational dependencies
remain exact. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Exact imported predicates and
critical theorem contracts have pinned source evidence and separate Challenge/
Solution semantic audits.

All necessary validation is local under AGENTS.md. Exact-source canonical full,
independent kernels, fresh original rendering/browser review, packet checks and
independent final review have separate source-bound receipts. This source does
not claim release completion, registry submission or acceptance from those
requirements alone.
