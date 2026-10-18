# Fréchet–Urysohn Σ-products of first-countable spaces

Given arbitrary topological factors `X i` and a specified point `b` in their
product, the **Σ-product** consists of points differing from `b` on at most
countably many coordinates. It has the subspace topology inherited from the
ordinary product, not the box topology. We prove that if every factor is
first-countable, this space is Fréchet–Urysohn: each point in the closure of
any set is the limit of a sequence drawn from that set.

The index is arbitrary, including empty, and its universe is independent of
the factor universe. The main result uses no Hausdorff, T₁, compactness,
metrizability, separability or countable-index hypothesis. The supplied
basepoint is an explicit premise; this does not assert existence of a
basepoint when a factor is empty. Countable support is not finite support.

## Proof content

The main proof chooses antitone countable neighbourhood bases in each factor.
It enumerates the support of the target and of every selected point. At stage
`n`, a finite set contains the first `n+1` enumerated coordinates of the target
and of each of the first `n` chosen points. Closure supplies a new point that
meets the depth-`n` neighbourhood requirements on these coordinates.

Any coordinate appearing in the target or a chosen point is eventually
scheduled at every depth. A coordinate never appearing in any such support
is constantly the basepoint, hence already equals the target. This proves
coordinatewise convergence and therefore actual product/subtype convergence.
The empty-index case is handled separately without choosing a coordinate.

The companions provide countable tightness with an explicit countable subset,
Fréchet–Urysohnness of all subspaces, density of the Σ-product in the full
product, and a precise contrast with large Boolean cubes. In products of
T₁ spaces, the closure of a countable set of countably supported points uses
one countable set of coordinates, so the Σ-product is sequentially closed.
It is dense and proper in an uncountable discrete Boolean cube; the full cube
is therefore not sequential. The T₁ premise belongs to these ambient closure
statements and is not silently imposed on the main theorem.

## Selected declarations

- `SigmaFrechet.exists_sequence`
- `SigmaFrechet.frechetUrysohnSpace`
- `SigmaFrechet.countable_closure_support`
- `SigmaFrechet.isSeqClosed_countableSupport`
- `SigmaFrechet.countable_tightness`
- `SigmaFrechet.subspace_frechetUrysohnSpace`
- `SigmaFrechet.dense_countableSupport`
- `SigmaFrechet.boolean_cube_not_sequential`

Selected definitions: `SigmaFrechet.deviationSupport` and
`SigmaFrechet.SigmaProduct`; their literal bodies are given in
[DEFINITIONS.md](DEFINITIONS.md) and tested across independent imports.
The proof module and fully proved Challenge are identical; Challenge imports
only Mathlib. Solution publicly imports the proof module. No prior campaign
project is an import dependency.

## Mathematical sources and limits

Gabriyelyan–Reznichenko, [*On k_R-spaces and s_R-spaces*,
arXiv:2506.15206v1](https://arxiv.org/pdf/2506.15206v1), printed pp.6–7,
recalls the first-countable **finite-support** σ-product Fréchet–Urysohn result
before Proposition4.4, crediting Noble1970. Page6 explicitly defines its lower
case σ by finite support. This is a directly consulted restricted statement;
our independent proof establishes the classical **countable-support**
formulation and dispenses with that paper's global Tychonoff convention.
We do not claim that this source states the exact generality proved here.
Its new k_R/s_R results are not formalized.

Avilés–Krupski, [arXiv:2411.10035v3](https://arxiv.org/pdf/2411.10035v3),
printed pp.1–2, supplies the exact countable-support definition and a research
setting involving Corson/Eberlein compacta and Lindelöf scattered subspaces.
Its σ-compactness theorem is not formalized. Marciszewski–Plebanek–Zakrzewski,
[arXiv:2107.02513v5](https://arxiv.org/pdf/2107.02513v5), printed pp.1–4 and
Proposition4.7, supplies Corson/Boolean-algebra/Banach-function-space context
and a use of sequential closure. Its new κ-Corson results are not formalized.
These papers establish a concrete research audience rather than a claim of
new mathematics in this classical theorem.

Noble's original, *The continuity of functions on Cartesian products*,
Trans.AMS149(1970),187–198, DOI10.1090/S0002-9947-1970-0257987-5, was identified
bibliographically through the consulted recall. Its official full text was
inaccessible and not consulted. Neither an original theorem number nor a
reproduction of the original proof is asserted. No novelty, priority,
collectionwise-normality or W-space claim is made. First-countable factors
are essential to the scope: arbitrary Fréchet–Urysohn factors are not claimed.

## Toolchain, checks and current gates

This package owns its toolchain and lockfile: Lean4.35.0-rc2, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`, Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Its nine dependency records match
the preceding package; no global toolchain or existing package pin is changed.

Run from this directory:

```bash
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

Six modules cover the proofs, independent Challenge and Solution contracts,
ten transitive dependency audits and semantic cases: empty and real index,
lifted index universe, non-T₁ first-countable factors, arbitrary nonzero
basepoint, literal definition values and a genuinely uncountable Boolean cube.
See [REVIEW.md](REVIEW.md) for the dated review scope and limits.

Canonical full mechanical verification **passed** for exact source
`10f8b9075144c51468729b9b620c46b739c0a680` and
`topology/sigma-product-frechet/comparator.json`, SHA-256
`a88221925c316500fd5706a6bfc0144b30e70321ccfa05ae509fb37b8c177a5e`.
[Palomar run 39085577215](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39085577215)
records successful protected comparison and con-ron, NanoDa and Lean default
kernel checks; con-ron verified 7,125 declarations. The report covers all eight
selected theorems and both definitions. Canonical Challenge rendering
[separately passed in run 39083465499](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39083465499)
for that same source. Browser visual review is not claimed.

These receipts certify the explicitly named snapshot, not arbitrary later
commits. Before intake of a later commit, its own exact-source full report
must pass. The provenance account can remain fixed while that report records
the new commit, avoiding a status-edit/verification cycle. See
[VERIFICATION.md](VERIFICATION.md) for the receipt hashes and scope.
Editorial review and registration are separate; neither is inferred from a
passing mechanical or rendering report. A new canonical runner job still
requires specific approval if its pinned installer would load the temporary
AppArmor exception. The cloud-host restriction is not bypassed.

No equivalent was found in the pinned Mathlib checkout, sixteen-project
repository catalog or complete dated revision332/598-entry public snapshot
captured2026-10-17 at16:05UTC. This is bounded overlap evidence; fresh global
registry clearance, private-attempt reconciliation and current protocol/proof
capability remain unresolved. No current private intake, editorial acceptance or registration status is inferred from these public checks.

## Attribution

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
These are separately confirmed roles carried forward under the standing
campaign. OpenAI Codex authored substantive proofs, tests and packaging;
human names do not imply invented proof contributions. Reviews are independent
internal AI reviews; no human review is claimed and no external peer review or
Palomar editorial outcome is asserted. Classical mathematics, sources and
upstream Lean/Mathlib infrastructure retain attribution. License: Apache-2.0.
