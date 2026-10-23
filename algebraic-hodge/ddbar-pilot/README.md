# Algebraic Hodge pilot: column E1 degeneration

This independent Lean project formalizes the classical algebraic implication
from explicit image/kernel identities to E1 degeneration of the column-filtered
total complex. The pages are actual filtered quotients, the differentials are
induced by the actual total differential, and bounded convergence is proved by
stabilization of those quotient submodules. Local verification receipts are
kept separately under `verification/continuation/`; the earlier six-module
checkpoint in `verification/local-report.json` did not establish degeneration.
This is a draft research pilot, not a Palomar submission packet.

For a mathlib commuting bicomplex `K` over a field, the hypothesis
`ImageKernel K p q` is the explicit equality

```
range(h : K[p,q] → K[p+1,q]) ∩ ker(v : K[p+1,q] → K[p+1,q+1])
  = range(h ∘ v : K[p,q-1] → K[p+1,q]).
```

The global assumption is this identity for every integer `p,q`. It is one
componentwise direction of the classical d′d″ condition and suffices for this
one-filtration implication. No representative, dimension equality, or
degeneration conclusion is supplied as input. No finite dimensionality is
assumed. Rectangular boundedness means the actual vector spaces are zero
outside an integer rectangle, expressed as `Subsingleton` of their carriers.
The convergence proof uses only its weaker consequence, finite horizontal
support.

The main entrypoint is [E1Degeneration.lean](E1Degeneration.lean):

| Declaration | Proved contract |
| --- | --- |
| `exists_closed_representative` | Every actual vertical cohomology class has a representative killed by both operators. `exists_closed_correction` separately exposes its vertical correction witness. |
| `Column.firstPageIso` | The genuine first quotient page is isomorphic to actual column cohomology, without a d′d″ hypothesis. |
| `Column.all_differentials_zero` | The actual induced differential vanishes for **every integer r ≥ 1**, at every bidegree. |
| `Column.associatedSequence` | A mathlib `CohomologicalSpectralSequence (ModuleCat k) 1` with those quotient pages and induced differentials. |
| `Column.associatedSequence_transition` | Its recurrence agrees with quotient classes on common cycle representatives; `zeroPageHomologyIso_π` identifies the actual homology projection. |
| `Column.eventually_stable` | Under finite horizontal support, actual numerator and denominator submodules eventually equal their stable counterparts. |
| `Filtered.infinityGradedIso` | The stable quotient is canonically the associated graded of actual total cohomology, with its induced filtration. |
| `Column.bounded_e1_degeneration` | Under rectangular boundedness and the explicit identities, all higher differentials vanish and the actual quotients eventually stabilize. |
| `Column.boundedStableGradedIso` | The stabilized pages identify with the associated graded of actual total cohomology. |

`Filtered.Filtration` stores only decreasing submodules and differential
preservation. The standard page formula, in total degree n, is

```
Zr(p,n) = Fp Tot^n ∩ D⁻¹(F(p+r) Tot^(n+1))
Br(p,n) = Fp Tot^n ∩ D(F(p-r) Tot^(n-1))
Er(p,n) = Zr(p,n) / (Z(r-1)(p+1,n) + B(r-1)(p,n)).
```

The denominator is restricted to `Zr` by a proved inclusion. The column
filtration is the span of genuine total summands with column at least p.
The conventional bidegree is `(p,q)` with `n=p+q`, and the descended total
differential has degree `(r,1-r)`. The first-page computation justifies E1
indexing directly; no E2 object is renamed E1. `Indexing.lean` retains a
separate spectral-object indexing blueprint, but the present construction
uses the concrete quotient route. Comparison with mathlib's abstract
mapping-cone `SpectralObject.spectralSequence` constructor is not claimed.

`SignBridge.lean` proves the operator bridge `v ↦ (-1)^p v`: anticommutation,
square-zero, unchanged kernels/ranges, and involution. The formal theorem is
stated for mathlib's commuting bicomplexes with signed totalization.
Reconstruction from an independently specified anticommuting double-complex
category and a full categorical totalization comparison remain future work.
The compact-Kähler analytic theorem, DGMS's converse/opposite-filtration
statement, noncommutative Kaledin theorem, and computational paths are outside
this pilot. ComputationalPathsLean is not imported.

Build with Lean `leanprover/lean4:v4.35.0-rc2` and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`:

```sh
lake build
lake env lean -DwarningAsError=true AxiomAudit.lean
python3 scripts/verify.py
```

The cloud uses an ignored link to an existing dependency checkout with exactly
these pins. No topology or paper sources are changed. The verifier checks
source stability, pins, retained upstream excerpts, all local modules, and
transitive axiom dependencies of the declarations listed in `AxiomAudit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; no proof holes,
new axioms, `unsafe`, `implemented_by`, or `native_decide` are used. The final
receipt identifies the tested source commit and digests. A later evidence-only
commit is distinguished from that source, rather than represented as a fresh
whole-commit verification. Protected Comparator, external kernels, Challenge
rendering, and Palomar intake have not run for this project.

See [PLAN.md](PLAN.md) and [REVIEW.md](REVIEW.md) for source fidelity, review
scope, and remaining release gates. This is AI-assisted work; internal review
is by another AI agent using the same Lean kernel, with the primary agent
reviewing that agent's contributions. No human proof contribution or human
mathematical review is asserted. Final author/maintainer metadata has not been
assigned. The repository's Apache-2.0 license applies; upstream attribution is
retained in the source inventories.

Sources: [DGMS §§5.15–5.17](https://www.math.stonybrook.edu/~dennis/publications/PDF/DS-pub-0024.pdf),
[Chen–Ho–Teh, v2](https://arxiv.org/abs/1506.06451v2), and
[Stelzig, v3](https://arxiv.org/abs/1812.00865v3). This formalizes a classical
implication; mathematical novelty and Palomar editorial acceptance are not
claimed. Draft PR40 is the sole campaign for this work.
