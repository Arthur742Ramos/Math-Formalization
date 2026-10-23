# Algebraic column E1 degeneration and bounded abutment

This project proves a classical conditional algebraic degeneration theorem for
actual mathlib bicomplexes over a field. It supplies a proof-complete,
Mathlib-only Challenge and a separate modular Solution. It is a draft package
for mechanical preflight, not a Palomar submission or verified intake handoff.

For commuting squares, `ImageKernel K p q` is the actual operator identity

```
range(h : K[p,q] → K[p+1,q]) ∩ ker(v : K[p+1,q] → K[p+1,q+1])
  = range(h ∘ v : K[p,q-1] → K[p+1,q]).
```

Assuming it in every integer bidegree, the proofs construct biclosed vertical
cohomology representatives and show **every actual dr vanishes for r ≥ 1**.
Rectangular boundedness is actual component vanishing via `Subsingleton`;
finite horizontal support suffices for the convergence proof. No finite
dimensionality, characteristic-zero or analytic assumption is implicit.

The filtration is the span of genuine total summands with column at least p.
For total degree n and actual signed total differential D, the pages are

```
Zr(p,n) = Fp Tot^n ∩ D⁻¹(F(p+r) Tot^(n+1))
Br(p,n) = Fp Tot^n ∩ D(F(p-r) Tot^(n-1))
Er(p,n) = Zr(p,n) / (Z(r-1)(p+1,n) + B(r-1)(p,n)).
```

The denominator's inclusion in the numerator is proved. D descends to these
quotients before the image/kernel hypothesis is used. Conventional bidegree
is `(p,q)`, n=p+q, with dr of degree `(r,1-r)`; the first-page computation
justifies E1 directly. No E2 object is renamed E1.

| Selected contract | Meaning |
| --- | --- |
| `exists_closed_representative` | Every actual vertical homology class has a biclosed representative; `exists_closed_correction` exposes the vertical correction witness. |
| `Column.firstPageIso` | Actual E1 is actual vertical cohomology, without the image/kernel hypothesis. |
| `Column.all_differentials_zero` | Every actual quotient differential dr is zero for every integer r≥1. |
| `Column.associatedSequence` | Mathlib cohomological spectral sequence of these actual quotient pages. |
| `Column.zeroPageHomologyIso_π` | Its zero-page comparison agrees with the actual homology projection. |
| `Column.associatedSequence_transition_next/covers` | Recurrence agrees with standard representatives and covers every next-page class. |
| `Column.bounded_e1_degeneration` | All higher differentials vanish; actual page numerator and denominator submodules eventually stabilize. |
| `Column.boundedStableGradedIso_closed` | Stabilization identifies a total cocycle's page class with its class in the associated graded of actual total cohomology. |
| `Column.cohomologyFiltration_exhaustive_separated` | The actual induced cohomology filtration is exhaustive and separated; stronger explicit finite bounds are also proved. |

`ReleaseFidelity.lean` additionally proves that the stabilization and
degeneration maps to graded cohomology are equal as actual morphisms. The
selected names are fixed in [comparator.json](comparator.json): eight theorems
and seventeen concrete definitions/constructions. The definitions have their
literal values in Challenge; their values are not unspecified placeholders.

[HodgeChallenge.lean](HodgeChallenge.lean) contains complete proofs and only
three Mathlib imports. Its 995 lines and roughly 61 KiB fit the hard cap but
exceed the readability-warning threshold. The modular development remains the
readable proof organization. [scripts/make_challenge.py](scripts/make_challenge.py)
selects actual transitive local declaration dependencies and reflows statement
headers; all 135 retained declarations were independently compared with modular
sources modulo comments/whitespace. No mathematical proof command or contract
is changed. [HodgeSolution.lean](HodgeSolution.lean) imports the modular proofs.
The selected configuration itself and full protected comparison still require
the canonical run described in [RUN-PLAN.md](RUN-PLAN.md).

Pins are Lean `leanprover/lean4:v4.35.0-rc2` and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Ordinary cloud commands are:

```sh
lake build
python3 scripts/make_challenge.py --check
python3 scripts/check_interfaces.py
python3 scripts/verify_package.py --pipeline-root /path/to/pinned/PalomarSubmission
```

`HodgeChallengeTests` and `HodgeSolutionTests` separately compile the semantic
bridges. [MATERIAL-DEFINITIONS.md](MATERIAL-DEFINITIONS.md) and its machine
inventory retain material definitions, pinned bytes, attribution, expansion
boundaries and canonical homology/quotient bridges. The root inventory
validator must run in both static and exact-dependency modes. Source hashes and
that validator do not establish semantic completeness; review is separate.

All local source uses complete proofs. The axiom allowlist is only `propext`,
`Classical.choice`, and `Quot.sound`. New package receipts go under
`verification/package-local/`; the earlier six-module checkpoint and full
continuation receipts remain immutable history. Each receipt identifies its
actual tested source. A later evidence-only commit is not presented as a fresh
whole-commit run. The local interface/source-closure checker is explicitly not
a protected Comparator verdict or independent-kernel replay.

Protected comparison and its negative controls, external kernels, rendering,
browser inspection and the final release-packet guard remain separate gates.
The current host's namespace probe fails; no security workaround is attempted.
[RUN-PLAN.md](RUN-PLAN.md) identifies the exact runner/setup/resource approval
needed before a canonical run. No workflow is active for this package.

The formal domain is mathlib's commuting squares and signed totalization.
`SignBridge.lean` proves an operator sign involution, anticommutation,
square-zero and kernel/range preservation. Reconstruction of independently
specified anticommuting data, abstract mapping-cone spectral-object comparison,
the second filtration and DGMS's converse/oppositeness remain extensions.
No compact-Kähler analytic theorem, Kaledin theorem or computational-path
contribution is claimed; ComputationalPathsLean is not imported.

Human authors and responsible maintainers, explicitly assigned for this package,
are Arthur Freitas Ramos, Ruy Jose Guerra Barretto de Queiroz and David Barros
Hulak. OpenAI Codex supplied substantive Lean proofs and packaging; that role
assignment does not invent human proof contributions or human mathematical
review. Review is internal AI review with the same kernel/cache, with the
primary contributor independently reviewing reviewer-authored modules.
Apache-2.0 applies; upstream attribution is retained.

Classical sources: [DGMS §§5.15–5.17](https://www.math.stonybrook.edu/~dennis/publications/PDF/DS-pub-0024.pdf),
[Chen–Ho–Teh v2](https://arxiv.org/abs/1506.06451v2), and
[Stelzig v3](https://arxiv.org/abs/1812.00865v3). Mathematical novelty and
editorial acceptance are not claimed. See [PLAN.md](PLAN.md) and
[REVIEW.md](REVIEW.md). PR40 remains the sole draft campaign; unrelated
mathematical projects and their pins are preserved.
