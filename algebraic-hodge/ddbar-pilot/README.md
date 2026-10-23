# Algebraic Hodge pilot: closed representatives

**Compiled pilot; full E1 degeneration remains unproved.** This independent
project formalizes the representative step of the classical algebraic
`d′d″` argument in genuine mathlib bicomplexes over a field. It is not a
compact-Kähler analytic theorem, a new mathematical result, or a Palomar
submission packet.

For a commuting bicomplex `K`, write `h` and `v` for its actual horizontal
and vertical linear maps. The explicit hypothesis at `(p+1,q)` is

```
range(h : K[p,q] → K[p+1,q]) ∩ ker(v : K[p+1,q] → K[p+1,q+1])
  = range(h ∘ v : K[p,q-1] → K[p+1,q]).
```

`exists_closed_correction` proves that a vertical cocycle `x` has a correction
`b` with `y = x - v b` killed by both operators.
`exists_closed_representative` quantifies over the column's actual
`HomologicalComplex.homology` object, using mathlib's canonical
kernel/quotient comparison to prove that `y` represents the given class.
`exists_total_closed_representative` also proves that its summand inclusion
is a cocycle in mathlib's actual total complex. These local statements need
neither boundedness nor finite dimensionality. The future global target is
bounded double complexes satisfying the explicit identities in every degree.

`SignBridge.lean` proves that replacing `v` by `(-1)^p v` anticommutes with
`h`, squares to zero, preserves kernels and ranges, and is involutive. These
are operator lemmas on genuine complexes; reconstruction of a commuting
bicomplex from independently specified anticommuting data and the full
totalization comparison remain future work.

`Indexing.lean` supplies genuine `SpectralSequenceDataCore` starting at page 1
with differential degree `(r,1-r)`. Its interval formulas and coordinate
shear are proved. No associated filtered total complex, `HasSpectralSequence`
instance, page comparison, higher differential vanishing, or E-infinity
comparison is claimed. Coordinate arithmetic is only indexing infrastructure.

Build with Lean `leanprover/lean4:v4.35.0-rc2` and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`:

```sh
lake exe cache get Mathlib.Algebra.Homology.TotalComplex Mathlib.Algebra.Homology.ShortComplex.ModuleCat Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
lake build
lake env lean AxiomAudit.lean
```

The cloud check used the existing matching dependency checkout through an
ignored `.lake/packages` link; no existing topology or paper source was
changed. A fresh checkout can let Lake obtain the pinned dependencies normally.
Verification records identify source digests and distinguish source commits
from later evidence-only commits. The audited transitive axioms are restricted
to `propext`, `Classical.choice`, and `Quot.sound`. No proof holes, new axioms,
or `native_decide` are used. Protected Comparator, external-kernel validation,
and Challenge rendering have not been run for this pilot.

See [PLAN.md](PLAN.md) for the remaining dependency graph and
[REVIEW.md](REVIEW.md) for independent AI review and its limits. Code and
documentation were produced with OpenAI Codex assistance; no human proof
contribution or human mathematical review is asserted. The repository owner
is not automatically credited as the author of these proofs. No final
authorship or maintainer metadata is assigned to this pilot. The repository's
Apache-2.0 license applies; mathlib authorship remains with its cited sources.

Sources: [DGMS §§5.15–5.17](https://www.math.stonybrook.edu/~dennis/publications/PDF/DS-pub-0024.pdf),
[Chen–Ho–Teh, v2](https://arxiv.org/abs/1506.06451v2), and
[Stelzig, v3](https://arxiv.org/abs/1812.00865v3). DGMS is the source being
adapted; the other papers supply context and alternative proof architecture.
The scalar correction is classical. Neither novelty nor registry acceptance
has been established.
