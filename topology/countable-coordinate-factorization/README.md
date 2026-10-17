# Countable-coordinate factorization for compact products

Every continuous map from an arbitrary product of **nonempty compact Hausdorff**
spaces to a **metrizable** space factors continuously through a countable
subproduct. The source index is arbitrary; the target need not be separable or
second countable. The factor on a fixed selected subproduct is unique, because
its projection has a section obtained by refilling omitted coordinates from a
basepoint. No uniqueness, minimality or canonicity of the coordinate set is
asserted. Countably many continuous maps have one common countable coordinate
set and continuous factors.

The substantive bridge is uniform: every product entourage contains all pairs
agreeing on finitely many coordinates. Pull back a countable target-uniformity
basis, take the union of the finite coordinate sets, and apply uniform
separation. Compatible compact Hausdorff uniformities and Heine–Cantor give the
continuous result. The proof does not assume the factors metrizable.

An injective map must retain every nontrivial coordinate. Thus a nonempty compact
Hausdorff product embeds continuously into a metrizable target only if at most
countably many factors are nontrivial. The product itself is metrizable iff each
factor is metrizable and only countably many are nontrivial. The reverse uses
canonical countably generated product uniformities and an explicit section;
arbitrarily many singleton factors cause no obstruction.

## Sources and research context

This is classical mathematics, with no novelty or historical priority claim.
Karlova–Mykhaylyuk, [On α-embedded subsets of products](https://arxiv.org/pdf/1411.3173v1),
printed p.5 Definition3.1 and Theorem3.1, gives a broader invariant-subspace and
pseudo-aleph1-compact factorization theorem with regular-Gδ-diagonal targets.
We prove its compact Hausdorff full-product/metric-target specialization, using
an independent uniform-space argument. We do not formalize their broader result.
Maslyuchenko–Mykhaylyuk, [Separately continuous functions…](https://arxiv.org/pdf/1512.08606v1),
printed p.1, explicitly uses compact-product countable-coordinate dependence in
research on separately continuous maps and discontinuity sets. That gives a
concrete audience in general topology and function spaces. Their new results
are outside this package. The original Noble–Ulmer1972 source was identified
but not directly consulted; no reproduction of that proof is claimed.

Mathlib at `065356127b1dc0016f66b7283ce0ce2c4055aa55` supplies the product
uniformity, filter bases, compact compatible uniformity, Heine–Cantor and
compatible target uniformity infrastructure. No equivalent arbitrary-product
countable-coordinate factorization theorem was located. All14 prior monorepo
packages are preserved. A dated independent audit of the saved596 active public
registry entries at revision329 found no equivalent target. Current public registry
and submission-protocol endpoint checks returned HTTP403, so this does not claim
current complete duplicate clearance or knowledge of private attempts.

## Scope and precise contracts

`CCChallenge.lean` is byte-identical to the substantive proof module and imports
only canonical Mathlib. `CCSolution.lean` publicly imports that module. The
Comparator selects13 proved theorems and the literal `refill` definition.
`DEFINITIONS.md` maps every selected declaration to its exact hypotheses.
Dependence alone has no nonempty-factor hypothesis. Full-subproduct continuous
factorization and the product criterion assume nonempty factors; uniform
factorization and fixed-support uniqueness carry an explicit basepoint.
Empty index and empty selected-coordinate sets are allowed. `refill` uses
classical decidability; all selected transitive dependencies use only `propext`,
`Classical.choice` and `Quot.sound`. No holes or added mathematical axioms occur.

## Reproducibility and status

Lean `leanprover/lean4:v4.35.0-rc2` and the committed lockfile fix this package's
own toolchain. From this directory in the prepared cloud environment:

```sh
/workspace/palomar-tools/run lake build
/workspace/palomar-tools/run lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

Ordinary Lean compilation, independent import contracts and semantic tests are
separate from canonical Comparator/NanoDa/con-ron verification and Challenge
rendering. Those canonical checks have not run for this project. Their pinned
installer may conditionally load an AppArmor user-namespace policy on fresh
GitHub runners, requiring new specific approval; earlier PR16 approval is not
reused. Local Comparator cannot run on this host's read-only UID map and no
restriction is bypassed. No intake, review acceptance or registration is claimed.
See `REVIEW.md` for the actual internal review scope and pending gates.

## Attribution

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.
These are separately confirmed roles carried forward by the authorized campaign.
OpenAI Codex authored substantive proofs, tests and packaging. Independent
internal AI agents reviewed the stated scope; no human review is invented, and
no human or external peer review is claimed. Canonical Mathlib and mathematical
source attribution are retained. Apache-2.0.
