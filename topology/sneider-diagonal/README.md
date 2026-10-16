# Sneider's Gδ-diagonal metrization theorem

For every compact Hausdorff space `X`, including the empty space,

```lean
MetrizableSpace X ↔ IsGδ (Set.diagonal X)
```

The diagonal is taken in `X × X` with its ordinary product topology. No
first-countability, second-countability, separability or countability of `X`
is assumed. The package also supplies an actual metric whose induced topology
equals the given topology.

The substantive proof establishes a general compact-normal lemma: if `K` is
closed and Gδ, shrink countably many open witnesses to closed neighborhoods of
`K`. Their finite intersections form a cofinal neighborhood basis. Compactness
of the complement of an arbitrary open neighborhood supplies the finite
subintersection; merely having the correct infinite intersection would not
suffice. Applied to the diagonal, this makes the compact uniformity countably
generated. Canonical Mathlib uniform metrization finishes the argument.

## Scope and sources

[Gary Gruenhage, *Spaces having a small diagonal*, arXiv:math/9910153v1](https://arxiv.org/pdf/math/9910153v1),
printed p.1, recalls the compact Gδ-diagonal equivalence. Its introduction and
Section 2 place the criterion in research on compact spaces, diagonal properties
and countable networks. See [SOURCES.md](SOURCES.md) for the consulted source,
source fidelity and overlap audit. This package proves the classical criterion;
no novelty, priority or Palomar acceptance is claimed. The countably compact
extension and the paper's small-diagonal research results are outside scope.
The original 1945 Sneider paper was not consulted.

## Formal interface

The seven Comparator-selected declarations, all in namespace `Sneider`, are:

- `exists_closed_countable_nhds_basis_of_isGδ`
- `nhdsSet_isCountablyGenerated_of_isGδ`
- `isGdelta_diagonal`
- `exists_closed_diagonal_basis`
- `metrizableSpace_of_isGdelta_diagonal`
- `metrizable_iff_isGdelta_diagonal`
- `exists_compatibleMetric`

`SDChallenge.lean` contains the complete statements and proofs and imports only
canonical Mathlib modules. It is byte-identical to `SneiderDiagonal.lean`.
`SDSolution.lean` publicly imports the latter. They are checked as separate
module contracts; no file imports both duplicate declaration sets. There are
no new selected definitions. [DEFINITIONS.md](DEFINITIONS.md) records the standard
upstream notions at the exact Mathlib pin.

## Verification and limits

Lean `v4.35.0-rc2` and the committed lockfile pin Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Run commands from this directory:

```sh
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

The campaign cloud uses `/workspace/palomar-tools/run` before these Lean/Lake
commands. [AUDIT.md](AUDIT.md) explains the checks, and [REVIEW.md](REVIEW.md)
records independent internal AI review. Transitive axiom dependencies are
restricted to `propext`, `Classical.choice` and `Quot.sound`; no human review is
claimed. Semantic tests cover exact binders and topology equality, empty spaces,
empty/full closed sets, and an indiscrete compact space.

Full canonical Comparator/multi-kernel preflight and Challenge rendering are
outstanding gates. Local Lean verification and ordinary Lean CI do not replace
them. This cloud's user-namespace restriction is preserved. The user approved the pinned installer’s disclosed path-specific AppArmor
user-namespace operation only on the disposable verification runner. The cloud
host restriction remains unchanged. Exact-source canonical results are recorded
separately after those jobs complete. No registry operation is authorized here.

## Authorship and responsible maintenance

The user explicitly approved Arthur Freitas Ramos, David Barros Hulak and
Ruy Jose Guerra Barretto de Queiroz as both the authors and the responsible
maintainers of this project. These are separately confirmed roles; they do not
assert that the named humans wrote the Lean proofs. Existing projects’
attribution is preserved.

OpenAI Codex authored the substantive proofs and packaging under Arthur's
campaign authorization. Independent internal AI mathematical/source and
implementation reviews are distinguished from human review. Apache-2.0 applies;
upstream Lean/Mathlib and classical mathematics retain their attribution.
