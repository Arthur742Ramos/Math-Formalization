# Composants of continua

A composant of a point is the union of the proper subcontinua containing it.
For a nondegenerate compact Hausdorff continuum, every composant is dense and
connected. In an indecomposable continuum, these sets are equal or disjoint
and cover the space. Under second countability, each composant is a countable
union of proper subcontinua and is meagre in the indecomposable case. Baire's
theorem then gives uncountably many distinct composants.

The formalization follows Frank Sturm's 2009 thesis, Theorems 1.8, 1.10, 1.11
and 1.13. The countable-family argument uses an open basis rather than metric
balls. The literal definition gives an empty composant in a singleton, so
point membership, density, connectedness, coverage and uncountability require
`Nontrivial X`. See [definition fidelity](DEFINITIONS.md) and
[provenance](PROVENANCE.md) for the exact assumptions and reused proofs.

From this directory, with elan installed, run:

```sh
python3 scripts/verify.py --lake-build --output .lake/verification.json
python3 scripts/check_definitions.py --compare-mathlib --self-test
```

This performs the pinned ordinary Lake build, then fresh local Lean proof,
statement, literal-definition and axiom checks. Without `--lake-build`, it
uses already installed dependencies. `--check-package-only` checks the
source layout and pins without running Lean. Local checks do not establish
hosted Comparator or independent-kernel replay; see [verification](VERIFICATION.md).

Lean is pinned to `v4.35.0-rc2`, Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. `Boundary.lean` and `Interior.lean`
retain bounded, attributed source modules from earlier projects. This folder
has no imports from another monorepo target. Challenge imports only Mathlib.
