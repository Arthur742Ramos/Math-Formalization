# Sorgenfrey covering theorems in Lean

This project proves that every subspace of the Sorgenfrey (lower-limit real) line
is Lindelöf and that every open cover of every subspace has a countable,
pairwise disjoint clopen refinement. The refinement is locally finite, so every
subspace is paracompact. It also proves that the Sorgenfrey plane is neither
Lindelöf nor paracompact.

These are classical theorems. This project makes no claim to a first-ever
formalization. Mizar's [TOPGEN_6 article, *Some Properties of the Sorgenfrey Line
and the Sorgenfrey Plane* (2013)](https://mizar.uwb.edu.pl/fm/2013-21/pdf21-2/topgen_6.pdf)
already formalizes line Lindelöfness and plane non-Lindelöfness and non-normality.

## Reproduce

- Lean: `leanprover/lean4:v4.28.0`.
- Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (the v4.28.0 release).
- Dependency revisions are fixed in `lake-manifest.json`.

Run from `topology/sorgenfrey-covering` with
[elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get Counterexamples.SorgenfreyLine Mathlib.Topology.Compactness.Lindelof
lake build
lake env lean AxiomAudit.lean | tee axiom-audit.log
python scripts/check_axioms.py axiom-audit.log
LEAN_NUM_THREADS=2 lake env leanchecker SorgenfreyCovering AxiomAudit
lake env lean scripts/CompareTypes.lean
python scripts/check_definitions.py --compare-mathlib --self-test
```

The CI workflow builds the package modules, runs the axiom audit, checks its output,
rechecks the compiled proof terms with Lean's bundled `leanchecker`,
and uploads the verification logs. Its checkout and Lean setup actions are
pinned to commits. The logs identify the exact repository commit being checked.
The path-specific workflow is `.github/workflows/sorgenfrey-covering.yml`. See
[VERIFICATION.md](VERIFICATION.md) for the single-command driver,
[PROVENANCE.md](PROVENANCE.md) for source lineage, and
[DEFINITIONS.md](DEFINITIONS.md) for definition evidence. The independent
Challenge has no theorem holes; its local checks make no external registry
comparator claim.

## Statements and proof

All declarations below are in `Counterexample.SorgenfreyLine`.

| Declaration | Meaning |
| --- | --- |
| `countable_Ico_cover` | Right half-open intervals based at every point of any subset have a countable subfamily covering that subset. |
| `isLindelof_set` | Every subset of the actual Mathlib Sorgenfrey line is Lindelöf in its induced topology. |
| `instHereditarilyLindelofSpace` | Hereditary Lindelöfness as a Mathlib instance. |
| `disjointify_clopen_cover` | A countable clopen cover of any topological space admits a subordinate clopen partition that is locally finite. |
| `clopen_refinement` | Every open cover of any Sorgenfrey subspace has a countable, pairwise disjoint clopen, locally finite refinement. |
| `instParacompactSpace_subspace` | Paracompactness of every Sorgenfrey subspace. |
| `instParacompactSpace` | Paracompactness of the whole Sorgenfrey line. |
| `not_lindelofSpace_prod` | The Sorgenfrey plane is not Lindelöf. |
| `not_paracompactSpace_prod` | The Sorgenfrey plane is not paracompact. |

For a subset A, choose a subordinate basic interval [x,b(x)) at each point x.
The ordinary real open intervals (x,b(x)) have a countable subfamily with the
same union, by second countability of the usual reals. The exceptional points
of A outside this union are countable: choose a rational strictly between each
exceptional x and b(x). Two exceptional points cannot have the same chosen
rational, since the larger endpoint would belong to the smaller point's
ordinary open interval. Adding the exceptional points yields a countable
half-open interval cover of A.

Restrict the clopen basic intervals to the subspace and use Lindelöfness to
select a countable clopen cover C(n). Replace C(n) by its difference from the
finite union of earlier C(k). The resulting sets are clopen, pairwise disjoint,
and still cover. Each point has its partition member as an open neighborhood,
meeting at most one partition member, which proves local finiteness. Empty
subspaces and empty cover index types are handled explicitly. Empty members of
a refinement are allowed, as in Mathlib's definition of paracompactness.

For the plane, Mathlib already proves that the antidiagonal is closed and
discrete and has cardinality continuum. Lindelöfness would force it to be
countable, a contradiction. Paracompactness of this Hausdorff plane would imply
normality, contradicting Mathlib's existing non-normality theorem.

## Provenance and scope

The definition of the Sorgenfrey line, its neighborhood basis, the clopen basic
intervals, separation properties, and the antidiagonal facts come from Yury
Kudryashov's Mathlib `Counterexamples/SorgenfreyLine.lean`. This project imports
that definition directly; it does not introduce a substitute topology.

The pinned Mathlib file leaves line paracompactness as a TODO and contains no
line Lindelöf theorem. The same gap was checked at upstream commit
`a37dcbd570ffe4283df24efc20b144a09cc3661e`, whose toolchain is Lean 4.35.0-rc4.
This project uses the installed stable 4.28.0 toolchain for its reproducible
build. Compatibility with other Mathlib revisions is not asserted.

Targeted GitHub code searches for `Sorgenfrey` under Arthur742Ramos and
PalomarArchive returned no results on 2026-10-09. This is a scoped overlap check,
not an exhaustive novelty claim.

The new proof uses no `sorry`, `admit`, or declared axioms. `AxiomAudit.lean`
prints the transitive axiom dependencies of all nine exported declarations.
The checker accepts only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` foundations. No registry submission is part of this project.

Licensed under Apache 2.0; upstream Mathlib retains its own attribution.
