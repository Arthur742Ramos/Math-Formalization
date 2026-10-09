# Verification

Run from `topology/sorgenfrey-covering`:

```sh
python3 scripts/verify.py --check-package-only
lake exe cache get Counterexamples.SorgenfreyLine Mathlib.Topology.Compactness.Lindelof
python3 scripts/verify.py --lake-build --output .lake/verification.json
```

The verifier checks pins, ported proof hashes, canonical Challenge imports,
unfinished source and complete definition evidence. It runs a Lake build, twelve
transitive axiom audits, seven independent statement assignments, direct pinned
source comparisons, rejection controls and the bundled `leanchecker`.

The original source passed a
[hosted Linux run](https://github.com/Arthur742Ramos/sorgenfrey-covering-lean/actions/runs/37987933137)
at `b60f28592f22a142949e48e50597bcacb05aebfe`; local logs are retained in
`verification/`. That evidence alone does not verify the new wrapper or
workflow. The monorepo's **Sorgenfrey covering** PR check verifies the nested
package at its recorded checkout SHA and uploads its build, axiom, statement and
kernel-check logs.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted. There are no
theorem holes or new axioms, including in the independent Challenge. No registry
submission or acceptance is asserted.

The port's Palomar workflow calls `PalomarRegistry/PalomarSubmission` at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, mode `full`, execution profile
`palomar-standard-v1`. It checks the exact PR head SHA. It runs the canonical
Challenge provenance audit and real Comparator with bundled NanoDa and con-ron,
as well as Lean's kernel. Ordinary leanchecker evidence is not a substitute for
that report. A preflight does not create a Palomar registry submission.
