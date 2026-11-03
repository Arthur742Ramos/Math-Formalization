# Verified components of cyclic covering constructions

This is a **partial formalization** supporting the manuscript *Covering schemes
with one or two extra rows*. It ports 48 proof modules from the executed
research supplement and adds five normalization/transport modules. It pins
official Lean 4.35.0-rc2 with its bundled Std library.
No Mathlib, external solver, or native-evaluation proof oracle is used.

## Principal result and scope

`CyclicDigitTransport.no_representative_extension` proves that no sixth column
extends any of the seventeen literal order-nine representatives, using the
original modular-difference extension predicate. It derives the lower-profile
and digit-equation conditions from that predicate rather than assuming them.

The proof uses `CoveringArithmeticExclusion.no_digit_lift`: complete quota
enumeration yields 72 eligible profiles, 71 certified linear contradictions,
and one certified quadratic contradiction. New generic normalization theorems
show that subtracting every column's sum preserves arbitrary ten-row coverage
and gives every pair the exact multiset `[0,1,2,3,4,5,6,7,8,0]`.

The other modules prove explicit 10-by-5, 11-by-6 and 11-by-7 coverings of the
cyclic group of order nine, an index-two 18-by-6 seed, the published 63-by-7
index-one matrix, complete finite quota enumeration, generic left-nullspace
soundness over the three-element field, and qualified lifting and transformation
implications. Seventeen batch modules check 2,088 literal transformation records.

**This package does not prove unrestricted nonexistence of a 10-by-6 covering of
order nine, exhaustive graph/classification completeness, or the manuscript's
infinite-family theorems.** Canonical row/column normalization into the
enumerated graph, exhaustive
candidate/triangle generation, and formal integration of the batch records
with the transformation API remain separate obligations. The narrow
order-45 theorem is not unrestricted order-45 nonexistence.

See [the detailed coverage boundary](FORMAL_COVERAGE.md),
[the original source review](REVIEW.md),
[the new bridge review](NEW-BRIDGE-REVIEW.md), and [provenance](PROVENANCE.md).

## Reproduce the native checks

Install the official pinned Lean release and Python 3.10 or newer, then run:

```sh
python3 run_formal.py --lean /absolute/path/to/lean --jobs 2
```

The runner compiles all 53 modules in a fresh temporary directory, records
source hashes and per-declaration transitive axiom reports, and rejects
compilation failures, source mutation, proof placeholders, custom axioms and
`native_decide`. It retains compiler output in `logs/` and writes
`verification_report.json`; these generated outputs are ignored by Git.
Every printed declaration is checked against the standard allowlist
`propext`, `Quot.sound`, and `Classical.choice`. This is not a claim that every
proof is axiom-free, nor an independent-kernel verification.

An official Linux release in the managed execution environment can require the
included narrowly scoped executable-path compatibility shim. The runner enables
it only after observing that exact runtime incompatibility. It changes no Lean
kernel or proof declaration. Ordinary Linux and Windows installations should not
need it; Windows reproduction has not been tested.

## Publication and registry status

This is a source-publication package, **not yet a Palomar-ready submission**.
The native build does not establish protected Comparator acceptance,
independent-kernel replay, canonical rendering, editorial review, or registration.
A [draft self-contained Challenge and Comparator contract](CONTRACT.md) is
included. The supported-toolchain port still requires finalized attribution,
protected contract comparison, independent kernels, and canonical rendering/full
gates. Native compilation does not remove the canonical host-capacity minimum.
No private intake or public registration is asserted here.

## Attribution

The order-nine positive bounds, general lifting/composition methods, and the
order-63 difference matrix have prior literature and are not claimed as new.
The manuscript's priority assessment remains separate from proof verification.
The source was developed with substantial AI assistance. The accompanying
independent review is an internal AI review, not human or external peer review.
This directory is distributed under the repository's Apache 2.0 license.
