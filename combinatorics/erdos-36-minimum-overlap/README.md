# A Lean lower bound for Erdős' minimum-overlap problem

This Lean 4 development formalizes a lower bound for
[Erdős problem 36](https://www.erdosproblems.com/36). For every positive
integer `N` and every partition of `{1, …, 2N}` into equal-sized sets
`A` and `B`, the selected finite theorem states that there is an integer
`k` with more than `0.380627948 N` representations as `a - b = k`.
The normalized discrete liminf is at least `0.3806279485`, and hence
strictly greater than `0.380627948`.

The project also proves the auxiliary lower bound for continuous relaxed and
binary models with Borel measurable representatives. The discrete result
uses a proved binary step-function embedding and does not assume equality
between the discrete and continuous optimization problems. The exact
constant and existence of a discrete limit are not claimed.

The complete proof is instantiated from Lean-checked Fourier, periodic,
phase Gram, and integral certificates. The large generated Lean modules are
part of the proof; external reports are not used as numerical oracles.
`Challenge.lean` independently states the definitions and nine results,
using only Mathlib imports. Its intentional `sorry`s are statement
placeholders. `Solution.lean` imports the completed proof without importing
the Challenge.

## Verification status

The included [ordinary Lean verification receipt](reviews/full_verification/kernel_verification.json)
records a successful earlier build and transitive axiom audit with Lean
4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The recorded mathematical sources and toolchain locks match this snapshot.
The selected declarations were reported to depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The protected Comparator run, independent NanoDa verification, complete
Palomar mechanical preflight, editorial review, and registration are
separate stages and are not established by that receipt. This is a
preparation, not a verified submission. Follow the repository's local
validation policy and see [VALIDATION.md](VALIDATION.md) for the remaining
checks and the licensing constraint on submitting from this monorepo.

## Provenance and scope

The development adapts the Fourier, periodic, and phase Gram framework in
[Justin Wetch's minimum-overlap work](https://github.com/justinwetch/erdos-36-minimum-overlap/tree/27b1cba5f929da7182e97d2e8c42c78c5ee5d4a8)
and uses the problem formulation discussed by
[Ethan Patrick White](https://arxiv.org/abs/2201.05704). An unpublished
research note preceded the formalization and is not included in this
repository. Provenance, authorship, AI assistance, and the Borel-measurability
limitation are recorded in `formalization.yaml`.

This package is released under its [BSD 3-Clause license](LICENSE). The
included adapted LeanCert components retain their own license and provenance
under `vendor/leancert`. The monorepo root is Apache-2.0; Palomar currently
requires the repository-root license to match the package metadata. A
BSD-licensed standalone source snapshot is therefore needed for Palomar
when submitting from this monorepo, unless the applicable licensing and
intake requirements change.
