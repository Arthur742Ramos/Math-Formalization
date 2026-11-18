# A Lean lower bound for Erdős' minimum-overlap problem

This Lean 4 development formalizes a lower bound for
[Erdős problem 36](https://www.erdosproblems.com/36). For every positive
integer `N` and every partition of `{1, …, 2N}` into equal-sized sets
`A` and `B`, the selected finite theorem states that there is an integer
`k` with more than `0.3806279907 N` representations as `a - b = k`.
The normalized discrete liminf is at least `0.380627990701`, and hence
strictly greater than `0.3806279907`.

The project also proves the auxiliary lower bound for continuous relaxed and
binary models with Borel measurable representatives. The discrete result
uses a proved binary step-function embedding and does not assume equality
between the discrete and continuous optimization problems. The exact
constant and existence of a discrete limit are not claimed.

The proof uses Fourier, periodic, phase Gram, and integral certificates whose
arithmetic and source identities are checked by Lean during compilation.
The large generated Lean modules are
part of the proof; external reports are not used as numerical oracles.
`Challenge.lean` independently states the definitions and nine numerical results,
using only Mathlib imports. Its intentional `sorry`s are statement
placeholders. `Solution.lean` imports the completed proof without importing
the Challenge. Two proved field contracts specify the admissibility and balanced
partition structures. The Comparator configuration selects these contracts and
the nine numerical results. Fifteen fixed model definitions are reached from
their statement types and compared as full dependencies, including their values.
`definition_names` is empty: that field declares definition holes. The retained
[fixed-definition inventory](verification/fixed-definitions.json) and
`AuditFixedDefinitions.lean` check this dependency coverage. Structures are
covered by the field contracts.

## Verification status

Use the immutable verification reports distributed with the release packet;
each report identifies its exact source commit, configuration, toolchain and
metadata hashes. Native compilation, protected comparison, independent kernels,
negative controls and Challenge rendering have distinct recorded outcomes.
The standard axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
Local verification is distinct from editorial review or public registration.

The retained [earlier ordinary Lean receipt](reviews/full_verification/kernel_verification.json)
concerns the predecessor result at `0.380627948`. It authenticates its own
listed source hashes. The stronger proof and selected statement surface differ;
that receipt is historical evidence for its original source. See
[VALIDATION.md](VALIDATION.md) for source-bound checks and packaging.

## Certificate and replay

The frozen `fully_joint32` inputs in `certificates/frontier` specify the net
kernel and ten additional rational witnesses. The physical kernel uses 6,805
nonzero periodic rows, 641 cosine terms, and the original 23 positive
semidefinite Gram matrices with changed nonnegative multipliers. The separate
32-frequency correction and original cosine approximation have a combined
uniform error bound of `2e-12`.

The integral proof uses 11,293 shared polynomial caches and 50,430 accepted
geometries. Every geometry checks its source patch, reflected patch, normalized
coordinates and fixed-point arithmetic. Every leaf checks its witness slope
and integral budget. Ordered blocks and balanced joins assemble the full
interval, including the uniform approximation errors. The active profiles are
4–19; profiles 0–3 are not needed. The outer argument retains sixty checked
denominators and excludes thirty further intervals by the proved cap-to-mean
bound. These data implement the stronger candidate, independently of the
separate, weaker development checkpoint from the research handoff.

Shared caches and smaller kernel decisions control checking cost. The generated
leaf data use explicit `noncomputable def` declarations,
retaining their values and proofs without generating unused runtime code. Geometry
checks are proved condition by condition; leaf checks cover fixed prefixes and
the complete remaining tail. Profile slope equalities use proved integer cross
multiplication, with shared kernel-checked facts for the physical tau values.
Geometry proofs use sign-aware interval multiplication with a proved equality
to the four-corner formula.
Every original arithmetic and source-binding condition is retained. Generators
are untrusted: Lean proof terms check their outputs, and analytic
theorems connect the checked data to the actual overlap functions. The affine
and correction-coefficient JSON tables are derived intermediates, regenerated
by `generate_frontier_affine.py` and `generate_frontier_grid.py`; all literal
proof data remain in Lean source. Run those generators before generating a new
integral proposal. Development caches are separate from fresh verification.

## Provenance and scope

The development adapts the Fourier, periodic, and phase Gram framework in
[Justin Wetch's minimum-overlap work](https://github.com/justinwetch/erdos-36-minimum-overlap/tree/27b1cba5f929da7182e97d2e8c42c78c5ee5d4a8)
and uses the problem formulation discussed by
[Ethan Patrick White](https://arxiv.org/abs/2201.05704). An unpublished
research note preceded the formalization and is not included in this
repository. Provenance, authorship, AI assistance, and the Borel-measurability
limitation are recorded in `formalization.yaml`.

[Linmiao Xu's earlier minimum-overlap source](https://github.com/linrock/math-proofs/blob/22db103d7b6109baca46f2623a7287b965a56936/erdos-36/Solution.lean)
includes classical weaker lower bounds and limit statements. That separate
formalization is recorded as related work in the metadata.

This package is released under its [BSD 3-Clause license](LICENSE). The
included adapted LeanCert components retain their own license and provenance
under `vendor/leancert`. The monorepo root is Apache-2.0; Palomar currently
requires the repository-root license to match the package metadata. A
BSD-licensed standalone source snapshot puts this exact package tree at the
repository root for Palomar. The standalone branch is a submission artifact
and must not replace the monorepo tree. The release packet records both trees
and their equality explicitly.
