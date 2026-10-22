# Brouwer characterization of Cantor space

A topological space `X` is homeomorphic to `ℕ → Bool`, with the product of
discrete two-point topologies, if and only if it is nonempty, compact,
metrizable, has a basis of clopen sets, and has no isolated points.

The full theorem `CantorCharacterization.nonempty_homeomorph_iff` quantifies
over an arbitrary supplied `TopologicalSpace X`. All five conditions appear
on its right-hand side. `HasClopenBasis X` means
`IsTopologicalBasis {U : Set X | IsClopen U}`. The exact pinned meaning of
`PerfectSpace X` is equivalent to every punctured neighborhood filter being
nontrivial. Perfectness alone permits the empty space, so nonemptiness is a
separate condition. `MetrizableSpace`, rather than pseudometrizability,
provides the separation required here.

This is a formalization of a classical theorem of Brouwer, following the
statement of Anush Tserunyan's *Introduction to descriptive set theory*,
Theorem 5.3. It is not a new mathematical theorem or priority claim.

## Proof and selected contracts

The sufficient core uses compactness, Hausdorffness and second countability,
a clopen basis, perfectness and nonemptiness. It first enumerates a countable
clopen basis as `B n`. Each nonempty clopen cell has a genuine disjoint
two-piece nonempty clopen partition. At depth `n`, that partition also decides
membership in `B n`: use its intersections with the set and its complement
when both are nonempty; otherwise split the cell using perfectness.

The resulting full binary tree has covering children, not just disjoint
subsets. Every point has a binary address. The address map is continuous
because each coordinate is constant on a suitable open cell. Every binary
branch is realized by the compact intersection of nested nonempty closed
cells. Decisions of all basis elements separate points. Thus the address map
is bijective; the compact-to-Hausdorff theorem supplies inverse continuity.

The eleven Comparator targets are:

- `exists_clopen_split`, `exists_deciding_split`, `exists_binary_scheme`;
- `BinaryScheme.continuous_code`, `BinaryScheme.surjective_code`,
  `BinaryScheme.injective_code`;
- `nonempty_homeomorph_of_secondCountable`, `nonempty_homeomorph`;
- `cantor_hasClopenBasis`, `cantor_perfectSpace`, `nonempty_homeomorph_iff`.

All names are in `CantorCharacterization`. `definition_names` is empty:
`HasClopenBasis`, the binary scheme and address functions remain fixed
compared declarations, not definition holes. This package does not prove the
equivalent total-disconnectedness formulation or a real middle-thirds-set
corollary. It does not prescribe a diameter reduction at each binary split.

## Sources, overlap and audience

[SOURCE-MAPPING.md](SOURCE-MAPPING.md) relates the source statement to the
formal contracts and discloses the different proof route. Mathlib's existing
specific Cantor-set homeomorphism, general Cantor embeddings and continuous
surjections onto compact metric spaces do not identify an arbitrary target
space homeomorphically. Bounded overlap checks found no equivalent intrinsic
characterization at the pinned revision or in the 28 prior campaign packages.
Global and private overlap checks are not exhaustive.

Intrinsic recognition of Cantor spaces and compact zero-dimensional coding
are useful in general topology and descriptive set theory. The theorem
complements the campaign's Baire-space characterization; the fully covering
binary construction is the substantive formalization here. Research scope
and mathematical fidelity require review independent of machine compilation.

## Authorship and verification

Project authors: Arthur Freitas Ramos, David Barros Hulak, and
Ruy Jose Guerra Barretto de Queiroz. The separately recorded responsible
maintainers are the same three people under the campaign's authorization.
OpenAI Codex contributed substantive proof, source-audit and packaging work;
internal reviews are AI reviews. No human proof contribution, human review,
external peer review or registry endorsement is inferred from these names.

Lean is pinned to `leanprover/lean4:v4.35.0-rc2`; Mathlib and all nine Git
dependencies are fixed in `lake-manifest.json`. Challenge and proof have equal
bytes and import pinned Mathlib; Solution imports the proof. Only `propext`,
`Quot.sound`, and `Classical.choice` are allowed.

[VERIFICATION.md](VERIFICATION.md) specifies the checks. Exact-source run
outcomes, source commits and release readiness belong to external immutable
receipts, not to an inference from this README. Source-only inventory checks
do not establish successful semantic compilation, protected comparison,
independent kernels, rendering, editorial review or registration. The final
release-packet guard must bind the exact source, metadata and original reports
before verified submission fields are delivered. This source grants no
registry, credential, merge, payment or security-setting authority.
