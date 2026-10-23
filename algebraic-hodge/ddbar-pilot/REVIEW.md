# Internal mathematical and semantic review

This account concerns the continuation from representative lemmas to the
actual column spectral sequence and bounded convergence. The six-module
checkpoint account is preserved unchanged in
[verification/checkpoint-review.md](verification/checkpoint-review.md).
Its old hashes, twenty-declaration audit and unproved milestones are historical,
not the current status. The exact-source continuation receipt and source
binding are retained separately under `verification/continuation/`.

Review is internal AI review using the same Lean kernel and dependency cache.
It is not human mathematical review, external peer review, an independent
kernel check, or Palomar editorial review. The primary contributor authored
the column-filtration, quotient-page, representative, differential,
spectral-sequence, infinity and bounded-stabilization proofs. A separate
reviewer checked their statements, hypotheses, actual operators and source
meaning. That reviewer authored `CohomologyClass` and `GradedCohomology`; the
primary contributor independently read and freshly compiled both, checking
that their canonical class map targets actual `C.homology n` and that its
kernel is exactly the incoming differential's range. The reviewer authored
the older indexing blueprint, which the primary contributor independently
checked. Authorship is not counted as independent review.

## Statement and semantic findings

- `ImageKernel` is an explicit equality of submodules of actual bicomplex
  components. The local proof constructs an actual preimage of h(x), corrects
  by v(b), and proves both closure equations and actual homology-class equality.
  The identity used is one direction of the classical d′d″ condition, sufficient
  for degeneration of the column filtration. No symmetric/converse theorem is
  inferred.
- The filtration is the span of real total summand inclusions. Its leading
  projections come from totalDesc and its differential formulas use the actual
  signed total differential. The filtration record contains only submodules,
  monotonicity, and preservation by the differential.
- Page numerators retain the condition D(x)∈F(p+r), page boundaries retain
  filtered primitives, and the denominator inclusion is proved. The differential
  is D descended by liftQ, defined without the d′d″ hypothesis. The generic
  square-zero proof uses the actual D²=0 law.
- E1 identifies with actual vertical homology without d′d″. For r≥1, zero
  leading class implies membership in the genuine page denominator. The
  incoming identity makes leading components of total boundaries vertically
  exact, and the outgoing identity supplies biclosed representatives. These
  establish all-page comparisons and every higher differential's vanishing.
- The packaged mathlib spectral sequence retains those actual quotient objects
  and induced operators in conventional degree (r,1−r). Its page homology
  isomorphisms are tied to the homology projection by `zeroPageHomologyIso_π`
  and to standard quotient classes by `associatedSequence_transition`.
  Degeneration does not enter the page or differential definitions; proved
  zero-differential theorems discharge the complex laws and recurrence.
- The infinity numerator is Fp∩kerD and its denominator is
  (Fp+1∩kerD)+(Fp∩rangeD). The generic graded comparison uses the range of
  filtered cocycles' actual cohomology classes, not a supplied quotient standing
  in for cohomology. Its representative rule is canonical.
- `HorizontalSupport` and `RectangularSupport` express actual component
  vanishing via carrier subsingletons. The finite-filtration proof uses genuine
  total summand maps. For U<p+r and p−r+1≤L the actual page numerator and
  denominator become the infinity submodules. The eventual bound is
  max(1,U−p+1,p−L+1). Thus bounded convergence is established by submodule
  stabilization, not merely by finding abstractly isomorphic pages.

## Source fidelity and scope

DGMS §§5.15–5.17 supplies the classical source. Its §5.17 equivalence also
contains both filtrations and their n-oppositeness, which are not claimed.
Chen–Ho–Teh's non-E0 hypothesis is not silently removed: this project gives
its own direct proof for every r≥1, including earlier degeneration. Stelzig's
square/zigzag decomposition is context, not an imported theorem here.
The initial scoped overlap search is documented in PLAN; no universal
prior-art audit or mathematical novelty claim follows.

The sign bridge is an actual operator sign involution. Reconstruction of an
independently specified anticommuting complex and categorical totalization
comparison are outside its proved contract. The concrete quotient construction
has conventional E1 indexing justified by its first-page computation; it does
not claim a `HasSpectralSequence` instance or an abstract mapping-cone spectral
object comparison.

The release inventories remain preliminary. The original literal-source
inventory is retained, with continuation excerpts for quotient descent,
submodule images/inverse images, actual zero-map homology data, total summand
maps and conventional spectral-sequence indexing. Exact-pin source and excerpt
checks are mechanical evidence, not a completeness or semantic-fidelity proof.
A complete selected-declaration dependency expansion and separate
Challenge/Solution bridges remain release gates.

## Verification and remaining limits

`AxiomAudit.lean` enumerates the local public definitions and theorems,
including the generic cohomology and graded comparisons, actual sequence,
bounded stabilization and final theorem. The verifier compares every returned
name with that list and permits only `propext`, `Classical.choice`, and
`Quot.sound`. It rejects proof holes, custom axiom declarations and unsafe or
native shortcuts. The continuation receipt, rather than the old checkpoint
report, identifies the exact tested commit, all source digests, audit count,
logs, Lean version and dependency pin. Reviewed-source hashes are recorded in
the separate continuation review receipt; later evidence-only additions do
not assert a fresh post-merge or whole-commit run.

No protected Comparator, external kernel, Challenge rendering, metadata
intake, Palomar registration or editorial acceptance has run for this project.
Final authorship and responsible-maintainer metadata require explicit role
assignment. A serious-research-interest assessment and exact release packet
review are still necessary before a Palomar-ready handoff. Draft PR40 remains
the only campaign and no submission is authorized by these notes.
