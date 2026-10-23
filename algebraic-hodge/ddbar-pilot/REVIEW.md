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

The original pilot inventories and continuation receipts remain historical.
The package now has a schema-2 material inventory: 47 definitions, structures
and classes, 30 exact-pin source files and 63 excerpts. The primary contributor
independently reviewed the reviewer's inventory and separately compiled
bridges, checking literal/proved distinctions, quotient and homology meaning,
sign conventions, coproduct existence and LinearEquiv inverse construction.
Core/order/algebra/category expansion boundaries are explicit rather than
claimed as exhaustive transitive theorem/tactic inventory. The validator's
apostrophe-final name bug was fixed with positive/negative regressions; all67
existing inventory tests passed. No other project's mathematics or pins changed.

## Package and abutment review

ReleaseFidelity was authored by the separate reviewer and independently read
and freshly compiled by the primary contributor. It proves next-page cycle
inclusion, recurrence coverage of arbitrary next-page classes, finite bounds
on actual induced cohomology filtration, exhaustion/separation, representative
compatibility of the actual stabilized quotient, and equality of the bounded
stabilization and degeneration maps as actual morphisms to graded cohomology.
The generic quotient transport lemma only transports along proved numerator
and denominator equalities; no convergence conclusion is assumed.

The reviewer independently compared all135 retained Challenge declarations
with modular sources modulo comments/whitespace, using a separate comparison
rather than trusting the generator's own hashes. Contracts and proof commands
match. Only three Mathlib imports occur, and complete proofs are supplied.
The current995-line statement surface fits the hard cap but triggers the
readability warning. Human/editorial evaluation of this large proof-complete
surface remains separate from compilation and internal review.

Eight theorem names and seventeen concrete definition/construction names are
selected. All must be checked through both entrypoints; the local interface
checker originally recorded declaration kinds and local kernel type-definitional equality
in a Solution environment. The approved source-c3107f8 run subsequently failed exact
Comparator equality because auxiliary-proof cache names differed. The corrected
checker calls the actual pinned `Lake.Check.compareAt` and additionally requires
selected literal definition values; separately compiled identical standalone
proof bodies remove that elaboration-history difference. A random Challenge alias
and in-memory declaration-mutation rejection controls test local comparison.
These shared proofs are not independent implementations. The modular change is
limited to 73 uses of `lia -abstractProof`, retaining generated arithmetic proofs
inline. The pinned Grind implementation changes proof storage, not the goal,
hypotheses or kernel checking. No supporting theorem holes are added. This does not protect the canonical statement
surface or validate exported proofs/definition values, so it is explicitly not
Comparator acceptance. Actual protected results require their own source-bound receipts.

## Verification and remaining limits

AxiomAudit enumerates 180 modular declarations. HodgeChallengeAudit separately
audits the 25 selected declarations through the standalone entrypoint. Only
propext, Classical.choice and Quot.sound are allowed; proof holes, custom
mathematical axioms and unsafe/native shortcuts are prohibited. Each exact-source
receipt records the actual results and source hashes. Package receipts are
separate from immutable checkpoint/continuation evidence, and evidence-only
commits are not represented as fresh whole-commit runs.

Local compiled module-closure evidence hashes actual source files and checks
Git-package bytes at exact manifest pins. Bundled Lean source bytes are
identified separately; neither this writable-cache inspection nor ordinary
Lean builds replace a protected canonical dependency audit or independent
kernel replay.

The user explicitly assigned Arthur Freitas Ramos, Ruy Jose Guerra Barretto de
Queiroz and David Barros Hulak to both human author and responsible-maintainer
roles. Metadata and README preserve that assignment and the separate substantive
AI contribution disclosure. No human proof contribution or human/external
review is invented from those roles.

The pinned metadata/config validators are read-only local checks. Protected
comparison, actual kernel outcomes, rendering, visual inspection and the full
release-packet guard are recorded separately for each exact tested source.
Local compilation and AI review do not imply those other results. RUN-PLAN
specifies the execution protocol; applicable action-time authorization and
budget facts are retained with each reviewed plan and run receipt. Source
snapshots and later evidence-only or status-only commits remain distinct.
Serious-research-interest/editorial qualification and exact-packet review are
separate from mechanical verification. No human review or registry acceptance
is inferred from an execution report.
