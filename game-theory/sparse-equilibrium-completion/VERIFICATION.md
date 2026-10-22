Historical scope statements in the checkpoint sections below describe that
checkpoint's source at the time recorded. They do not describe the latest scope.
The joint/algorithm and rational-grid sections, together with SCOPE.md, describe
the expanded development. Exact-source verification
is recorded by an external immutable receipt naming the complete commit and tree.

# Reproducible verification boundaries

Run from this package with the pinned Lean toolchain and locked dependencies:

```sh
lake build
python3 scripts/check_package.py
python3 ../../scripts/check_imported_definitions.py \
  --project-path game-theory/sparse-equilibrium-completion \
  --dependency-root .lake/packages/mathlib
```

After committing the complete source, run
`python3 scripts/verify_native.py --out /absolute/path/outside/the/package`.
The verifier refuses a dirty package, removes only package build artifacts,
retains dependency caches, and rebuilds the default targets at that commit.
Its external receipt binds the Git commit/package tree, file hashes, Comparator
config, exact native toolchain, locked Mathlib source, commands, logs and exports.

The native verification sequence builds both independent contracts, all actual
axiom reports, the definition bridges through each entrypoint, and a semantic
counterexample proving that cuts cannot replace omitted-row guards. The protected
Challenge is a deterministic assembly of the exact seventy-four local source bodies with
full proofs, zero definition holes, and exposed public declarations; it is
compiled under a different module alias
without importing the solution. The unchanged pinned `Lake.Check.compareAt` API
compares dependency identities. A modified fixed `envelope` definition must be
rejected. `Lake.Check.checkAxioms`, native module checking and independent checking
of the solution export provide separately logged checks. No custom comparison
normalization is introduced.

`scripts/assemble_challenge.py --check` authenticates this assembly. Source module
imports are replaced by their fixed bodies; external Mathlib imports are retained.
The immutable first foundation checkpoint remains tagged separately with its own
exact-source receipt; later development never inherits that receipt automatically.

These native checks do not constitute the registry's canonical Linux sandbox,
renderer, editorial decision or publication. They do not prove correspondence
with the manuscript or whole-paper coverage. Independent source/semantic review
and the explicit scope map address those separate questions. Exact-source
receipts and final reviews are retained outside the frozen source to avoid a
self-referential verification/status edit loop.

Before an eventual release, complete the outstanding mathematics in SCOPE.md,
confirm project-specific human roles, recheck current intake policy/schema and
account/duplicate state, obtain exact-source canonical and rendering receipts,
and run the repository release-packet guard. A security-changing runner requires
specific action-time authorization. No prior topology-job runner approval or
submission authorization transfers to this project.

## Completion reconstruction follow-on

The next source tranche adds finite layer-cake duality, compact-convex separation,
the exact completion criterion (including zero weights), and actual sparse game
witnesses. A development build passed 3142 jobs before the expanded imported-
definition bridges. Independent internal mathematical review found no defect in
the three reconstruction modules; it explicitly excludes algorithmic complexity.
These edits do not inherit the preceding checkpoint's exact-source verification.
A separate immutable external receipt will identify the final commit and all
actual build/export/comparator/kernel outcomes. No canonical sandbox, rendering,
registry eligibility or submission claim follows from native checks.

The first reconstruction freeze, `16972876b887323868c7907a3be99c6875ff87a1`,
passed native build, module kernel checking, protected compilation and both
exports, then failed the protected comparator at fixed definition
`weightedVariation`. Elaborated terms exposed generated numeric evidence:
the Solution referenced `weightedVariation._proof_1`, while assembly shared the
same evidence with `gridNode._proof_1`. The follow-on source uses an explicit
natural-number cast for that denominator, preserving its real value while
avoiding generated proof identity sharing. The comparator is unchanged. The
failed immutable receipt is retained outside source; the correction needs its
own exact-commit run and independent review.

## Two-anchor rigidity follow-on

This tranche adds normalized bounded sparse-witness wrappers, arbitrary-target
prefix exposure, tight-prefix edge saturation, bounded normalized fixed-share
rigidity, the exact uniform formula correspondence, and inverse rigidity under
two minimum shares. Independent internal mathematical review found no circular
mass assumption in the minimum-share argument. All proof helpers remain public
and exposed. Selected real numeric literals use explicit natural casts to avoid
generated numeral-evidence sharing under protected assembly. Finite-ordinal
source evidence is independently bound to the compiler's GitHub blob, with
literal/field bridges compiled through both entrypoints. Full native exact-source
results belong to the separate immutable receipt for the final commit, not the
preceding reconstruction checkpoint. At that tranche quantitative support and uncertainty work
remained open; no submission, canonical sandbox or rendering is claimed.

## Quantitative support follow-on

Seven further modules prove prefix stability, finite-subset quantization, the
actual support partition, inverse-square witness lower bounds, matching
existential upper support order, and attained total-support minima for both
commitment classes. The integrated development build passed 3168 jobs with
172 source proof audit declarations and 62 selected contracts. New independent
entrypoint bridges for sorted finite coverage, cubic power means and natural
minimum attainment/minimality compiled separately. Nat.find is noncomputable
for this real existential predicate; the dense witness proves nonemptiness.
Upstream Nat.find definitions are unexposed, so the projection bridge is a
proved equality from minimality and attainment, not a claimed literal unfolding.

These development results do not inherit any earlier exact-source receipt.
The external receipt for the frozen quantitative commit records the fresh native
build, protected dependency comparison, altered-helper rejection, axioms and
kernel outcomes. The explicit parity/bin constructions, residual-minimum law
packaging, uncertainty theorem and other open rows in SCOPE.md remain unfinished.

The first quantitative freeze, `79fc325e467d7b2c8ee55f49b09ba6319e255e4d`,
passed its clean build, axiom audit, module kernel, protected compilation and
both exports, then failed dependency comparison at
`uniformMinimumTotalSupport_zero._proof_2`. Elaborated evidence showed its
statement's `by omega` mass-positivity argument referenced a module-private
auxiliary theorem under different module identities. The correction uses direct
public order proof terms in the minimum-zero and sharp theorem statements, plus
reflexivity for zero tolerance. The fixed definitions and comparator are unchanged;
the failed receipt remains immutable and the correction requires its own run.

## Residual minima and uncertainty lower follow-on

Three subsequent modules package attained residual minima with their distinct
fixed/minimum-share tolerance ranges, and prove interval and one-core lower
restoration, actual support-count meanings, attained minima, radius-zero
correspondence and origin density. Statement proof arguments use direct public
terms, with fixed rational literals expressed through natural casts. The prior
quantitative checkpoint remains immutable with its own successful receipt.
This new source requires separate exact-source native checks. It does not claim
the matching uncertainty upper law or the paper's explicit bin construction.

## Balanced bins and sharp uncertainty follow-on

Ten further modules prove explicit central-label bin compression, canonical
exhaustive partitioning, balanced-bin size bounds, call contraction, moment-loss
bounds, bounded skew completion, and the clipped single-core adjustment. These
combine with the attained minima to prove both sharp uncertainty laws, with the
paper's constants and parameter ranges. The integrated development build passed
3194 jobs with 259 source proof audits and 149 selected contracts. Retained source
and independent entrypoint bridges cover the bin equivalence, dependent finite
enumeration and reversal used in pairing.

The cast-stabilization pass was corrected to keep divided powers as natural
exponents; failed development logs are retained outside source. The standalone
reviewed proofs and the final integrated source are separately identified. This
tranche requires its own frozen-commit build/export/comparator/kernel receipt;
it inherits no gate from the preceding lower-bound checkpoint. The source's
explicit residual-payoff algorithm and exact global parity formula remain open.


## Exact midpoint and finite correction follow-on

The sharp-uncertainty checkpoint `2ea1b04d485ff500a4c75ed006c21aa717519873`
is preserved with its complete 12-check native receipt (SHA256
`1c9b614de2707a9020e325a5f918a97e943187f6373606c47dd2e142f558621b`),
3194 build jobs, 259 source proof audits and 149 protected contracts. Both native
kernel checks passed and the altered-helper negative control was rejected by
the unchanged comparator. These are native macOS checks, not registry clearance.

Four follow-on modules prove the exact global parity formula, positivity and
injectivity of the original middle representatives, exactly h residual support
for odd bins, and the equal odd-bin game witness with an anchor attaining its
exact error. Balanced full-game witnesses satisfy the sharper finite correction.
Source-fidelity review distinguishes real subtraction in the parity term from
truncated natural subtraction, and verifies positive mass for the exact support
claim. Finset.image and compiler Function.Injective have retained exact-source
provenance and separately built entrypoint semantic bridges.

These new bytes require their own frozen-commit native receipt, including all
168 protected contracts and 278 source proof audits. The current tranche does
not inherit a passing check from its predecessor. Whole-paper coverage,
canonical Linux checks, rendering, intake and publication remain separate.


## All masses and extra linear moments follow-on

The exact midpoint checkpoint `ced929e5132058ef4575d7273d2ff1a226627cac`
is preserved with native receipt SHA256
`7ea68f5e6e14e78140438318e86be0dadfcd8c77c46029f36416f509832ee610`:
all 12 checks passed, including 168 protected contracts, 278 axiom reports,
both kernel checks and rejection of the altered fixed helper. Its independently
authenticated tag and bundle preserve the complete history.

Six follow-on modules cover every nonnegative residual mass and make the finite
cardinality minima explicit. They also preserve d arbitrary additional linear
measurements, including the sharper exact-equilibrium count, while retaining the
original k-anchor game. Zero mass is proved to force every residual weight to
vanish; no positivity or nonempty-type assumption is smuggled into that branch.
The actual original-row guards and bounded skew reconstruction remain proved.
Existing imported-definition meanings and provenance apply to these wrappers.

This new source has 291 actual source proof audits and 181 selected contracts.
Its full frozen-source checks require a separate native receipt. It inherits no
verification gate from the preceding midpoint checkpoint. Algorithmic, graph,
conic and joint-k construction clauses in SCOPE.md remain unfinished.


## Score-prefix and conic follow-on

The all-mass/extra-moment checkpoint
`0834612ffb5c9ef52eb7cf17b02a0708cec3ce27` is preserved with native receipt
SHA256 `6175f6f2456f0c96b4ee558748e637de2665812f4943a9f5246c2031965eeb0c`:
all 12 checks passed, with 181 protected contracts, 291 axiom reports, both
kernel checks and altered-helper rejection. Independent verification authenticates
the source, pins, logs and exports; its complete-history bundle is preserved.

Three follow-on modules prove the score-prefix reduction, exact quadratic and
concrete rotated-cone representation, and convexity at fixed tolerance. The
threshold maximum is only taken after genuine nonemptiness is proved; prefix0
handles empty sets. The retained predicate inventory covers Antitone and
Finset.Nonempty; finite maximum/supremum definitions and membership/upper-bound
contracts have source evidence and bridges through both entrypoints. No shared
checker or protected comparator is changed.

The new integrated source requires its own exact frozen-commit native receipt.
These results do not certify an executable conic solver, rational exact-decision
complexity, interval convexity/separation, or any publication readiness.


## Interval and arbitrary-cover follow-on

The conic checkpoint `33bd1d04598ebead90586dbf903538210ac45708` is
preserved with receipt SHA256
`5fce87be4dafc15f6bfc6225fc731ce48e912119cd640d1647329482f761217d`.
All 12 native gates passed there: 307 source axiom reports, 197 protected
contracts, both kernel checks, and rejection of a deliberately altered helper.
Its independently authenticated complete-history bundle and review are retained.

The historical interval/cover tranche added 13 modules and 57 theorems, for 59
mathematics modules, 364 source axiom reports and 254 selected contracts.
That tranche was subsequently verified at a618d1a32b31abf44277168f0ab0bcba30c3c463,
with the receipt recorded below. The root imported-definition checker accepts exact identifiers ending
in primes, with explicit negative identifier controls. The protected comparator
is unchanged. The native verifier also binds its two root audit tools to the
recorded clean Git commit and rechecks their hashes after execution.

That historical scope excluded joint interval convexity/separation, general value
stability and joint-k lower constructions, which the expanded tranche below proves.
Algorithmic gaps are tracked precisely in the current SCOPE.md. Native macOS
verification is separate from canonical sandbox checks, intake and publication.
No submission is authorized or attempted.


## Joint geometry, stability, gap correctness and cloned-anchor follow-on

The interval/cover checkpoint `a618d1a32b31abf44277168f0ab0bcba30c3c463`
is preserved with native receipt SHA256
`86e5c0a4d1328312e1638df58888ba21e1ad4acd7276d85d6cca4a2e8900ec21`.
All 12 gates passed: 364 source axiom reports, 254 protected contracts, both
kernel checks and altered-helper rejection. Independent source, semantic, static
and evidence authentication reviews bind all 83 files; the complete-history
bundle is retained.

The expanded follow-on contains 92 mathematics modules, 499 source proof audits
and 389 selected contracts. The external exact-source receipt mechanism identifies the complete frozen commit
and tree; this paragraph does not assert that a new run has passed. The protected comparator is unchanged. Literal tuple, singleton,
disjoint-sum, finite enumeration and actual conditional-infimum meanings have
pinned source evidence and separate semantic entrypoints. Joint REAL numeral
normalization follows the established explicit Nat-coercion discipline.

SCOPE.md separates the proved joint interval and clone-family mathematics from
the remaining rational algorithms, executable separation and operation/bit-cost
proofs. No predecessor receipt verifies altered source bytes. No registry or
journal action is authorized or attempted.

The expanded tranche includes the independently reviewed rational checker,
fixed/gap value minima, interval gap recovery, floor/allocation-grid value bounds
and conditional rational bisection. Both semantic entrypoints retain actual Rat
and finite-support enumeration meanings, with Batteries RatCast authenticated
separately at its own dependency pin. RatCast supplies a bare map; Real cast laws
are proved contracts. Native verification remains separate from canonical Linux,
registry rendering, editorial eligibility, human role confirmation and submission.


## Computable rational grid and supplied-point follow-on

The preceding joint/algorithm source was verified at
`c21990c76e3b70395b56fa9f4d826c75b002509a`, with native receipt SHA256
`27852b6b8acd67384aef9e2fa9c1ada466d30f4f31b92f9b97cb4eb127391c00`.
All12 native gates passed there: 3316 build jobs,499 audited proofs,389 protected
contracts, both kernel checks and altered-helper rejection. Independent source,
static and receipt/bundle authentication reviews bind all119 source files.

The rational-grid addition gives95 mathematics modules,513 source proof audits
and403 protected contracts. Exact-source results for this expanded source belong
to an external receipt identifying its complete frozen commit/tree; a predecessor
receipt does not verify altered bytes. The genuine computable Rat ceil route and
integer Nat.sqrt algorithm have separate pinned compiler/Mathlib evidence and
literal bridges through both entrypoints. Two executable controls test acceptance
of a valid zero-residual case and rejection of an offending zero-mass residual row.
The grid and point checker are executable, but no existential LP feasibility
solver, rational completed-matrix constructor or bit-cost theorem is asserted.


## Rational elimination and reconstruction follow-on

The new tranche has 17 mathematical modules and 85 theorem contracts. It adds
actual rational LP feasibility, real/rational transfer, real-game exclusion,
rational matrix reconstruction, finite linear repertoires and concrete
bisection/value certificates. Independent internal mathematical review and
scratch compilation precede integration. Three composition controls exercise
successful reconstruction, true rejection and exact bisection width; the solver
and residual controls additionally cover empty, inconsistent, one-sided and
nonzero matrix cases. Both entrypoints retain literal elimination/index bridges.
All selected source declarations enter the standard axiom audit and protected
Comparator. The unchanged altered-envelope negative control must still reject.

The immutable 95b5ea24578121fb4cb95faf2305c25f159bd522 checkpoint passed all 12
native gates before this tranche. It does not verify these new bytes. A fresh
exact-source receipt outside the frozen package records the follow-on outcome;
no future commit identity or future PASS is embedded here. Polynomial cost,
canonical Linux verification, registry rendering and editorial readiness are
separate unestablished claims. No submission is authorized or attempted.


### Generated matcher identity correction

Commit 73f6b11dc7df7b59c6d45c2c70f6528f32bb4bd1 passed its clean 3368-job
build, all source axiom prints, source kernel, protected compilation and both
exports, then failed the protected Comparator at rationalGapAlgorithm. It is
preserved as a failed verification history, not a complete checkpoint. Export
inspection found generated match-helper reuse differing between assembled and
separate modules in Algorithm and the gap-feasibility decider. Public Option.bind
and dependent Option.rec replace those matches; two finite-index selectors use
explicit natural values. The five affected module revisions preserve all19 theorem
headers and have independent internal semantic review. The Comparator, negative
helper control, definition-hole policy, root tools and dependency pins are
unchanged. A fresh exact-commit receipt is required for the corrected bytes.


## Interval rational program and automatic-round follow-on

The preserved425fba69adc05271b51de96be1a326cdda948670 checkpoint passed all12
native gates, including488 protected contracts and598 source axiom audits. It
does not verify this altered tranche. The addition has18 mathematical modules
and50 source proofs, taking the package to130 mathematics modules,648 source
proof audits and538 protected contracts. Nine executable controls cover
automatic rounds, compatible/inconsistent core intervals, empty systems, invalid
residual mass and certificate skew rejection. Exact finite index and Nat.log2
evidence is pinned and bridges compile independently under both entrypoints.

Independent internal mathematical reviews cover all50 new proof declarations;
exact hashes and scope limits are retained externally. A fresh frozen-commit
receipt, separate kernels/exports, protected comparison and altered-helper
rejection are required before describing the integrated bytes as verified.
Protected comparator behavior, dependency pins and root verification tools are
unchanged. Whole-paper, polynomial-cost and canonical-release readiness remain
unestablished. No submission or publication is authorized or attempted.


## Physical-repertoire interval value follow-on

The preserved cbe6aadb16069f666edb28cfa9e71af161b90fdb checkpoint passed all12
native gates,648 source audits and538 protected contracts, with independent
source/log/kernel/export/bundle authentication. It does not verify these altered
bytes. The new15 mathematical modules and32 independently reviewed proofs take
the package to145 mathematics modules,680 source audits and570 protected
contracts. Five executable controls cover accepted/inconsistent residual floors,
automatic approximation and its computed width, and negative-tolerance rejection.
Precise imported usage, semantic/static reviews and a fresh exact-commit native
run remain required for this tranche. No future PASS or commit is embedded. No
submission or publication is authorized or attempted.


## Physical consistency initializer follow-on

The preserved416c2db8b46bbb2872935e3ef094105210817536 checkpoint passed all12
native gates and independent exact-source authentication:145 math modules,680
source axiom audits and570 protected contracts. It does not verify later bytes.
The new5 mathematics modules add12 independently reviewed proofs, giving150
math modules,692 source audits and582 protected contracts. Eleven executable
controls cover feasible/infeasible floors, computed consistency and game
initialization, actual bracket width, zero residual and fully empty cases.
Fresh integrated consistency, protected comparison, kernel/export and exact-commit
verification are required before claiming this tranche verified. No submission.
