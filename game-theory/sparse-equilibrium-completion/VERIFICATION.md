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
Challenge is a deterministic assembly of the exact304 local mathematical source bodies with
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


## Executed floor-grid follow-on

The preserved8bc06639dbe13f12a721f039e0606756798c2733 checkpoint passed all12
exact native gates and independent authentication:150 mathematics modules,692
math-source axiom audits,582 protected contracts and186 source files. Its tag
and complete-history bundle are preserved outside this source. Later bytes
require their own run.

The new29 mathematics modules add60 independently reviewed proofs, bringing
the candidate to179 math modules,752 math-source audits and642 protected
contracts. Three executable control modules add22 passing guards, covering
finite enumeration, infeasible candidates, true variable-anchor feasibility,
nonzero-core optimization, solver-derived global decisions, epsilon0, empty
actions and residual-only actions. One finite-index test-helper theorem is
compiled in the controls and is outside the60 mathematical contracts.
The candidate still requires integrated imported-meaning closure, exact public
helper identity comparison, both exports/kernels and fresh immutable-commit
verification. Compiling drafts and preflight checks do not establish those
gates. No submission or publication is authorized or attempted.


## Sparse rational output follow-on

Preserved677b724c9ff7e5ef31e4a4fb212994534217a478 passed all12 native gates and
independent exact-source authentication:179 mathematics modules,752 actual
math-source audits,642 protected contracts and218 files. Its complete-history
bundle and tag remain outside this source. This history does not verify later
source bytes.

The next12 mathematics modules add31 independently reviewed, pinned-toolchain
compiled proofs: exact actual-grid compression, finite support LP search,
actual rational payoff completion, full-game validity, interval physical-row
reduction, sparse output, automatic value brackets and computed physical
initialization. The candidate has191 math modules,783 math-source audits and
673 protected contracts. Three additional control modules have23 passing
guards: actual support reduction from4actions to at most3, mass/nonnegativity,
skew/bounded payoff and response checks, incompatible interval floors, exact
rational recovered data, empty/zero-mass behavior, initialized sparse output
and automatic width. These controls are outside the31 selected math contracts.

Integrated imported-meaning review and a fresh frozen-commit native build,
protected dependency comparison, altered-helper rejection, exports and both
kernels remain required for the new candidate. Scratch compile successes do
not substitute for those gates. No registry or journal submission occurred.


## Source-explicit bin follow-on

Preserved91afffed2205d48ed60214ef7370c5a98ed5c362 passed all12 exact native
gates and independent authentication:191 math modules,783 actual math-source
audits,673 protected contracts and233 files. Its suspected closed support-index
helpers passed actual protected identity comparison; altered-helper rejection
remained active. Tag and complete-history bundle are retained externally.

Fourteen new mathematics modules add39 independently reviewed compiled proofs,
bringing the current candidate to205 math modules,822 math-source audits and
712 protected contracts. Two new executable control modules add22 passing
guards for actual[4,1] bins, central/cross/omitted signs, exact rational weights,
normalization, all5 response identities, skew/bounds and zero residual mass.
Two genuine finite-index/positive-length test helpers are outside these39
selected math contracts and compiled with the controls.

The new candidate retains expanded constructive indexing evidence with
66 material meanings,76 compiler contexts,2 auxiliary records and110 Mathlib
source files containing202 exact excerpts. Local source/provenance checks
and9 fresh optimization-mode rejection controls passed. The ten new semantic
contracts passed separate Challenge and Solution bridge builds before the09
freeze. Its integrated reviews are retained, subject to the later filter-context
discovery. Fresh immutable-commit gates remain necessary for each altered candidate. Prior receipt
history does not verify the new bytes. No registry or journal submission.


## Global sparse certificate and bin-identity correction follow-on

Frozen09e46bd223a0692b3a3a2ade46b680ba404776f8 passed its3576-job clean
build,822 actual axiom allowlist checks, first native kernel, protected alias
compilation and both exports. Its unchanged protected comparator rejected
rationalBinnedLabel, so it is NOT a fully verified checkpoint. The negative
altered-helper control after positive comparison and the export kernel gate
did not run. The failed receipt, exports and independent diagnosis are retained.
Lean shared generalized Fin bound and positivity proof auxiliaries differently
between assembled Challenge and separate Solution modules.

The correction reuses the existing executable public binCompressedLabel and
binnedLabel definitions. Five actual alias execution controls and all affected
bin proofs/22 guards pass. One representative proof now unfolds those genuine
public definitions explicitly. No comparator behavior, definition hole, allowed
axiom, toolchain or dependency pin is changed.

Eight new math modules add17 independently reviewed, strict-toolchain compiled
global proofs and two control modules add20 passing guards, including the
computed epsilon-width bracket. The candidate has213 math modules,839 actual
math-source audits,729 protected contracts and259 source files. The retained
meaning counts remain66 material,76 compiler and2 auxiliary, with111 exact
Mathlib files/203 excerpts. The final alias audit also retains the actual named
NeZero.one instance for its two direct users and four direct Nat successor
nonzero contexts; a generic one-nonzero bridge is checked through both entrypoints. A versioned literal filter expansion corrects
List.filter context for132 earlier and13 new users, plus the specifically
identified40 constructor/3 DecidablePred/2 Decidable predecessor contexts.
Historical receipts are preserved; earlier inventory-completeness judgments
are qualified by that newly discovered supporting-context omission.

At that draft stage, fresh integrated reviews and a new immutable commit run
were pending, and91afffed2205d48ed60214ef7370c5a98ed5c362 was the last fully
passing checkpoint. That corrected source subsequently passed as355 below.
No registry or journal submission, canonical Linux sandbox or release clearance
is claimed.

## Historical instrumented-certificate freeze

At that earlier freeze, the candidate contained232 math modules,910 math-source theorem audits and800
protected selected contracts. Independent internal AI mathematical/source reviews
cover71 added proofs; three control modules contain36 executable guards. The nine
new compiler contexts retain authenticated exact source/excerpts, and literal
NeZero/Fin.foldr expansions are assigned from actual declaration traces. The
meaning inventory is66material/85compiler/2auxiliary,111Mathlib sources/203excerpts.
At that freeze, nine additional semantic bridges and the exact build,
axiom/kernel audits, exports, protected comparison and altered-helper rejection
were pending. They subsequently passed at f3 as recorded below. The historical
85-context inventory has the retained-source qualification described below.
Prior checkpoint and failed-run evidence remain immutable history.
Native macOS checks do not establish canonical Linux/registry/release clearance.

## Completed corrected-bin/global-sparse baseline

Commit355f44f29419e7317dab3c0ac7e3fd9a142073c2, package tree
2efc570974794358fd00c0462318488d51057378, passed all12 exact native macOS
gates:3596-job clean build,839 source axiom audits, native module kernel,
fresh protected compilation, both exports,729 protected contracts with unchanged
axiom checks and deliberately altered-envelope rejection, and export kernel.
All259 source hashes, nine clean dependency pins and compiler/tool identities
were independently authenticated. Receipt SHA256:
973026910b6ce7ff3a85136b8b4345a896e7cb621a0d90c4cd0fb71f3e2e3e35.
Independent authentication SHA256:
ed3a0992b17f41fea65acbafe0786ca2254914734af2ee11001732e2f6e2428c.
A local checkpoint tag and complete-history bundle are preserved; bundle SHA256:
ebfbd6757d610679cb17d4359fa3b2c34533275a908adc2f24910a15f7451867.
The bundle/tag authentication SHA256 is
9be621d9e18be7601026b3931b26ed934837fc0b3ea6281babbe3b47acfd9d82.
These receipts certify that baseline only. The later71-proof tranche passed
its own gates at f3 below; canonical Linux, registry and journal submission,
release clearance and external human review are not asserted.

## Completed instrumented-certificate checkpoint and current correction

Commit f3c300572e22fb88de71183aee09ccc66785c3da, package tree
6cb153a406832759141270f0f18eac8f67ceb05c, passed all12 native gates:
3640-job clean build,910 source axiom audits, module kernel, separate protected
compilation, both exports,800 protected contracts and permitted-axiom checks,
deliberately altered-envelope rejection, and export kernel. All282 source
hashes and nine exact clean dependency pins were independently authenticated.
Receipt SHA256 c263f36095c64d3bda6b65a19125594ef9fac1598bf0b9621f9a0a0013b34984.
Independent authentication SHA256
a0d31c7b95c3e84719743406b993be857840809706c1ce457392ce2e77624ef8.
The complete-history checkpoint bundle SHA256 is
b72343d34ad6926a9ab9b46915c0a470b5dd8f7a2dfbdd6b871ed3231867d8e5;
independent preservation review SHA256
8d6583560637b5c269ab7d91f293d7cf815111c32769d01e2b1f1cc5efe308db.

Those mechanical outcomes remain valid. Retained-source completeness is
qualified: the old Nat.findX excerpt omitted its final application line54 and
literal WellFounded/Classical recipes were not retained. The historical43 source corrected these contexts with exact affected-user assignments and finite-equivalence/classical-equality wrappers. It subsequently passed all12 native gates at878941b36b81420c180ee57edeb1eab5a3246e53 for its own bytes. No predecessor receipt verifies altered source.

## General payoff bounds and actual worst-case support

The historical43-proof follow-on added payoff rescaling, general-M upper and hard-instance
lower bounds, and actual attained per-instance support minima and their attained
worst-case maximum. For every k≥2, m>0, M>0 and 0<η≤M, in both fixed-anchor and
minimum-anchor-share classes, the maximum of those minima lies between
`(sqrt(3/1216)/2) * min(k+m,k+sqrt(M/η))` and
`2 * min(k+m,k+sqrt(M/η))`. The hard input is an actual finite-label scaled clone
game; responses, anchor commitments and support cardinality are transported
through an equivalence. The zero game only establishes nonemptiness.
`worstCaseSupport_sharp_general` proves the two-sided bound.

`PhysicalAnchoredWitness`, `AnchoredSupportProblem`, `physicalMinimumSupport` and
`supportProblemMinimum` quantify over actual bounded skew completions and
normalized strategies satisfying every response inequality. Existence of their
least support is proved from original feasible data. `worstCaseSupport` takes
the maximum over all such problems using the proved finite cardinality cap.
`supportProblemMinimum_observation_invariant` proves that the original feasible
certificate does not affect that minimum when observed K,D and floors agree;
`anchored_support_problem_representation` represents every raw feasible input.
These extrema use genuine classical predicates and do not provide an executable
optimizer or a polynomial-time decision procedure.

At the historical43 source, the package had246 mathematical modules,953 source theorem audits and843
protected selected contracts. Strict scratch compilation and independent
internal AI mathematical review cover the43 additions. Final integrated builds,
separate protected identities, altered-helper rejection, exports and kernel
checks require a new immutable exact-source receipt. Those predecessor receipts
remain evidence for their own source only.

## Executable rational cut checks and the source-scale allocation mesh

This section records predecessor836ab90. Later additions and resolved gaps are described below.

The prior verified follow-on added59 proofs in17 mathematical modules:45 cover actual
balanced sorting, original action labels, running-sum prefix scanning and raw
or interval perspective cut checks;14 cover the allocation step proportional to
`epsilon/(M*k)` and its actual dense floor-search output. That historical package
had263 mathematical modules,1012 source theorem axiom audits and902 selected
protected contracts. Independent internal AI mathematical reviews cover these
additions; these are not human or external peer reviews. Only an immutable report for this candidate's complete source certifies the
checks named in that report. Reports are stored outside the frozen package.
A predecessor's receipt only certifies that predecessor.

`rationalSortedCutCheck` computes a descending score order and scans every prefix
until a violation occurs, carrying mass and payoff sums. For nonnegative M and
weights, `rational_sorted_cut_check_iff` proves its returned Boolean is true iff
all original cuts have violation at most delta. The bound
`m*(Nat.log2 m+2)+1` is the returned same-program **comparison count**: sorting
score comparisons plus quadratic prefix comparisons. It excludes arithmetic,
effective-score formation, equality guards, moment formation, getter and
administrative work, bit operations and machine runtime. No stability of sorting
or equality with the entire upstream mergeSort algorithm is asserted.

`rational_perspective_cut_check_iff` uses candidate-dependent H/q scores with
zero-mass H=0 explicitly required. `rational_interval_cut_check_iff` earns that
condition from the actual linear perspective bounds and forms H as sum(p*V).
The returned Boolean checks the quadratic cut component. Other linear, anchor,
core and global zero-row guards remain separate. It does not return a violating
subset or separating hyperplane; those outputs and full candidate-guard
composition remain open. M>=0 suffices for this cut checker; the existing
interval completion equivalence retains its explicit M>0 assumption.

For M>0, epsilon>0 and k>0, `rationalSourceFloorAllocationStep` equals
epsilon/(6*M*k); the k=0
branch uses the previous safe positive step. The actual generated allocation-node
count is `(1+floor(6*M*k/epsilon))^k`, including nodes later skipped as inadmissible.
This is neither a count of feasible nodes nor an algorithm-time bound.
`rational_source_floor_certified_value` supplies an actual compatible dense
rational game, all row bounds and a global interval of exact width epsilon.
No additional reconstruction error eta is hidden in that width. The older sparse
floor program still uses its conservative k+1 step; this dense variant does not
silently replace it or prove arbitrary-repertoire sparsification.

Source-inventory correction: authenticated compiler list recipes, including
logical/runtime length contexts, now retain precise supporting contexts for53
historical declarations. The existing finite-equivalence choice recipe is also
expanded through Trunc.out, Quot.out and Classical.choose for its exact19 users;
Nodup/Pairwise/list membership contexts are assigned to their actual affected
subgroups. These are source-retention corrections. Historical build, protected
comparison and kernel receipts remain evidence for their own source; the new
candidate requires its own checks. The literal Unit=PUnit alias additionally
receives its exact42 missing historical contexts; newly added Unit users carry
the same PUnit support. The specialized WellFounded.Nat.fix recipe is retained
for its exact final-trace new-target group, distinct from generic WellFounded.fix.
No blanket assignment to all1012 targets is
made, and the generic comparator, permitted axioms and dependency pins are
unchanged.

Whole-paper readiness remains false. Remaining work includes general repertoire separation, full arithmetic and bit complexity, polynomial rational
LP/flow guarantees, efficient sparse vertex selection and executable arbitrary
cover transport. Native macOS checks do not establish canonical Linux sandbox,
rendering, release-role or editorial readiness. No submission is authorized.

## Violating-cut payloads and exact candidate reconstruction

The next local tranche adds43 genuine proofs in8 modules, giving271 mathematical
modules,1055 source theorem audits and945 selected protected contracts. The
actual rational prefix scan returns an original-label subset whose cut is
strictly violated. Its None result agrees with the existing Boolean cut checker;
all-cut completeness requires nonnegative M and weights. A second payload
constructor uses the proved Nodup label list directly. Its executable data path
uses take/map and the Finset constructor without dedup; its equality proof with
the earlier List.toFinset program still imports the literal dedup semantics.
This tranche does not yet wrap the payload in interval perspective coordinates
or return affine separating coefficients.

The same-program supplied-score arithmetic ledger counts additions,
subtractions and multiplications as unit rational operations. It proves at most
7*m+4 written arithmetic operations and m*(Nat.log2 m+2)+1 comparisons, with
combined bound m*(Nat.log2 m+9)+5. It excludes score/getter formation, rational
normalization, equality tests, allocation, traversal and machine/bit costs.
Denominator products bound the reduced denominator of a rational list sum and
its binary length. Numerator growth, primitive arithmetic bit cost and complete
algorithm runtime remain unproved.

rationalIntervalExactCheck computes all finite linear perspective, anchor,
core-skew/core-interval and global lower-score guards, including every zero-mass
row, and the sorted quadratic cut check. For M>=0 it is equivalent to the exact
cast intervalPerspectiveSystem. An optional arbitrary physical repertoire R is
not wired into this base checker. The full-game existence wrapper retains M>0 and
explicit normalization, anchor nonnegativity and physical interval bounds.
rationalIntervalExactReconstruction returns actual rational cross and residual
payoff tables using the existing genuine rational residual LP at epsilon.
Its completeness holds for M>=0, including M=0; soundness gives the original
bounded normalized skew game under the stated physical premises and all rows
at epsilon without hidden eta slack. None rejects this particular candidate
(q,V,K), not the entire physical class. The residual LP is Fourier--Motzkin:
its correctness is proved, but no polynomial running-time bound is claimed.

The43-source narrow check passed strict compilation,43 axiom reports (including
two axiom-free proofs) and36 executable controls. Internal independent AI review
covers the mathematics, proof repairs and receipt authentication. These narrow
checks are not a clean exact-commit whole-package verification. All completed
mechanical gates for the integrated candidate are bound by immutable evidence
outside the frozen source; predecessor836ab90 passed all12 native gates for its
own bytes. Whole-paper and submission readiness remain false. At predecessor273fb8c, perspective violating-cut output and affine separation were open; the later52 tranche below supplies them. Complete arithmetic/bit costs, polynomial rational LP/flow guarantees, efficient sparse vertex selection and executed supplied-cover encode/decode transport remain open. Native macOS checks do not establish
canonical Linux, rendering or editorial readiness. No submission is authorized.

## Computed violating cuts, separation and flow foundations

This follow-on adds52 proofs in10 modules to predecessor273fb8c. The resulting
source at predecessor dd34 had281 mathematical modules,1107 source theorem audits and997 selected
protected contracts. These counts describe scope, not whole-paper completion.
Its exact-source verification and independent receipts are recorded outside the
frozen package; predecessor receipts certify only their own source bytes.

RationalPerspectiveViolation and RationalIntervalViolation connect actual
rational prefix search to an original-label violating quadratic cut. None is
equivalent to the corresponding cut checker, under the stated M≥0 and q≥0 premises, with H=0 at zero q
or the interval perspective bounds that imply it. RationalPerspectiveSeparator computes an
affine functional from the returned cut and the candidate mass. The exact gap
is M times a squared mass difference. For M≥0 the functional separates the
violating candidate from every real point satisfying the perspective cuts.
This is a separation certificate, not a polynomial LP implementation.

RationalFlowDemandCuts proves the signed-demand network cut identity.
RationalSaturatedFlow decodes a supplied nonnegative source-saturated arc-flow
certificate to a bounded skew payoff table when the unknown masses are positive.
RationalFlowZeroRows handles zero masses by an explicit piecewise table; the
original global row guard is essential. RationalFlowCertificateCheck checks the
physical premises and supplied certificate and returns the actual decoded table.
Some is sound. None means that supplied certificate failed; it does not establish
infeasibility. Zero total mass, zero capacity and empty unknown index sets are
covered where the theorem premises allow them.

RationalResidualReach executes finite flood layers on a Boolean adjacency
function. After n layers the reachable set is closed and equals finite
reflexive/transitive reachability. This input is a function, with no array-cache
or access-cost theorem. RationalNetFlow converts nonnegative arc flow F to skew
net flow F(u,v)−F(v,u), proving capacity, divergence and residual identities.
Residual capacity includes cancellable reverse flow. Applying C−F directly to
raw nonnegative arc data would use the wrong convention.

FiniteSkewEquilibrium proves that every finite nonempty real skew game has a
normalized nonnegative mixture with all row responses nonpositive. Its proof
uses compact convex separation, normalization of a nonnegative separating
functional and the zero self-payoff identity. The simplex is defined locally;
this is a classical existence foundation, not a computable optimizer or a
novelty claim.

Source retention adds the literal Relation.ReflTransGen declaration and exact
compiler routes for Nat's generated recursor and finite existential decision.
Nat.rec is compiler-generated from the retained Nat inductive; there is no
literal def Nat.rec. This also repairs62 precisely identified historical
WellFounded.Nat.fix source contexts. Predecessor273fb8c's native checks remain
valid, while its retained-source completeness was qualified by that omission.
The new finite-existential route is retained separately from finite universal
decision. Exact declaration usage follows actual compiled local dependency
closures, with no assignment merely from module membership. Both import
contexts retain executable controls and semantic bridges.

At that historical stage, residual path recovery, augmentation and a maximum
flow finder were still open; the cloud integration below supplies their functional
correctness. Polynomial flow and rational LP guarantees,
primitive arithmetic/bit costs and full runtime, efficient canonical sparse
selection and executed supplied-cover encode/decode transport. Existing comparison counts,
supplied-score unit arithmetic ledgers and denominator bounds do not prove
those runtime claims. Canonical Linux/rendering and release-role confirmation
also remain separate. Formalization authors and maintainers are unconfirmed;
internal AI reviews are distinguished from human or external review.
No registry or journal submission is authorized or performed.

## Historical cached-path checkpoint438b4ac

Checkpoint438b4ac had287 mathematical modules,1155 source theorem audits
and1045 selected protected contracts. Its exact-source12-gate native report
passed, including the pinned protected comparison, altered-helper negative
control and explicit kernel checks. The migrated report's source hashes were
authenticated against that unchanged commit. Its six new modules supplied48
proofs and18 executable controls, with14 imported-definition semantic bridges
checked through both canonical contexts. These historical results apply to
checkpoint438b4ac; the cloud integration described below requires its own
complete frozen-source receipt. The generated-definition validator and its14
portable Python regression methods establish retained-evidence consistency,
with mathematical source fidelity reviewed separately.

`RationalPositiveNetFlow` reconstructs nonnegative arc flows from skew net flow.
`RationalReachCut` and `RationalNetCut` prove saturation of the actual residual
reachable cut, cut/divergence identities, weak duality and a maximum certificate
when the target is unreachable. They do not find a feasible flow or implement an
augmentation loop.

`CachedResidualBFS` stores a finite Boolean adjacency table and, per layer, a
vector of discovered complete walks. Its actual Option result is None exactly
when the target is unreachable. A Some result is a genuine walk with the stated
endpoints, at most n edges and shortest length among genuine walks. Predecessor
extraction uses that returned path. This is not a predecessor-forest/linear-space
implementation, and no table-access, allocation, traversal-operation or machine
cost theorem is claimed. For zero vertices there are no source/target Fin labels;
the zero-size cache construction is executable. The rational residual graph uses
C−F for NET flow. Raw positive arc flows require the proved antisymmetrization
bridge; reverse residual capacity can arise from a negative net-flow entry.

`RationalNumeratorGrowth` adds actual magnitude, numerator-product, binary-power
and numerator bit-length bounds for rational LIST SUMS. These supplement the
existing denominator bounds. They do not bound intermediate sizes of arbitrary
LP elimination, normalization/gcd primitives or end-to-end rational bit time.

`FiniteSkewNash` gives an actual both-player mixed-deviation predicate for the
zero-sum game and proves its equivalence to the symmetric row-response criterion
for skew games. Finite nonempty skew games therefore have an actual symmetric
zero-tolerance mixed equilibrium. This is an existence/interpretation result,
not a computable optimization algorithm or a generic non-zero-sum Nash theorem.

Source retention records the genuine to_additive generators mabs→abs and
Pi.mulSingle→Pi.single separately from their actual generated declarations.
Their inferred names are not accepted as fake literal source heads. The narrowly
reviewed validator distinguishes the exact two generated source/target pairs. A retained
dual-export attestation binds actual target presence, while separately named
semantic bridges have now compiled in BOTH canonical entrypoints. Exact historical
marker audits cover240 abs and184 Pi.single contexts. Cached-table construction
retains Vector.ofFn→Array.ofFn and its coordinate contract; integer magnitude
retains Int's signed constructors and natAbs's logical/extern boundary.

The finite-complement source correction is operation-specific:223 contexts use
element search/difference,226 use shared erasure/runtime support, and183 older
contexts use the explicit Finset.erase→Multiset.erase wrappers. Three historical
erasure users do not require List.elem. These audits stop at the established
project-local/external-definition boundary; they do not claim exhaustive
expansion of every upstream theorem body. Frozen predecessor receipts remain
unchanged and mechanically valid, with the discovered retention qualification
preserved in this new candidate.

Whole-paper completion and submission readiness remain false. The cloud
integration below supplies a complete finite capacitated-flow finder and
augmentation correctness. Open work includes their operation and bit bounds,
polynomial rational LP guarantees, complete arithmetic/encoding
costs beyond the proved components, efficient sparse selection and the remaining
source-specific algorithm compositions. No publication or submission is made.


## Cloud integration of augmentation, finite flow and feature compression

This development integrates the preserved149 follow-on proofs and six proofs
for an equivalent directly recursive flow loop. The source has304 mathematical
modules,1310 source theorem audit targets and1200 selected protected contracts.
These counts describe the code under review; complete mechanical verification
is established by an immutable exact-source receipt outside the frozen package.
The earlier checkpoint sections retain their historical source state and do
not determine the current source's mechanical verification status.

`rationalAugmentOnce` uses the actual cached shortest path, checks its finite
safety conditions, computes an attained positive bottleneck and materializes
the updated table. For distinct source/sink labels, the checks are earned from
the path and None is equivalent to actual residual unreachability.
`rationalTableFindFlow` has finite input-derived denominator-lattice fuel.
Its returned table is feasible, has no residual source-to-sink path and
maximizes source value among feasible skew net flows; its actual reachable
cut supplies primal/dual equality. Source-equals-target is intentionally
excluded from the maximum/cut statements.

The fuel magnitude can be exponential in the input's binary encoding. The
preserved Nat.rec implementation constructs a state transformer for that fuel.
`rationalTableFindFlowDirect` returns exactly the same table using recursion
only after an actual successful augmentation; its equality, stopping, maximum
and computed-cut statements are proved. This change removes an avoidable
continuation-construction cost. A capacity-independent augmentation bound and
a complete program/bit-cost theorem remain separate obligations.

`rationalFeatureCompress` computes repeated rational kernel/deletion steps,
preserves nonnegativity, mass, every declared feature moment and original zero
coordinates, and bounds support by the feature dimension when mass is already
a feature. Explicitly adjoining mass gives one additional dimension. Its
kernel search currently uses Fourier--Motzkin elimination. The generic
compressor therefore establishes functional correctness; paper-specific
canonical-grid composition and polynomial kernel/bit bounds remain separate.

The retained narrow Linux checks cover the preserved149 proofs,149 axiom
reports and44 guards. The direct-loop development has six further allowed-axiom
reports and two large-fuel immediate-stop guards, plus independent internal AI
source review. These are distinct from protected identity comparison, altered
helper rejection, exports and independent kernel checking of an integrated
commit. Independent internal AI review does not assert human or external
peer review. The pins and permitted standard axioms are unchanged.

Whole-paper completion remains false. Demand-network/game composition,
capacity-independent flow runtime, efficient paper-specific compression,
polynomial exact rational LP and complete arithmetic/encoding/bit costs are
tracked separately. No registry or journal submission is authorized.
