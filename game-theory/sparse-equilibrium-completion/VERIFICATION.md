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
Challenge is a deterministic assembly of the exact twenty local source bodies with
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
