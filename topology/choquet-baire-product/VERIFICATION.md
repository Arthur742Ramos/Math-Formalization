# Source-bound verification contract

The package owns Lean v4.35.0-rc2 and Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55
with its complete nine-dependency lockfile. Ordinary compilation builds six
modules with warnings treated as errors. CPChallenge is byte-identical to
ChoquetProduct; CPSolution publicly imports the proof module. Independent
ChallengeTests and SemanticTests compile all eight declaration contracts,
literal fixed-model meanings, full-history/empty boundaries and imported
semantic bridges. AxiomAudit prints transitive dependencies of all eight
theorems, five fixed model definitions and the explicit metric strategy.
Only propext, Classical.choice and Quot.sound are permitted.

Static hashes and source-origin checks do not establish mathematical fidelity
or successful compilation. Each actual build needs retained original logs.
A canonical full result requires the official pinned workflow in full mode
for the exact repository, commit, project and Comparator bytes, including
protected Lean Comparator and NanoDa/con-ron. Rendering needs its separate
exact-source report, original artifact and authenticated declaration surface.
Browser-runtime visual inspection is separate. External immutable receipts
record completed outcomes without editing this frozen source. A descendant
source is never claimed verified solely from a predecessor's report.

Mechanical checks and internal reviews do not establish editorial acceptance
or registration. Actual private attempts, duplicates and current official
protocol must be reconciled before any manual service action. This package
and its tests authorize no intake or security-setting change.
