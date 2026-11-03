# Formal proof coverage

Date: 3 November 2026. Original suite: official Lean 4.19.0, Std only.
This publication ports it to Lean 4.35.0-rc2 and adds five new bridge modules.
Exact build outcomes are recorded in external source-bound evidence.

## What the kernel checks

The reproducible combined result is `verification_report.json`, produced by
`run_formal.py`; externally retained source-bound receipts establish the actual
verification completed before a particular release. Each listed source is rebuilt into a new temporary directory.
Every printed theorem's axiom report is retained. A successful run rejects
proof placeholders, `native_decide`, user-added axioms, compilation errors,
unexpected axioms, and modified sources. The standard Lean axioms `propext`, `Quot.sound`,
and `Classical.choice` occur in the combined development; some finite and constructive proofs
use no axioms at all. This is not a claim that every theorem in the suite is
axiom-free.

| Mathematical claim | Formal files | Scope |
| --- | --- | --- |
| Ten-by-five and eleven-by-six/seven coverings over cyclic Z9 | `BaseWitnesses.lean` | Original pairwise modular-difference coverage and explicit existence. |
| Three-/four-trit moment criteria and the exact base-three carry identity | `DigitLemmas.lean` | All finite instances, by ordinary kernel reduction. |
| The 18-by-6 cyclic seed is an index-two difference matrix | `DigitLemmas.lean` | All 30 ordered column pairs and all 9 residues in the original difference predicate. |
| Arithmetic identities of all 71 left-nullspace certificates | `ArithmeticCertificate.lean`, `CertifiedLinear.lean` | Matrices/RHS are computed from literal representatives and lower profiles. |
| Left-nullspace witness soundness in all finite dimensions | `F3Linear.lean` | Inductive finite-sum proof over the three-element field, then application to every one of the 71 certificates. |
| Exact completeness of the exceptional affine line | `ExceptionalProfile.lean` | Supplied inverse-minor multipliers imply every coordinate formula; all 3 parameters satisfy the equations. No rank or solver result is assumed. |
| Exceptional quadratic contradiction | `ExceptionalProfile.lean` | The original chosen fibre at column 2, phase 1, rows 0, 8, 9 cannot have the required second moment. |
| Completeness of quota enumeration | `ProfileEnumeration.lean` | Generic induction for arbitrary lengths and all three quotas; specialized list has 4200 words. |
| Complete 17-representative lower-profile calculation | `ProfileData.lean`, `ProfileCheck00.lean` through `ProfileCheck16.lean`, `ProfileCoverage.lean` | Every one of the 4200 balanced words is filtered for every representative; exactly 72 profiles remain, and all match the 71 linear plus one affine certificate. |
| Combined arithmetic exclusion for all eligible profiles | `ArithmeticExclusion.lean` | `no_digit_lift` proves no solution to the defined linear and quadratic digit-lifting equations for any eligible profile of the 17 representatives. |
| Paired lifting preserves unique coverage | `PairedLift.lean` | Generic theorem under explicit selector and coordinate-fibre bijection hypotheses. It does not supply the character-sum existence theorem. |
| Every archived triangle has a checked representative transformation | `TriangleBatch00.lean` through `TriangleBatch16.lean` | All 2088 literal target matrices and supplied transformations pass direct finite checks. The ordinary export ties these targets to the candidate archive; exhaustive graph generation is a separate obligation. |
| Allowed transformations preserve coverage and transfer an extra column | `TransformSoundness.lean` | Generic preservation and extension pullback with the stated row/column/unit hypotheses. |
| Published cyclic 63 difference matrix and a small cyclic 3 six-column covering | `Known63Witness.lean` | Original finite positive properties, with explicit inverse-row certificates for the 63 matrix. |
| Narrow cyclic 45 projection/cycle obstruction | `Cyclic45Obstruction.lean` | Fibre count implication and the distinct-lifted-cycle contradiction. The complete relative-difference-set counting bridge remains outside these declarations. |

## New normalization and original-predicate exclusion

`Normalization.lean` proves that a covering length-ten list over `Fin 9` is a
permutation of all nine residues plus one extra residue; that residue equals
the sum modulo nine and is uniquely repeated. `CoveringNormalization.lean`
uses the original `CoveringScheme.Covers` predicate to prove simultaneous
column-sum normalization for arbitrary ten-row arrays.

`RepresentativeExtension.lean` and `RepresentativeEligibility.lean` derive
the exact difference multisets, fibre moments, and `Eligible` predicate from
an arbitrary original `CoveringTransforms.Extends` extension of one literal
representative. `DigitTransport.lean` proves all `LiftEquations` and concludes:

`CyclicDigitTransport.no_representative_extension (c : Fin 17)`

No additional sixth column extends the literal representative indexed by c.
The theorem does not assume normalized digits or the lifting equations.

## Exact remaining boundary

The package still does not prove unrestricted 10-by-6 covering nonexistence.
General simultaneous column-sum normalization is now proved, but a complete
canonical row/gauge transport into the enumerated candidate graph is not yet
linked. Exhaustive generation of candidates and triangles is still external.
The triangle batches check literal records, while a Lean integration theorem
identifying those records with the generic transformation API and applying
extension pullback remains a separate obligation.

The suite also does not yet formalize the full quadratic-character estimate,
finite-field existence and prime-power reasoning, every finite parameter
certificate, the external Pan classification theorem, or the entire
infinite-family theorem. Those claims retain the written proofs and the
independent ordinary computational verification documented elsewhere.

Earlier uncompiled candidate files remain only in the original research
archive. They are not compiled or selected by this publication package.

## Reproduction

Use the supplied Python runner, which builds the actual Lean sources afresh:

```bash
python run_formal.py --lean /absolute/path/to/lean --jobs 2
```

An ordinary Windows installation can provide its own Lean executable path.

Windows execution has not been tested in this session. The suite needs no
Mathlib, package downloads, C++ search, or external proof oracle. Compiler
jobs have explicit timeouts and a 64 MiB thread-stack setting for the finite
list reductions. The source package does not contain the compiler distribution.

`PROVENANCE.md` records the supported official release and archive hash.
The original research archive separately retains its historical toolchain receipt. The managed executor exposes
`/proc/self/exe`; its reported numeric PID does not select the same process in the mounted `/proc` namespace, where the corresponding numeric path can be missing or inaccessible; the official Lean
runtime uses the latter for executable discovery. The small audited
`proc_self_compat.c` maps only that exact own-process readlink request to the
former. It leaves all other operations unchanged and does not change Lean's
kernel or any proof declaration. The runner activates it only after observing
that precise incompatibility. Ordinary Linux and Windows installations do
not need it.
