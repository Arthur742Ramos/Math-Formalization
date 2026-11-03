# Independent source and scope review

Date: 3 November 2026.

**Review type:** Internal AI source review. This is not a human or external review, a public pull-request approval, or a fresh build attestation. The review inspected the 48 Lean source modules, proof-coverage documentation, compiler runner, and supporting literal data. It made no source changes and did not run the Lean suite.

## Conclusion

The reviewed source is suitable for publication as a **partial formalization of cyclic-covering results**, subject to a fresh successful build. No mathematical/source blocker was found within its explicitly limited claims. It does not establish in Lean the whole manuscript, nonexistence of a 10-by-6 covering over Z9, the complete cyclic45 relative-difference-set obstruction, or the infinite-family theorem.

## Strongest established declarations

- `CoveringArithmeticExclusion.no_digit_lift`: for every `c < 17` and list satisfying `CoveringProfileCoverage.Eligible c xs`, no assignment `v : Nat → Fin 3` satisfies `LiftEquations c xs v`. These are fifteen linear fibre equations and fifteen second-moment equations computed from fixed representatives and lower profiles. The theorem covers every assignment to the ten relevant upper digits; values outside indices 0–9 are irrelevant.
- `CoveringCertifiedLinear.no_linear_solution`: applies the generic, inductively proved `CoveringF3.left_nullspace_sound` to each of the 71 literal certificates.
- `CoveringExceptional.affine_line` and `affine_line_is_solution`: establish the complete ten-coordinate solution line, without trusting an external rank computation. `no_fibre_solution` excludes the original selected quadratic fibre.
- `CoveringScheme.exists_covering_9_10_5`, `exists_covering_9_11_6`, and `exists_covering_9_11_7`: explicit positive witnesses under the original modular-difference coverage predicate.
- `CoveringKnown63.known_cyclic63_index_one`: exactly one row for each distinct ordered column pair and residue, using checked inverse identities.
- `CoveringFormalRound3.cyclicSeedIndexTwo`: the exact index-two difference counts of the 18-by-6 Z9 seed.
- Generic quota-enumeration completeness, paired-lift bijection, and transformation/extension theorems are substantive quantified implications.

## Source fidelity and nonvacuity

The extension equations and profile counts were compared with the companion manuscript, `covering_schemes_research_note.tex`, especially its exact modular moment criterion, extension equations, and formal-status discussion. The carry sign, equation ordering, profile composition, and stated scope agree.

Independent Python parsing and evaluation of literal data, without running the supplied verifier, established:

1. The profile counts are `[1,2,12,12,1,5,4,0,0,0,12,12,4,1,5,1,0]`.
2. All 72 supplied profiles satisfy the length, quota, and difference-histogram conditions in `Eligible`. Thus the central result is not globally vacuous. Zero-based classes 7, 8, 9, and 16 intentionally have no eligible profiles.
3. All seventeen copies of the representative table in `TriangleBatch*.lean` equal `ArithmeticCertificate.representatives`.
4. All 2,088 record targets exactly reconstruct from `q9_candidates.txt` using their triangle indices and fixed first two columns.
5. Concatenating the seventeen `archivedTriangles` lists exactly reproduces `q9_triangles.json`.

These Python checks are supporting source-fidelity evidence, not kernel proofs or proofs that the candidate archive is exhaustive.

Default-valued access such as `getD ... 0` could conceal malformed inputs in an unconstrained development. Here relevant concrete dimensions and bounds are checked or restricted; no current malformed-data counterexample was found.

The numerical hypotheses of `full_fiber_from_counts` are satisfiable: `(3,1,1,1,1)` is an example.

`PairedLift` does not simply assume its conclusion: coordinate bijections, selector uniqueness, and character compatibility legitimately imply the combined bijection. However, it constructs no finite-field instance. “Outside the hole” is an interpretation of abstract type `Y`, not a formal hole predicate in that module.

## Remaining formal bridges

1. An arbitrary covering must be transported through repeated-residue normalization into the exact `Eligible` and `LiftEquations` predicates.
2. Exhaustive candidate generation and triangle completeness must be proved, beyond checking the supplied archive.
3. Triangle certificates still need formal integration with `TransformSoundness` and `ArithmeticCertificate`. Batch files define their own representative tables and Boolean validity, importing only `Std`. No Lean theorem identifies those tables with the arithmetic table or applies the generic extension pullback to the arithmetic exclusion. The independent data comparisons above substantiate the connection externally, not within Lean.
4. The complete cyclic45 counting/projection bridge remains absent.
5. The finite-field character estimate, existence and prime-power arguments, external classification theorem, and complete infinite-family construction remain absent.

`TransformSoundness` has appropriate explicit hypotheses. Coverage preservation uses surjective rows and injective columns. Extension pullback uses a left inverse for rows and surjective columns; a right inverse is unnecessary for its proof. Its difference orientation is reversed relative to `BaseWitnesses.Covers`. This is mathematically harmless for coverage over all ordered pairs, but the development contains no formal equivalence connecting those predicates.

## Proof trust and runner

At review time, all 48 Lean source hashes matched the existing PASS report. That report lists 114 printed declaration axiom reports; their axiom union is exactly `propext` and `Quot.sound`. This review checked the correspondence but did not independently recompile those declarations.

A comment-stripped scan found no proof placeholders, `sorryAx`, custom axioms, `native_decide`, unsafe declarations, foreign implementations, or custom elaborator/macro/oracle machinery. Inspected proofs use ordinary kernel-checkable constructions, `decide`, simplification, induction, and `omega`.

The runner uses a clean temporary build directory and explicit import stages. It rejects compilation failure, disallowed printed dependencies, and changed source inputs. Important limits are:

- It audits printed declarations, not automatically every declaration. Their axiom reports cover transitive logical dependencies.
- Its token scanner and output parser are practical checks, not an adversarial verifier.
- It permits `Classical.choice`, although that axiom does not occur in the reviewed report.
- Version text and a recorded executable hash provide provenance, not independent attestation of every compiler/library component. A separate provenance file records several library hashes.
- It inherits environment variables, including any existing `LD_PRELOAD`. A sanitized official-toolchain CI run provides stronger reproducibility evidence.
- `proc_self_compat.c` redirects only the exact current-process numeric executable readlink to `/proc/self/exe`. Inspection found no theorem or kernel manipulation. It nevertheless adds to the runtime trust surface.
- Temporary `.olean` outputs are deleted after the run. Sources, hashes, and logs are retained as evidence.
- Windows execution remains untested.

`ArithmeticCertificate.lean` retains a stale comment describing the soundness bridge as future work. `CertifiedLinear.lean` now supplies that particular bridge. Correcting the comment would improve presentation without changing mathematical validity.

## Suggested registry scope

A suitable description is **“Verified components of cyclic covering constructions.”** The principal negative theorem can be `no_digit_lift`, explicitly qualified by its fixed-representative and eligible-profile predicates. Original-definition positive witnesses, generic F3 soundness, paired-lift bijection, and transformation theorems are suitable additional entries.

Incomplete manuscript-level goals should remain prominent exclusions. The package must not be described as a complete formal proof of Z9 nonexistence or of the entire cyclic-covering manuscript.

## Reviewed SHA-256 anchors

Paths below are relative to the reviewed formal source directory. The report hash identifies the existing report inspected during this review, not any later rebuild report.

| File | SHA-256 |
| --- | --- |
| `ArithmeticExclusion.lean` | `11a1cb598867823b7db57a6765c68dba4491996e0aeee6444c29962f9a767979` |
| `ProfileCoverage.lean` | `085aa3a831b408268455841a3b7572faa77ef7c2c15b2f8685b401ca61854d95` |
| `F3Linear.lean` | `c42999b8632aef08c33ca997a4a370f2aab1e403be24815903e99869a436c2eb` |
| `PairedLift.lean` | `c83e176c2b160016f6f968138c0bb03fc31ff510b130db3af94cae58ad02c4b7` |
| `TransformSoundness.lean` | `442526962d76d0e28a0cc1b20a36b51c79c2e46aac59e446c26e45525827017b` |
| `Known63Witness.lean` | `c6af0e6ac1ee46553f337db74229c0197217e7ff63a6d2d8168267ddb041bf36` |
| `Cyclic45Obstruction.lean` | `4d74a939555fa8c88132fe8eaa6e482b9825c393cb4ef94676288a5dfa6a19ab` |
| `FORMAL_COVERAGE.md` | `7b1734ed9ecd28db8302d6983aea5b872e9fa72f67b7a8835cca7171178604b8` |
| `run_formal.py` | `4aba649591883ee8938e0eb3345f18bc60c7443e475b46f327846547115f5979` |
| `proc_self_compat.c` | `b5c40585dc3c375782bb683f5d81a1a4827c38cdbfe4f9f853b58a7c2d06cdfe` |
| Existing `verification_report.json` | `8d35dc711a9c5f75039971da5d053514229c313cf421d2656fd6ed216ccb2e89` |
