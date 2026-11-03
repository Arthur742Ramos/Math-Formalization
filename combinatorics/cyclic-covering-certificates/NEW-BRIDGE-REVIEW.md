# Independent review of normalization and representative-extension bridge

Publication context: this is the retained source review and its dated port
supplement. References below to the round-five runner, failed attempts, or
`attempts/` directory refer to the original research supplement, not files
in this source-publication directory. Pending compilation statements describe
the review checkpoint; later exact-source build receipts are kept separately.

Date: 3 November 2026.

## Review status and conclusion

This is an internal AI source review, not a human or external review, a public approval, registry submission, or independent compilation attestation. No Lean source was changed by this reviewer. The five new modules and their relevant original definitions were inspected. No mathematical/source blocker was found for the stated fixed-representative result. Publication remains conditional on the coordinator's exact-toolchain build and verification gates.

The new final theorem `CyclicDigitTransport.no_representative_extension` states, for every `c : Fin 17`, that there is no function `x : Fin 10 → Fin 9` satisfying the original `CoveringTransforms.Extends (representative c) x`. It does not merely assume eligibility, moment equations, normalized digits, or the desired nonextension conclusion. Those necessary conditions are derived from an arbitrary putative extension before invoking the existing arithmetic exclusion.

## Mathematical and source checks

1. `covered_ten_perm` extracts the nine distinct residues from a covering list of length ten, leaving exactly one extra residue. Their sum is 36, so the extra residue equals the total sum modulo nine. The count theorem consequently gives one occurrence of every residue and one additional occurrence of that sum.
2. `translate d x` means x minus d modulo nine. The Nat subtraction cannot truncate incorrectly because d is below nine. Translation by the total sum normalizes a length-ten list to total sum zero, since ten is one modulo nine. For covering lists its multiset is `[0,1,...,8,0]`.
3. Simultaneous column normalization uses each column's own sum. Its pair difference is the original difference minus the difference of column sums. `translate_difference` has this sign, and surjectivity supplies coverage preservation. `normalized_pair_perm` applies the original `CoveringScheme.Covers 9 10 k` predicate directly. It is a valid arbitrary-array normalization result, not a classification theorem.
4. `representative` reads the original `ArithmeticCertificate.entry` table, with explicit indices bounded by 17, 10, and 5. `entry_lt`, `first_column_zero`, and `column_sum_zero` are checked finite propositions. As an independent supporting calculation, Python parsed all seventeen literal arrays and verified their 10-by-5 dimensions, entries below nine, zero first columns, zero column sums modulo nine, and pairwise coverage. This is supplemental evidence, not a kernel proof.
5. `CoveringTransforms.difference a b` is b minus a, so `Extends m x` covers x minus each old column. This agrees definitionally with `translate (m r j) (x r)`. The other original coverage predicate uses first column minus second; this distinction is correctly respected locally. A global equivalence between the two original coverage predicates is not claimed.
6. `normalize_extension` translates only the new column and preserves its extension property without assuming old column sums. The zero-sum property of the literal old columns is used separately to establish the normalized difference multisets. The zero first column gives the normalized new column multiset itself.
7. Lower digit multiplicities of `[0,1,...,8,0]` are exactly 4,3,3. Each lower-digit fibre has upper digits 0,1,2, with one additional zero in the zero fibre; hence first moment is zero and second moment is two in F3. Both filter and conditional-sum forms faithfully express these facts.
8. `literal_lower_columns` identifies the imported profile table with the lower digits of the very same representatives. `extension_eligible` derives every part of `Eligible`: ten rows, counts 4,3,3, and the difference histogram for all tested columns. Dropping the first column in the old profile test is harmless because the first column's constraint has already supplied the quotas.
9. `profile_get` proves the actual list lookup agrees with the corresponding row's low digit for every bounded row. `vector` agrees with the high digit on rows 0 through 9; its zero default outside that range is unused by every ten-term sum.
10. `phase_eq` and `upper_eq` connect the imported arithmetic formulas to actual difference digits. The high-digit offset is old upper digit plus one when new low digit is smaller than old low digit; subtraction of that offset is the correct borrow convention. Independent evaluation of all 81 pairs of Z9 digits confirmed both lower- and upper-digit formulas.
11. `moments_transport` sums the actual ten rows. `linear_point` restores the offset from the upper difference and yields the coefficient times the new upper digit. `linear_of_moment` sums this identity and matches the original modular RHS. No equation is omitted: e below 15 yields j=e/3 below 5 and t=e%3 below 3. The second component covers all five columns and three fibres.
12. `no_digit_lift` is applied to the derived eligible profile and derived `LiftEquations`. Its 71 linear certificates and exceptional affine obstruction are the existing arithmetic result. There is no circular dependency from these older modules back to the new extension theorem.

## Proof trust and build limitations

The five inspected new sources have no proof placeholders, custom axioms, native-decision calls, unsafe definitions, or foreign implementation declarations in a comment-stripped scan. Their proofs use ordinary Lean constructions, finite `decide`, simplification, induction, and `omega`.

The existing new-module logs report axiom dependencies within `propext`, `Classical.choice`, and `Quot.sound`. In particular the final extension theorem includes Classical.choice; it must not be described as having only the two axioms reported for some older results. DigitTransport's worker reports a successful Lean 4.19.0 compilation of the source hash below, and its log and JSON evidence were inspected. This reviewer did not rerun Lean. The coordinator owns exact Lean 4.35.0-rc2 compilation and must associate any later verification with the final ported hashes.

The earlier fresh Lean 4.19 replay had killed triangle jobs with empty logs under reported resource contention. This is a failed/incomplete replay, not evidence of a full fresh pass. It must remain recorded separately from older successful reports and later exact-toolchain results.

## Scope still open

The bridge now proves actual nonextension of the seventeen supplied literal representatives, not just nonexistence of arithmetic lifts. It does not prove that every five-column covering is equivalent to one of them. Candidate-generation exhaustion, triangle completeness, and formal integration of the triangle transformation certificates remain separate obligations. Consequently unrestricted nonexistence of a 10-by-6 Z9 covering is not established by this theorem. The whole manuscript, cyclic45 obstruction, and infinite-family construction are likewise not newly proved here.

## Mechanical Lean 4.35 port review

All 48 original Lean modules were compared against their counterparts in the port directory. After removing only the added leading `module`, converting `public import` back to `import`, removing `public section`, removing `@[expose]` before `def`, and ignoring blank lines, every remaining line was identical. Thus no theorem statement, proof body, literal certificate, or computational definition was changed in this port snapshot. These visibility/reducibility edits support the newer module system; this source comparison does not itself prove compiler compatibility or replace a fresh build.

## Exact source hashes

SHA-256 values identify the inspected snapshots. Paths below are artifact-relative labels, not publication links.

### New Lean 4.19 sources

- `cyclic-normalization-new/Normalization.lean`: `c2d9c420167efd1207f59bd3f31532123f1566b325bcf167a4b6379dd083c04d`
- `cyclic-normalization-new/CoveringNormalization.lean`: `f5a899ac8b5f261f258824463151080b7d0efd3d516ddcda7803329c60827b2c`
- `cyclic-extension-new/RepresentativeExtension.lean`: `8c86597c1263e034085f0a1de07af1daa245dc3c95532d3cc52fea7710401a6f`
- `cyclic-extension-new/RepresentativeEligibility.lean`: `4d167056d7fa492f185cdc5f7283848ec6334ccef5c10fe1deb41e30116787fa`
- `cyclic-digit-transport-new/DigitTransport.lean`: `6607915353cfc8721c26dc23a1225f85df2ed292af85eada2dd47949f77296a6`

### Original and ported modules

Each row gives filename, original SHA-256, then ported SHA-256.

- `ArithmeticCertificate.lean`: `a437808e0d3cfec5f42b7fd27c45ff8d018feb81dfc48903506bce46faf85b94` → `f749dcd77f656b56f68a2f6de6643726863375066cc13efa8c032dae600a3506`
- `ArithmeticExclusion.lean`: `11a1cb598867823b7db57a6765c68dba4491996e0aeee6444c29962f9a767979` → `356a6985b3389c380bd5bd22107fe034084fadf5e1fc022b6f311449b71dea12`
- `BaseWitnesses.lean`: `b8c79685a8d7b747b7859a4ab61d6e136d6bb1a1022f0744b41c3b01df9042be` → `e80f310fb3fff64ab9acf1c7db4f1389abdd661321a8940e3e91e28bfadf9f9f`
- `CertifiedLinear.lean`: `4b576b0c372835b4db26f2fa7a60a3d52dcaa98d72236d99197b9a4b32dbb41b` → `a073a1ca46e0e37108352ae31190a2e39d6e4ae831bf383945963a45b84628a1`
- `Cyclic45Obstruction.lean`: `4d74a939555fa8c88132fe8eaa6e482b9825c393cb4ef94676288a5dfa6a19ab` → `2caf1a820864c022097436ebe5384e1c5302470efc43ecf95e15d0ecd555f8d6`
- `DigitLemmas.lean`: `6e4c69381c1758311271dd37fe7f38cb4472df092c4ae2f542da84a6629d7bd8` → `ea67a3e87dec48184b3afe60d8a5e6207e9aad1d719478d2fd6143a94b91f6d0`
- `ExceptionalProfile.lean`: `3b8e732187f003f232b012bba00c378025099b02ffa1490ca017e6739c6b22e8` → `8eddc0406118d96028d82f7c17977ba4ce2ba6a8d7c66ab93614916c0f749673`
- `F3Linear.lean`: `c42999b8632aef08c33ca997a4a370f2aab1e403be24815903e99869a436c2eb` → `40e63b54b21df9e85b1ad5423744a11d0b285f9ace5d3e97acafb026a3e3bde8`
- `Known63Witness.lean`: `c6af0e6ac1ee46553f337db74229c0197217e7ff63a6d2d8168267ddb041bf36` → `77584362c07a5c5a835cad2040756a117c09d4b500c1eca268abf124de30faf7`
- `PairedLift.lean`: `c83e176c2b160016f6f968138c0bb03fc31ff510b130db3af94cae58ad02c4b7` → `21fab88e4fc9a2216c7532606d097eb349c782c673d6b38d16b0fc9af7a2dea0`
- `ProfileCheck00.lean`: `ef4f2ac2d8b0bb70cced6cdd684fc1c0f161cdaecb9cf0a6174869d9d468c757` → `265ba225ac234462c80a2f661129babfde0c5f03e3222c00f518ff2dc3cc15ab`
- `ProfileCheck01.lean`: `2df293f1236110066bc91bdd0ef08dbdca049576ebe61d7067bbd8e2f8d19546` → `0ab274308eaa378e8936ee54acaea9cfcb40615dcb5a44554262c28853517ddd`
- `ProfileCheck02.lean`: `ea1047d3d9d82e8369e130d6e9dd17de6e71994dd89286b204fda7b2bf1aff94` → `7bc95f4215269d86fecd4468d205b1b20d8c2b82a5b0c9b67d1aabe77a059aa4`
- `ProfileCheck03.lean`: `0a030427840a89467fac8fe8045a542977318308eadf2635039a3dc0b5e293ce` → `fa19d9ba572b7aff586e65f5e9a359c86d0ca2a161e9e72b60ae4bebcd33889e`
- `ProfileCheck04.lean`: `c663c796c7a730e11a76943df7dca93c4ae7a56e90f4a64db585963826b92170` → `823157479eabd703770af3d77c05ce213342e8e8628eb08ae04f2e9807d8723b`
- `ProfileCheck05.lean`: `c943ac1c27c4f44927fc3906b86b262ae49191e5f0282a9aef22378565f1cd46` → `a04ee234d76cbba785fd5dca6b9ca65a8d6fc0804b9b1bf94c5c30bf477bc52a`
- `ProfileCheck06.lean`: `38b875c9d7b642ab19b28f589e88871bdb80b8f50cb7c0e6fe3cb6a2b03d81dd` → `ebc53dc7188e988e5476eaab22ed68f9be8880372f8890155e08600231cf2ddc`
- `ProfileCheck07.lean`: `22f556e94290b81465e04b5325755c208f156f4658572aa317564dfbffd2cd10` → `0fd250e87a1fd29373b3452a3473a6ef08b4aa2b32b2e995581744317db3e324`
- `ProfileCheck08.lean`: `909af017d6dd100aea22b2d7c4e5c357ac89af2ae6f4212d804aea4a51c4b591` → `78dd3b6f4a7572056f47e1a6ec953349fc1f045037ef50e18956589008c59a99`
- `ProfileCheck09.lean`: `fc777c21c19aac9e53ac3b416f338ffcfa92c310084381134a6924e674b91961` → `f2cebaf81596bdb15483f75c3aaef2cc89d845b7e010ce21a75a2459a4c749b2`
- `ProfileCheck10.lean`: `89fe82704dd140bb0a56352c7365a0dfba5a493bf1395b24a206eec2ae30fab0` → `ecfa86bb2732c6d29d3d03ce51c374a19f63c9116f5ef82d29353c567509f6a0`
- `ProfileCheck11.lean`: `50e607ea56fa901096003be4bea8ec70319f26f04f1e42e83ac35aa0e9d2f933` → `2936059d5bc0bc129f33997d6c350acc48546866d2d1b973ad0fdc4f4423f076`
- `ProfileCheck12.lean`: `b68b55fa83187feead111dc3a1be274b15e55a7f303dbab3824b961853539b1b` → `cad8ff3baf0e88f7effc7aca964255ca946780f8b177203fc295214cdabf35b1`
- `ProfileCheck13.lean`: `3cb9d55fe76689cab535d325508c8001f19e8f41b01e7a3de6d841c3614174a4` → `18dcfb50009250f2a06970a48790e68128f1da919bbc83bc239bdd3b68661724`
- `ProfileCheck14.lean`: `70f1c72438cbd558dadfa88df570d60bbd615a5a21f8425ebb24f6f68d9dca39` → `c82f51ec060e40cacee7bab306a4aa6d2c2d07f55e09ce77b8411f7a21856820`
- `ProfileCheck15.lean`: `d5543b41c5d0de6f7b50f3b0c58b06de085c966030adeb930dbbc625194ac734` → `16570c8f39323f1fb65b92faedde4215a6a41869f1ca0ccb0c178bb3feb0c254`
- `ProfileCheck16.lean`: `de8fc6e4e34cf35bf7bd9d25e19aa17f2384fdda67fe20d01e28e4309430ff21` → `1d11962068bc6c660ef4ef26b151eb7da7f0740254c25d76370c7a8591affcaa`
- `ProfileCoverage.lean`: `085aa3a831b408268455841a3b7572faa77ef7c2c15b2f8685b401ca61854d95` → `2567e298b7573fae68be524c6f539154c43d6b26effe307d8f6b86e571f0c8d1`
- `ProfileData.lean`: `857bd425c4c8b21419e4d2c7aca771687ff696c3e7ec16d17933dec91ce5e51f` → `b173a6e1ce2a4246e356bfe10575516aa99bc5b3525a78f063c797d7693ded54`
- `ProfileEnumeration.lean`: `85bea97aa2d5ec453fbce6d3f80f9b2e88f858d5116eee2c044051c1639d88a5` → `957138f146a25340c0eb4ca30ec79b1e2e81b80b3d6c451a36c1407c0c6b9986`
- `TransformSoundness.lean`: `442526962d76d0e28a0cc1b20a36b51c79c2e46aac59e446c26e45525827017b` → `9bd3c17964da550486ce9e3abb4c6ca8819966a2fbd20aa8b7d8f23f37dca318`
- `TriangleBatch00.lean`: `775f6ecb8ddfee74df46a1415c5b283b50a0f7052bc3d457e9d56d1550335cd2` → `02cac100e275a4e86fceaac976f5f50aacd28a4c841760bb512925bc6e55f1d1`
- `TriangleBatch01.lean`: `8a5c88aa3f0b5b6b9cbbeb7a02bbd9622bc9053081d46efd62bd836f8a3662ea` → `9bd0dfb756fa15ed27347af1a0fd674d4ba3532accb0c5d1be9b4c37c7ddef90`
- `TriangleBatch02.lean`: `5a10a448a0e426454251b5cf9a00819de9a2807fec732187ac759e5ebf240f7c` → `9380b9c4427ad610d528e638f7da0aa746c204138c47a95775c5552a59ff4412`
- `TriangleBatch03.lean`: `d1327abc56f18ddabd12b2e3d8f1f6d76ef2bc2ae39be529ca8b05f2ea64e47a` → `27deacd3f648cfaf6d77350cb87d93ddb9c18af1c3c5e47e5a8c4c139e5926d1`
- `TriangleBatch04.lean`: `cc0a61b6467d43f88c839519c0dd42c5ac351afcb83c1d5c3a7d1e3ec7a6a60e` → `e7fd2073992fdb82e8184e7af9de3719103adc9fca8623fb20bed6b8e46ffef5`
- `TriangleBatch05.lean`: `4c7cf2ab5e4d4f3547159001eb07aea28dc3974dedc299ec98e9dcebaaa13ab3` → `7f4ab7bde58610099b399c3d473e373733cdff196fad19d2e48e11a4abb3b4ff`
- `TriangleBatch06.lean`: `fe53fad9f0b6d42518ae8641fa09eadd144e9151eb8be82cd53e33863329e33d` → `14c5cf8ed27948e28b2399ed6bd6fa4d07c252cd161d7166f7452299dc6196ca`
- `TriangleBatch07.lean`: `16c5f679c776c2cc9d3e34c16230e703f4cc17eebfcf8ec279322a1182ebd602` → `6beed8280a8aa9d76f38e72bf71e932c800d406361a140b7a2e2552aac2ce9d3`
- `TriangleBatch08.lean`: `4649a723df1baedf53abd7b5eb3512351c087ac96ea268fe1cb2f799bb988793` → `8880346e2ec8aca4d80572d13f026bb38f300fb6a46f1473dc1291ac63bdff98`
- `TriangleBatch09.lean`: `c4e1262b69692b036d1d39e6e94e68368940354dbe01fddbe9165265d5782431` → `146edfc726c821ab9f1d5449995c8900c0375674230fa818da83666d6e0b0d84`
- `TriangleBatch10.lean`: `460d6dc6a0d48e466479eb9a5d5301f56748d31fd60ae747f4f0bf3477e5b760` → `ac497a7e9a2b216bbcfdf91d3a7e11610b27d6605734a6d6018448b7de5353ac`
- `TriangleBatch11.lean`: `3c700623a78601b3ad4652d7e27e7d914efd6eb2bca4456d4f775bbd28f87eca` → `2fc9efc736ed94037b743e9859e9907067c1eea78534148cac1c4987f6b7a19d`
- `TriangleBatch12.lean`: `6f0a19150347f25cf823b7c75bd9525687c1137333f5f979b1fe11be57b8b7aa` → `d66f90f408a83344677c4f3800ea0a0282dad3cc141cfaff4a5867b5a1559811`
- `TriangleBatch13.lean`: `12da28d9476132cb1d8d5152c9d0d8e80b9f64997f3089a52d467426ec8edb75` → `0836ca90a314a214046d2e992a1452f4dd515c1eb0d3a58dc9842b89e9bfffc6`
- `TriangleBatch14.lean`: `12918360496d81011892c3792a657bd11ab088f8a011c80701d25ff2c749647c` → `3afdf0fa42e074f406afd3f13225ac6be93bb092198b6a4b2d7cac4144617d84`
- `TriangleBatch15.lean`: `e892f291d190a31fc5369f5245b3750c200dadb7669741ecd0bfa9d33944a49a` → `9ccedbb2ee58e0a37122d8cc0257dc827b61c5b1e0995ee5126e9ce393e163e6`
- `TriangleBatch16.lean`: `f4fdcca84c537f25ba22a4d24f3afdaf47711040bea45146b1ad28869a9aa3f4` → `f24af8a797d5ca6f30d882638d283c23a02ba082daa5ffdd7b24350f62376269`

## Supplemental supported-toolchain and runner review

Supplement reviewed on 3 November 2026 after the preceding snapshot.

The new Lean 4.35.0-rc2 port adds the same module/export annotations and makes four small proof adaptations: `mem_residues` proves the same finite universal membership proposition with `decide`; `translate_self` drops an `omega` invocation after `simp` already solves the goal; `normalized_sum` explicitly unfolds `normalized` before simplifying map composition; `upper_eq` proves the bounded row lookup `vector z r.val = high (z r)` and rewrites the goal before applying the same finite borrow identity. Source comparison confirms these adaptations do not alter any theorem statement, definition, hypothesis, or mathematical conclusion. They are faithful proof-body repairs for newer elaboration/simplification behavior.

The inspected `port-verification.json` now records PASS for all 48 old modules on Lean 4.35.0-rc2, with unchanged inputs. This reviewer checked all 48 recorded source hashes against the port files. This updates the earlier pending-build status for those modules only. The new-module supported-toolchain compilation/complete closure run was still pending at this supplement's review time and is not asserted complete here. This remains inspection of coordinator-produced evidence, not an independently rerun compiler attestation.

`formal_round5/verify.py` was reviewed as the portable original-Lean-4.19 closure runner. It recursively orders the imports of the five requested modules; builds that closure serially into a fresh temporary directory; replaces LEAN_PATH with that directory; uses each source's directory as compiler cwd; pins the compiler version; enforces per-module timeout; records exit codes, printed axiom sets, log/source hashes and unchanged input checks; and fails on a missing/failed module or disallowed printed dependency. These are appropriate reproducibility checks for the inspected sources. No heavy execution was performed by this reviewer.

Runner limitations: its import parser supports the inspected single plain-import declarations, not arbitrary Lean syntax or the new `public import` port; it is intentionally pinned to 4.19.0 and must not be presented as a 4.35 runner. It audits printed declarations rather than automatically auditing every declaration. It inherits the remaining process environment, including possible dynamic-loader overrides. Its compiler hash/version are provenance, not independent compiler attestation. Windows execution is untested. Generic startup/configuration exceptions can abort without producing a final JSON report. Fixed log/report destinations overwrite current-run evidence on rerun, so preserving previous attempts requires explicit archiving as done in this package.

The original research supplement retains `failed-attempt1-report.json` and `failed-attempt1.log` for the initial cross-directory cwd error, and an `attempts/original-48-replay` directory for the earlier signal-9 replay. Its README accurately says 46 modules passed and two triangle modules were killed, and labels resource contention plausible rather than independently established. Those failed attempts cannot be relabeled successful on account of a later successful run. The successful 4.35 old-module report is separate evidence.

### Supported-port source and evidence hashes

- Supported-port `Normalization.lean`: `8c7ed187447c1c2e13ba4da9252ea2e30b5ca5c78f66b49b0dbd7ab673d8166a`
- Supported-port `CoveringNormalization.lean`: `7a44e2e1baf8eddcc7a1f83f20f94875d9d6b4524f5b7062429d4c6dba82cc56`
- Supported-port `RepresentativeExtension.lean`: `ea6549770954e7f992dd77bd6fea510bbeb3139af8bc4e3ca418e7eda58d04f3`
- Supported-port `RepresentativeEligibility.lean`: `443039741c6fe32914e1ec27d35698063b1dbe72dea9a8d99ba7fd55da43c96c`
- Supported-port `DigitTransport.lean`: `9731487db52a79d61d35c00ed8a2e5d45557cf345b47ba4c2dbf197b8543dc97`
- `cyclic-lean-port/port-verification.json`: `5fa2cb8063dcb3f868f802adbc871888d3a1b7e8123e7d1deddc1532da28ac90`
- `cyclic-formal-round5/verify.py`: `d39c96f8b6e4ab45d137d35b0301a0c3e7437a6c820c2973acd6958e649c5bd8`
- `cyclic-formal-round5/README.md`: `ed357d2653f09f1a5dcd2c53c3ada6a29821a8b9ddfcc98b65811c0e728ab46b`
- `cyclic-formal-round5/failed-attempt1-report.json`: `33401f5b9f170e4de06cca02af8f87677a1e705901f7702febd5200ff87722b2`
- `cyclic-formal-round5/failed-attempt1.log`: `48e9da06c2e228c00103540bdd9ea750d6b75af763cfcc99511983875d4da66d`
- `original-48-replay/report.json`: `076780483d48a671629badb6031be147fa081f7042b59ff9867d48e62b17d4b0`
