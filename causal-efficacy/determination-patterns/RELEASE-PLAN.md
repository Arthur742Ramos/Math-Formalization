# Comparator and verification plan — not a submission

The delegation requires no holes or new axioms, including in Challenges. The
published Palomar policy at `PalomarPolicy@28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`
permits deliberate Challenge holes, but that permission does not override this
project's constraint. Challenges must expose all material definitions and
principal claims, with permitted import closure only; the Solution can import
project proof modules. Preserve separate Challenge and Solution environments,
then prove the matching definitions and claims with the protected Comparator.

A local experiment concatenated the actual hole-free Core, Patterns, Witness
and Necessity code into a self-contained `import Init` pattern Challenge. The original draft compiled with Lean `v4.35.0-rc2` at 821 physical lines and
32,465 bytes (SHA-256 `d44db5779ab620da3b421a08d4f530942fd68184130906dcb21c39dbfc49107e`);
later documentation edits require fresh size, hash and verification evidence.
This is below the current 1,000-line and 100-KiB hard limits but above the
300-line readability-warning threshold. Removing unrelated declarations from
the revised Challenge reduces it to 762 lines and 30,225 bytes: below the
32-KiB warning, but still above 300 lines. Readability remains a real review
question; no proofs were minified. The draft pair and `comparator-pattern.json`
now select the pattern theorem and its two supporting source claims. Their
local-check evidence is retained separately and is not a canonical protected
verification or editorial acceptance. Inspect readability and semantic integrity independently,
and change design or split claims if necessary. Do not assume that a compiling
Challenge proves a protected comparison succeeds.

The region directions now have separate self-contained draft Challenges, with
coverage and the unselected biconditional stated in `REGION-COMPARATOR.md`.
Each will require its own final protected checks and review; local experimental
comparison is not a release pass.

A separate source-inference draft selects the fixed-context agreement theorem
and Proposition 10's active-determined equality, root path, unique-solution
extrema and distinct active-root consequences. Its standalone Challenge is
264 lines, below the 300-line warning. It does not cover the other paper
families. It still requires exact-source protected checks and review.

Proposed configurations, subject to size and dependency measurements on final
bytes: (A) exact relevant pattern theorem; (B) attainable regions and fixed-
context SOME/ALL; (C) all-context synthesis and well-foundedness; (D) shared
and labelled spine including hard link interventions; (E) copy-majority and
source/groundedness. Each must name precisely its theorem and protected
definition surface and honestly list claims not in that configuration. A
single Palomar entry corresponds to one config and exact commit, not the entire
manuscript. If a proof-filled Challenge exceeds limits or is unreadable, do not
silently omit principal claims, import non-permitted project helpers, weaken
proof checks, or bypass the no-hole requirement. Revisit package design and
report the actual limitation. One repository snapshot is capped at 500 MiB;
all submitted regular Lean files must meet module/header and line constraints,
not merely the selected package. Recheck current rules and toolchain at handoff.

For a candidate exact commit: independently review the entire final source,
paper crosswalk, theorem/definition meanings, allowed closure, provenance,
license/attribution and honest AI disclosure. Run complete package-native clean
builds and all declared semantic entrypoints, transitive axiom audits,
protected Comparator with definition-value and altered-definition negative
controls, all required independent kernels, imported-definition/source
provenance, and root `python3 scripts/local_validate.py catalog` on the final
commit. Then run the pinned canonical `scripts/local_canonical.py full` and
`render` locally with authenticated pipeline/tools, supported confinement and
capacity profile, the exact commit and external evidence. Review every report
and rendered artifact, including visual inspection, and run the release-packet
guard and independent final source/evidence review. Hash source, config, tools,
logs, reports and rendered artifacts; preserve failed runs and establish
post-merge tree equality separately. The shared lock and bounded scheduler apply
to all heavy validation. Never replace missing tools, sandbox controls, source
hashes, negative controls or independent kernels with a Lake pass.

As of this planning check, `python3` was found on the non-root Linux PATH;
`which` did not find `bwrap`, `ruby`, `licensee`, `comparator`, `nanoda`, or
`landrun`, and a shallow search did not identify an authenticated canonical
pipeline checkout. Subsequently a non-setuid bubblewrap 0.12.0 was built in an
isolated workspace from the upstream tag (whose signature GitHub reports as valid)
and passed a local smoke test;
the Lean toolchain includes `nanoda_bin` and other checkers. These observations
do not authenticate the canonical pipeline or its required independent tool
pins. Verify availability and pins before attempting the canonical wrappers. No security
settings or hosted CI may be changed to resolve a missing requirement. If the
current external protocol requires a hosted receipt, local-only policy creates
an intake blocker; report it rather than launch author-hosted jobs. Palomar
admission, automated review and registration remain separate from local checks
and are delegated to the designated registry owner.

The installed Lake sandbox implementation was inspected independently: it
read-only binds the host root and masks several sensitive Linux paths, but the
review did not establish that Windows-mounted drives under `/mnt/c` and `/mnt/q` are masked. Treat the local sandbox run as a proof-check experiment on this
owned source, not a verified confidentiality boundary or a replacement for
the canonical hardened profile. Do not run untrusted source under that profile
until its full isolation is independently established.
