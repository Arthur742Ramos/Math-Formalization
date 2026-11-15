# Validation status

The selected declarations and their exact statements appear in
`Challenge.lean` and `comparator.json`; their implementations are
exported by `Solution.lean` from `ErdosOverlap/VerifiedBound.lean`.
The pinned environment is recorded in `lean-toolchain` and
`lake-manifest.json`.

An earlier ordinary Lean run is recorded in
`reviews/full_verification/kernel_verification.json` with SHA-256
`a67bbf17b68218b0151e8c164563bc60448e4d225f5344795f29af6f5908955d`.
Its recorded mathematical source and toolchain hashes match this snapshot.
The corresponding axiom output is
`reviews/full_verification/AuditNumeric.log`.

The following quick checks compare the historical receipt with its recorded
source and log hashes, compare the two statement surfaces as text, and check
small finite instances. They do not run Lean or Palomar Comparator.

```sh
python3 scripts/check_historical_receipt.py
python3 scripts/audit_surface.py
```

The earlier protected Comparator attempt did not reach verification because
its Linux sandbox could not create a NETLINK_ROUTE socket. Its log and receipt
are included under `reviews/full_verification`. An ordinary Lean build
does not establish Comparator or NanoDa success.

The current monorepo requires local native verification, the pinned canonical
full verifier and Challenge renderer, and independent source-fidelity and
patch review before merge. Its hosted workflows are retired. See the
[monorepo validation policy](https://github.com/Arthur742Ramos/Math-Formalization/blob/main/LOCAL-VALIDATION.md)
for the required controls and evidence; a source-hash or text audit is not a
replacement for them.

There is also a packaging blocker for Palomar from the monorepo's main tree:
`formalization.yaml` declares BSD-3-Clause and this package carries that
license, while the repository-root `LICENSE` is Apache-2.0. The current
Palomar source contract requires an exact match with the single root license.
Do not relabel or relicense the package merely to pass that check. A
separately identified BSD-licensed standalone commit can retain the package
files and its license, but would need its own exact-source verification,
rendering and review. It must not be merged as a replacement for the monorepo.

The earlier Comparator attempt was made in another environment. No fresh
protected Comparator, NanoDa, canonical full or rendering pass is claimed
for the monorepo package or a standalone commit. A successful local preflight
is not Palomar intake, editorial acceptance, or registration.
