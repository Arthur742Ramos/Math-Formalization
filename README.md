# Math-Formalization

Independent Lean formalizations, organized by subject and target. Each package
owns its toolchain, Lake configuration, lockfile, Challenge, Comparator metadata,
definition evidence and verification scripts. Run build commands from its
directory; preserve each package's pins.

The [project catalog](PROJECTS.md) lists 17 audited developments, one source-account correction, and exact
source snapshots. The [repository readiness audit](READINESS.md) reconciles
their mechanical checks, public registration evidence and remaining obligations.
All 17 audited package trees match successful full canonical runs. Ten official
registrations are evidenced by the saved 2026-10-17 revision 332 public snapshot;
two more are user-reported with unconfirmed IDs. All three previously missing
rendering checks passed, and the separately authorized Sorgenfrey metadata
correction passed affected verification and merged. Sigma’s verification-status
correction now has a new exact-source full pass; rendering for that corrected
metadata snapshot remains unestablished. All proof files, Comparator contracts,
package pins and registered snapshots are preserved. The other sixteen package
trees are unchanged from the Sigma correction’s base.
See the audit for exact sources and run links.
The separately listed [collectionwise expansion package](topology/collectionwise-normal)
has completed full and rendering receipts for its original source. Its metadata,
README and linked status records now describe those passes explicitly. The
corrected source requires its own exact-source report before verified intake
handoff; proof equality alone does not transfer that result. [PREPARATIONS.json](PREPARATIONS.json)
binds both snapshots. [RELEASE-HANDOFFS.json](RELEASE-HANDOFFS.json) records the
prospective-packet audit and blocks stale sources from a new handoff. Earlier
no-intake notes describe their observation time and actor, not all later user actions.

Fresh global registry reads returned HTTP403 on 2026-10-18. Public snapshot absence
does not establish absence of private submissions. Mechanical success and
internal AI review do not establish Palomar editorial approval. Existing
registrations are bound to their exact versions and source commits in
[REGISTRATIONS.json](REGISTRATIONS.json); the audit is machine-readable in
[READINESS.json](READINESS.json).

Historical pending-status notes in immutable source snapshots predate subsequent
verification or registration. In particular, AU's source at
`8ff5eedba962cb74050fe6d5f0acd934ba830fc5` predates registration
[PALOMAR-2026-10-16-000021 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-16-000021&version=1).
The registered snapshot is unchanged. Later reports qualify preparation notes
for registered historical snapshots. For a new prospective handoff, correct
contradictory status claims inside the actual proposed source first.

Check catalog bindings, saved readiness evidence and package consistency with:

```sh
python3 scripts/check_catalog.py --package-checks
```

Use `--online` only when public-record access is available. These checks preserve
and reconcile evidence; they do not rerun Lean or certify a new registry review.
The existing catalog workflow performs these checks and public record binding.

Project code uses the [Apache-2.0 license](LICENSE). Retained upstream sources
preserve their attribution and license headers. Existing standalone repositories
remain available. Authorship, maintenance, material AI contributions and review
limits are recorded separately in each package.
