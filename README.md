# Math-Formalization

Independent Lean formalizations, organized by subject and target. Each package
owns its toolchain, Lake configuration, lockfile, Challenge, Comparator metadata,
definition evidence and verification scripts. Run build commands from its
directory; preserve each package's pins.

The [project catalog](PROJECTS.md) lists all 17 topology developments and exact
source snapshots. The [repository readiness audit](READINESS.md) reconciles
their mechanical checks, public registration evidence and remaining obligations.
All 17 current package trees match successful full canonical runs. Ten official
registrations are evidenced by the saved 2026-10-17 revision 332 public snapshot;
two more are user-reported with unconfirmed IDs. All three previously missing
rendering checks passed, and the separately authorized Sorgenfrey metadata
correction passed affected verification and merged. All proof files and pins,
all registered snapshots and the other sixteen complete packages are unchanged.
See the audit for exact sources and run links.

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
for Sneider and the other verified packages in the same way.

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
