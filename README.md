# Math-Formalization

Independent Lean formalizations, organized by subject and target. Each target
owns its toolchain, Lake configuration and lockfile, Challenge, Comparator
metadata, definition evidence and verification scripts. Run build commands from
the target directory. Targets can evolve their versions independently.

The [project catalog](PROJECTS.md) lists all 15 topology projects, their scope,
public Palomar status and source snapshots. The complete official repository
index checked on 2026-10-17 contains 10 registrations, including Alexandroff–Urysohn
as [PALOMAR-2026-10-16-000021 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-16-000021&version=1)
and Sneider as [PALOMAR-2026-10-17-000003 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000003&version=1).
The dated public registry-wide audit covers 596 active entries at revision 329.
No public registration was found for hyperspace components, Sorgenfrey,
Whitney or the countable-network project in that snapshot. The user later
reported countable-network registration underway at 2026-10-17T13:11:26Z.
A current public index request returned HTTP403, so that status is recorded
as registration pending without inferring a public ID. This does not
establish absence of private attempts or unregistered work.

Status statements inside immutable source snapshots describe the development
stage when those snapshots were created. In particular, AU's statements that
protected verification was outstanding and no submission had occurred predate
its later passing verification, submission and registration. The registered
snapshot remains unchanged; the dated official record establishes its current
registration status. The earlier nine-entry repository-index refresh is retained
as dated provenance alongside the newer public audit.

Sneider is registered as [PALOMAR-2026-10-17-000003 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000003&version=1).
Its [official record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-17-000003-v1.json)
confirms registration at 2026-10-17T05:08:01Z for exact source
`497432e5e02244f242cdfc8c0a43316de3aa5bdc`, with no review warnings. [PR14](https://github.com/Arthur742Ramos/Math-Formalization/pull/14)
merged the identical package tree. Its [passing canonical preflight](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/38975517426)
and [passing Challenge rendering](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/38975253426)
remain exact-source mechanical evidence; the later public record establishes
registration. Historical pending-status notes in the immutable source predate
those reports and registration. The registered package remains unchanged.

The [countable-network package](topology/compact-countable-network) proves the
compact Hausdorff countable-network metrization criterion and reusable network
transport and subspace results. Its [full canonical preflight](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39032757199)
and [Challenge rendering](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39032757099)
passed for exact source `47aaba112beb17b7c0ca68f56356c5c829ee154d`.
Independent source and implementation review and the dated public duplicate
audit found no blocking issue. The immutable source's earlier pending-gate
notes describe its preparation snapshot. These results establish mechanical
and review evidence. Its registration is now user-reported as underway; public
confirmation remains unavailable, so no registration or public ID is claimed.

The catalog links each registration to its verified ID, version and immutable
source commit. [REGISTRATIONS.json](REGISTRATIONS.json) provides the same records
in machine-readable form. Package source files retain their original provenance
and verification history. Existing standalone repositories remain available.

Check the catalog and its public record bindings with:

```sh
python3 scripts/check_catalog.py --online
```

This checks project-tree preservation, source ancestry, catalog links and public
registration records. Proof verification remains documented in each package.

Project code uses the [Apache-2.0 license](LICENSE). Retained upstream sources
preserve their attribution and license headers.

The [countable-coordinate factorization package](topology/countable-coordinate-factorization)
proves exact continuous factorization through countable subproducts of arbitrary
nonempty compact Hausdorff products, with a uniform-space bridge and product
metrizability consequences. Ordinary Lean verification and internal independent
AI review cover exact source `fc3f403c4d07356d2232e809f326f63a9ce9da45`.
Its [canonical full preflight](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39047061697) and
[Challenge rendering](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39047061497) passed on 2026-10-17 for that exact
source, with 13 selected theorems and the literal refill definition checked.
Comparator, NanoDa and con-ron accepted the protected Challenge/Solution pair;
the canonical renderer built and sanitized the selected declaration surfaces.
The source package is unchanged. Earlier preparation-status notes in its
immutable snapshot predate these completed checks; they describe that snapshot's
development stage. The public duplicate check remains dated to the saved
revision329 audit; current complete clearance is unavailable after HTTP403.
No intake, editorial acceptance or registration is claimed for this package.
