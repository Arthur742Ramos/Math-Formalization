# Math-Formalization

Independent Lean formalizations, organized by subject and target. Each target
owns its toolchain, Lake configuration and lockfile, Challenge, Comparator
metadata, definition evidence and verification scripts. Run build commands from
the target directory. Targets can evolve their versions independently.

The [project catalog](PROJECTS.md) lists all 14 topology projects, their scope,
public Palomar status and source snapshots. The complete official repository
index checked on 2026-10-16 contained 9 registrations, including Alexandroff–Urysohn
as [PALOMAR-2026-10-16-000021 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-16-000021&version=1).
Its [official record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-16-000021-v1.json)
confirms registration at 2026-10-16T21:58:30Z for exact source
`8ff5eedba962cb74050fe6d5f0acd934ba830fc5`. No public registration was found for
hyperspace components, Sorgenfrey, Whitney or Sneider in that dated index.
Sneider’s later registration is recorded below; no newer complete index refresh
is claimed.

Status statements inside immutable source snapshots describe the development
stage when those snapshots were created. In particular, AU's statements that
protected verification was outstanding and no submission had occurred predate
its later passing verification, submission and registration. The registered
snapshot remains unchanged; the dated official record establishes its current
registration status. The catalog's earlier global-search revision is preserved
as historical provenance, separately from this per-repository refresh.

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
transport and subspace results. Its ordinary Lean verification is separate from
canonical preflight and rendering, which remain outstanding. Current registry
clearance is incomplete; this development has not been submitted.

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
