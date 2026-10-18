# Math-Formalization

Independent Lean formalizations, organized by subject and target. Each target
owns its toolchain, Lake configuration and lockfile, Challenge, Comparator
metadata, definition evidence and verification scripts. Run build commands from
the target directory. Targets can evolve their versions independently.

The [project catalog](PROJECTS.md) lists all 17 topology projects, their scope,
public Palomar status and source snapshots. The complete official repository
index checked at16:04UTC on2026-10-17 contained10 registrations, including Alexandroff–Urysohn
as [PALOMAR-2026-10-16-000021 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-16-000021&version=1)
and Sneider as [PALOMAR-2026-10-17-000003 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-17-000003&version=1).
The public registry-wide audit refreshed at 16:05 UTC on 2026-10-17 covers
598 active entries at revision 332, across 24 consistent bounded pages.
No public registration was found for hyperspace components, Sorgenfrey,
Whitney or the countable-network project in that snapshot. The user
reported countable-network registration underway at2026-10-17T13:11:26Z and
clarified at18:31UTC that the countable-network result was registered. This is
a user report; its official ID remains unconfirmed. The last independently
checked16:04UTC index lacked the entry. The19:08UTC public-results read returned
HTTP403, so no newer public status is inferred. These observations do not
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
and review evidence. At18:31UTC Arthur clarified that the reported registration
was this countable-network result. Its official ID remains unconfirmed; the
last independently checked index was16:04UTC and later public-results access
returned403. The catalog therefore retains registration pending for public
record confirmation, without inventing an ID.

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
development stage. Independent semantic review of the16:05UTC598-entry public
audit at revision 332 found no equivalent target. This does not establish
absence of private attempts or unregistered work. Public-data access worked
through the ordinary route at16:04–16:05UTC; submission-protocol access returned
HTTP403 at16:05UTC and the later19:08UTC public-results read returned403.
No intake was performed by this task; editorial outcomes and registration
were not independently verified. The later22:21UTC user report is qualified below.

The [countable-density Hewitt–Marczewski–Pondiczery development](topology/hewitt-marczewski-pondiczery)
proves continuum-index separability and the sharp Boolean-cube criterion.
Its source snapshot and verification limits are recorded in [PROJECTS.md](PROJECTS.md).
At19:01UTC, PR17 was a separate pending manual submission. This development
does not itself establish an intake outcome or rejection; the later22:21UTC
registration report is recorded below without inventing an official ID.

The HMP package’s [full canonical verification](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39074862893) and
[Challenge rendering](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39074862730) passed for exact source
`cd7ae6bc5f4a1e5569cbbe1a883b83e92eb07a0e`; protected comparison and independent
kernels accepted all seven theorems and the literal row definition. The source
package, prior fifteen package trees and dependency pins remain unchanged.
The immutable preparation notes predate these results. Existing-record catalog
checks and the dated complete duplicate audit are separate evidence; current
global clearance is unresolved before any intake.

Arthur reported at22:21UTC that the previous countable-coordinate result
(PR17) registered. Its official ID remains unconfirmed and no intake is
repeated. See the dated report history in REGISTRATIONS.json; this report
does not establish an independently verified public registration.

The separate [Sigma-product sequential-closure development](topology/sigma-product-frechet)
proves that countable-support products of first-countable pointed spaces are
Frechet–Urysohn, using an adaptive finite-coordinate sequence construction.
Its T1 closure companions explain the failure of sequentiality in uncountable
ordinary Boolean cubes. See PROJECTS.md for the exact source, attribution and
verification limits. Its [canonical full verification](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39083465938)
and [Challenge rendering](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39083465499)
passed on their first attempts for exact source
`10f8b9075144c51468729b9b620c46b739c0a680`. Protected comparison and independent
kernels accepted all eight theorems and both literal definitions; the renderer
built and sanitized all ten selected declaration surfaces. The package and all
sixteen prior package trees are unchanged. Pending-canonical notes inside the
immutable preparation snapshot predate these results and are qualified here.
Current registry/attempt/protocol/proof-capability gates remain unresolved;
no intake, editorial outcome or registration is claimed. HMP is not resubmitted.
