# Math-Formalization

Independent Lean formalizations, organized by subject and target. Each target
owns its toolchain, Lake configuration and lockfile, Challenge, Comparator
metadata, definition evidence and verification scripts. Run build commands from
the target directory. Targets can evolve their versions independently.

The [project catalog](PROJECTS.md) lists all 13 topology projects, their scope,
public Palomar status and original source snapshots. At registry revision
315 on 2026-10-16, 8 projects have confirmed public registrations:
Alexandroff/composant foundations, order arcs, Michael's biquotient theorems,
Dowker's characterization, perfect surjections, Nagata-Smirnov metrization and
Smirnov local-to-global metrization, and perfect images of metrizable spaces.
No public registration was found for the hyperspace, Sorgenfrey, Whitney or
Alexandroff–Urysohn developments in that snapshot. The new Sneider diagonal
development is a proof-verified draft with attribution and canonical protected
verification gates outstanding; no public registration is claimed.

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
