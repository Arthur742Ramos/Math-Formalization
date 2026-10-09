# Math-Formalization

Independent Lean formalizations, organized by subject and target. Each target
owns its toolchain, Lake configuration and lock, Challenge, Comparator metadata,
definition evidence, and verification scripts. Run build commands from the
target directory. Targets can evolve their versions independently.

Current topology targets are [the Alexandroff property of metric indecomposable continua](topology/composants),
[order arcs between subcontinua](topology/order-arcs),
[path components of punctured continuum hyperspaces](topology/hyperspace-components), and
[Sorgenfrey covering theorems](topology/sorgenfrey-covering). The Alexandroff project
includes eight classical composant results as foundations. A separate package covers
[Michael's biquotient-map product and characterization theorems](topology/michael-biquotient).
See [PROJECTS.md](PROJECTS.md)
for the project index. Existing standalone repositories remain available.

Project code uses the [Apache-2.0 license](LICENSE). Retained upstream sources
preserve their attribution and license headers.
