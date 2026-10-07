# Path components of punctured continuum hyperspaces

Let X be a compact metric indecomposable continuum with at least two points. Its punctured continuum hyperspace consists of the nonempty compact connected subsets other than X, with the induced Vietoris topology. Two of its points are joined by a path exactly when the corresponding subsets lie in the same composant of X. This hyperspace has uncountably many path components.

[Solution.lean](Solution.lean) proves this using Mathlib's literal `Joined` and `pathComponent`. For any point x of A, `pathComponent A` is exactly the proper subcontinua contained in the composant of x. The classification itself needs compactness, a metric, and indecomposability; the uncountability theorem also needs connectedness and at least two points. [Challenge.lean](Challenge.lean) states six selected results independently with the same literal definitions. Its six theorem holes are intentional. Every Solution and support proof is complete.

The cited source is [Nadler and Pellicer-Covarrubias, *Hyperspaces with exactly two orbits*, section 2.7](https://hrcak.srce.hr/en/file/5558), specialized to Y = X. The paper states an arc-component result. The formalization proves the path formulation directly.

The difficult direction starts with a hyperspace path and takes the union of all its values. [PathUnion.lean](PathUnion.lean) proves that this is a proper subcontinuum. For each omitted point, the times whose continua omit it form an open set by the upper Vietoris topology. A finite interval subdivision subordinate to this cover gives proper segment unions. Indecomposability prevents the connected union of two overlapping proper subcontinua from filling X. Induction then proves that the entire path union stays proper. Running unions can have plateaus; the proof does not require strict increase.

For the converse, two continua in one composant lie in a common proper subcontinuum. The retained order-arc construction joins each to that common continuum. The uncountability proof maps singletons to hyperspace path components and uses the retained theorem that X has uncountably many composants. In a subsingleton ambient space the punctured hyperspace is empty.

| Module | Role |
| --- | --- |
| `Boundary`, `Interior`, `Foundations` | Attributed composant foundations |
| `Checkpoint`, `Scalar`, `Hyperspace`, `Chain`, `Parameter`, `OrderArc` | Retained order-arc construction |
| `PathUnion` | Proper union of a hyperspace path |
| `Solution` | Path classification, uncountability, subsingleton edge |

This folder has its own pins and lockfile: Lean `v4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. From this folder:

```sh
python3 scripts/verify.py --lake-build --output .lake/verification.json
python3 scripts/check_definitions.py --compare-mathlib --self-test
```

The first command builds the pinned project, recompiles every proof module into a fresh temporary directory, checks a renamed Challenge with dependency-only imports, compares raw types, universes and five definition values, and audits transitive axioms. The second checks the complete [definition dossier](DEFINITIONS.md), including declaration tails and rejection controls. [VERIFICATION.md](VERIFICATION.md) records the completed author checks and independent mathematical and Lean source review, with native YAML validation and hosted checks left to the coordinating lane.

[PROVENANCE.md](PROVENANCE.md) and [reuse.json](reuse.json) record the retained sources and licenses. Project code uses the repository's [Apache-2.0 license](../../LICENSE). Humanizer was applied to reader-facing prose. Exact local commands, attempts, resource limits and cleanup receipts remain in private evidence.
