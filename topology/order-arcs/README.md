# Order arcs between subcontinua

Let `X` be a compact metric space and let `A ⊊ B` be nonempty compact connected subsets. There is a continuous embedding of the real unit interval into the hyperspace of nonempty compact subsets of `X`, starting at `A`, ending at `B`, with connected values and strict increase under inclusion. The ambient space need not be connected or locally connected.

The selected theorem is `OrderArcs.exists_order_arc` in [Solution.lean](Solution.lean). [Challenge.lean](Challenge.lean) states it independently using Mathlib’s literal sets, topology, and inclusion order. The single Challenge theorem hole is intentional. The Solution and all support proofs have no holes or additional axioms.

This is the connected-endpoint consequence of J. L. Kelley’s segment criterion and preservation of connected values in [*Hyperspaces of a continuum*, Lemmas 2.3 and 2.6](https://www.ams.org/tran/1942-052-01/S0002-9947-1942-0006505-8/). The target is useful in continuum theory and the topology of hyperspaces. Limited searches of Mathlib and several other formal libraries found no matching result; those searches do not establish priority or absence from every library.

The construction uses a compact maximal inclusion chain. Boundary bumping first proves that any strict pair of subcontinua has an intermediate subcontinuum. A dense sequence gives distance-to-set coordinates, whose negative weighted sum is continuous and strictly increases with inclusion. Connected values and inclusion are closed conditions in the hyperspace. The maximal chain is therefore compact. A missing value in its scalar image would give adjacent chain elements with an insertable intermediate continuum, contradicting maximality. The scalar identifies the chain with a real interval, and its inverse supplies the required parametrization.

| Module | Role |
| --- | --- |
| `Boundary` | Attributed standalone boundary-bumping dependency |
| `Checkpoint` | Strict interpolation and a strict distance coordinate |
| `Scalar` | Uniformly summable distance scalar, continuity, strict increase |
| `Hyperspace` | Closed connected values, closed inclusion, closure of chains |
| `Chain` | Compact maximal chain and its full scalar interval image |
| `Parameter` | Homeomorphic interval parametrization of the chain |
| `Solution` | The order-arc theorem with its exact endpoints |

The scalar is not normalized on singleton sets, and this development does not establish a general theory of Whitney maps. Strict inclusion is essential: strict increase separates the endpoint values. A singleton ambient space admits no strict pair. [The semantic audit](scripts/SemanticAudit.lean) checks both facts in Lean.

This folder has independent pins and a Lake lockfile: Lean `v4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. From this folder:

```sh
python3 scripts/verify.py --lake-build --output .lake/verification.json
python3 scripts/check_definitions.py --compare-mathlib --self-test
```

The first command obtains the pinned Mathlib cache, performs an ordinary Lake build, recompiles all proof modules into a fresh temporary directory, compiles a renamed Challenge with dependency-only imports, compares raw declaration types, universes and definition values, and checks transitive axioms. The second verifies the complete pinned [definition dossier](DEFINITIONS.md) and its rejection controls. [VERIFICATION.md](VERIFICATION.md) records the completed local checks and remaining independent checks.

`Boundary.lean` retains the standalone [boundary-bumping source](https://github.com/Arthur742Ramos/boundary-bumping-lean/tree/58831416a12f73312ac01cdaec19c060a6d4b142), with its authorship header. [reuse.json](reuse.json) records the exact source and newline changes. The other mathematical proof modules were authored for this target. Verification scripts adapt the prior owned packaging infrastructure; no composants proof is imported. Mathlib snapshots retain their original headers and upstream Apache license. Project code is covered by the repository’s [Apache-2.0 license](../../LICENSE).

The public verification summary omits local machine paths. Exact commands, outputs, failed attempts, resource receipts, and cleanup records remain in private task evidence. Humanizer was applied to reader-facing prose. The public order-arcs commit `6225330b17f15735eb6e2b90fdd0a0f1dc712e1e` passed the [ordinary-build workflow](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/37519884539) and the [Palomar full preflight](https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/37519885829). Independent human mathematical review and registry acceptance are not established by those runs. These runs verify only order-arcs at that commit and do not verify the new hyperspace-components application.
