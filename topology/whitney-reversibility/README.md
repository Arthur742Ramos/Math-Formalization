# Sequential strong Whitney reversibility of hereditary decomposability

Let X be a compact metric continuum and μ a Whitney map on its continuum hyperspace C(X). Suppose 0 < tₙ < μ(X), tₙ tends to zero, and every level μ⁻¹(tₙ) is hereditarily decomposable. Then X is hereditarily decomposable.

[Solution.lean](Solution.lean) proves E. Abo-Zeid's Theorem 2.2 in [*Some properties of Whitney continua*, Topology Proceedings 3 (1978), 301-312](https://topology.nipissingu.ca/tp/reprints/v03/tp03201.pdf). Its supporting Theorem 2.1 is proved in relative form: for every nondegenerate indecomposable subcontinuum Y and 0 < t < μ(Y), there is a nondegenerate indecomposable compact connected family S of continua K ⊆ Y with μ(K) = t and union S = Y. The result asserts the existence of such a family inside the level.

Whitney maps are literally continuous, zero on singleton sets, and strictly increasing under proper inclusion. Hereditary decomposability means that every nondegenerate subcontinuum decomposes into two proper subcontinua. The singleton restriction is part of the literal definition. The theorem quantifies over a genuine Whitney map, as the source does. This package does not construct a general Whitney map.

The new proof has three parts. [Levels.lean](Levels.lean) proves that each relative size level is compact and connected and covers Y. For two level members sharing a point, order arcs from that singleton give a two-parameter union family. A continuous monotone scalar on the square has connected vertical level fibers, and a compact quotient argument proves the square level connected. Connectedness of Y then rules out a separation of the whole relative level. The argument allows plateaus and constant order paths.

[Reduction.lean](Reduction.lean) proves that connected compact families covering Y form a closed hyperspace subset. The existing continuous strictly increasing height function attains a minimum there. Strict increase makes the minimizer minimal under inclusion. Decomposing this minimizer into two proper subcontinua would give a decomposition of Y by their unions. The height function is used solely for this minimization.

[Solution.lean](Solution.lean) applies the reduction and proves that the covering family is nondegenerate because t < μ(Y). For the sequential theorem, an indecomposable nondegenerate Y has μ(Y) > 0, so some positive tₙ is below μ(Y). Its indecomposable covering family contradicts hereditary decomposability of that level.

The size-level statement is classical infrastructure, documented in Alejandro Illanes's [*Size levels of hyperspaces*, Topology Proceedings 26 (2001-2002), 213-233, p. 214](https://topology.nipissingu.ca/tp/reprints/v26/tp26115.pdf). The selected application is Abo-Zeid's reversibility theorem. No mathematical novelty, priority, or editorial acceptance is claimed.

The independent [Challenge.lean](Challenge.lean) contains five selected statements and nine literal definitions. Its five theorem holes are intentional. Solution and every retained support proof contain no holes or extra axioms. The folder pins Lean `v4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
python3 scripts/verify.py --lake-build --output .lake/verification.json
python3 scripts/check_definitions.py --compare-mathlib --self-test
```

The verifier compiles all proof modules afresh, compiles a renamed Challenge with dependency-only imports, compares raw theorem types, universe parameters and literal definition values, and audits transitive axioms and semantic controls. [DEFINITIONS.md](DEFINITIONS.md) and its manifest retain complete upstream source snapshots and declaration ranges. [PROVENANCE.md](PROVENANCE.md) records retained proofs and licenses. Humanizer was applied to reader-facing prose. Publication, independent review and hosted preflight remain with the coordinating lane.
