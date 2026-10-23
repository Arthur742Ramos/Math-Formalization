# Source correspondence and bounded overlap audit

The directly consulted source is Michael Francis, *Two Topological Uniqueness
Theorems for Spaces of Real Numbers*, arXiv:1210.1008v1,
https://arxiv.org/pdf/1210.1008v1 . Theorem 2 occurs on printed page 2;
its proof occurs on printed page 9. Downloaded PDF SHA256:
`cd7a764d023a930c4792545378732856fb73c76e2a9abe74a03cdd235ee28108`.

The source's convention makes countable mean countably infinite. Lean's
`Countable` is at most countable. Explicit `Nonempty X` together with
metrizability and `PerfectSpace X` excludes finite spaces and preserves the
intended scope. The statement concerns the topology supplied on `X`; `ℚ`
uses its existing real-induced topology, checked by a separate compiled
semantic equality. `nonempty_homeomorph` formalizes Theorem 2;
`nonempty_homeomorph_iff` adds its elementary necessary direction.

Francis derives zero-dimensionality and then uses a closure/Cantor-group
translation argument to remove problematic endpoints. This proof instead
constructs a full nonempty binary clopen scheme with scheduled basis decisions
and finite-point retention. Two-sided addresses permit a compatible dense
linear order without endpoints. Equality of the original and order topologies
is proved. This is an alternative proof of the same theorem, not a literal
transcription. The historical Sierpiński 1920 and Dasgupta 2005 references are
credited through Francis; their originals were not independently consulted.

## Audience and significance

Intrinsic recognition of countable metrizable spaces is useful to researchers
in general topology and descriptive set theory. Francis's Example 2 gives
concrete applications to countable dense Euclidean subspaces, rational finite
products and Cantor-set endpoints. The `ℚ × ℚ` application is independently
compiled here. This is a substantial classical recognition theorem and the
subject of a serious expository paper; a missing library lemma alone is not
the basis for its research scope. No novelty, editorial acceptance or priority
claim is made.

## Audit on 2026-10-23

The repository's branches and all 40 PRs were inspected through public GitHub
reads, together with the predecessor tree. No matching Sierpiński/rational
characterization project was found. Hodge and sparse-paper work were excluded
from modifications. The new package is isolated on its own branch and path.

Bounded searches at Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55` found the countable
completely-regular clopen-basis theorem, rational usual topology, lexicographic
orders and `Order.iso_of_countable_dense`. These are credited infrastructure;
they do not supply the topology-to-compatible-order construction proved here.
Searches for Sierpiński, rational homeomorphisms and countable/perfect metric
combinations found no equivalent general theorem. This is not an exhaustive
semantic equivalence audit or global first-formalization assertion.

The public recent registry JSON was inspected through the web source
https://data.palomar-registry.org/recent.json . Bounded searches for Sierpiński,
rationals and countable-metrizable descriptions found no matching entry. The
Cantor predecessor entry is publicly recorded as
`PALOMAR-2026-10-23-000001`, version 1, at the source commit above. The
registry-wide result API and direct versioned JSON requests were inaccessible
(HTTP 403 or web retrieval errors). Failed requests do not establish absence;
no exhaustive registry-wide duplicate clearance is claimed. Private entries
were not inspected and no new intake was attempted.
