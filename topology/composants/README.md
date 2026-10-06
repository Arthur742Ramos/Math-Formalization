# Alexandroff property of metric indecomposable continua

This project proves [Todorov–Valov Theorem 3.3](https://www.jstage.jst.go.jp/article/qagt/30/2/30_93/_pdf/-char/en):
for disjoint closed sets with nonempty interiors in a metric indecomposable continuum,
one open cover prevents every partition between those sets from admitting an
ω-map onto a continuum. An ω-map is a continuous map whose inverse images of
some open target cover refine the ambient cover on the partition.

The cover depends on the two closed sets. It works for every partition and every
nonempty compact connected Hausdorff target, including targets in another universe.
The target need not be metrizable. Singleton ambient spaces satisfy the theorem
vacuously because the two massive disjoint sets cannot exist.

`Foundations.lean` retains the eight classical composant results from the published
baseline. `Alexandroff.lean` proves the new result: shrinking-fiber maps would yield
a connected compact limit of separators; a different dense composant provides a
compact connected bridge avoiding that proper limit. The bridge contradicts
separation. Metric balls then give the required open cover.

`Solution.lean` exports the proof. `Challenge.lean` independently states the same
nine results and seven project predicates, importing only pinned dependencies.
The Challenge contains nine intentional theorem holes. Proof modules contain none.

From this directory:

```sh
lake exe cache get
lake build --wfail
python scripts/check_definitions.py --compare-mathlib --self-test
python scripts/verify.py
```

See [DEFINITIONS.md](DEFINITIONS.md) for complete definition bodies and pinned
source identities, [PROVENANCE.md](PROVENANCE.md) for retained source credits,
and [VERIFICATION.md](VERIFICATION.md) for author checks and their limits.
