# Scope and source audit

Dowker, *On countably paracompact spaces*, Canadian Journal of Mathematics 3
(1951), 219–224, DOI 10.4153/CJM-1951-026-2, is the primary source.
The selected target is Theorem 4, with Theorem 2's decreasing closed sequence
criterion and Lemma 3's compact metric product theorem as companions.

The definition of normality in the source requires separation of disjoint closed
sets, without a T1 condition. Mathlib `NormalSpace` matches that convention.
`Dowker.CountablyParacompact` uses ordinary countable open-cover refinements;
`countablyParacompact_iff_nat_precise` proves the indexed version and includes
empty covers. `Dowker.StrictInsertion` quantifies arbitrary functions to the
ordinary real numbers and requires pointwise strict inequality. Its bounds can
be unbounded and their gap can tend to zero.

The implementation changes proof organization while retaining these statements.
Strict insertion is constructed with a locally finite partition of unity over
rational levels. The interval-product converse places decreasing closed sets
at positive reciprocal singleton levels tending to zero. The forward compact
product proof separates compact fibers using finite unions from a countable
basis and locally finite shrinking. It proves the compact regular second-countable
case and specializes it to every compact metrizable factor.

Pinned Mathlib supplies shrinking, partitions of unity, closed compact projections,
semicontinuity and countable bases. The local search found no existing countable
paracompactness/Dowker characterization theorem in the pinned topology sources.
This is a scoped overlap audit, not a claim of first-ever formalization.

Hart's course notes on Dowker spaces explain the normal-product problem and the
homotopy-extension connection. The target addresses a classical obstruction
and an exact covering/function-insertion equivalence of interest to general
topologists; it is not a routine consequence of the earlier Sorgenfrey package.

The project preserves the Michael registered entry and all other packages.
No Monotone–Light AFP submission or Poincaré change belongs to this target.
