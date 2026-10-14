# Reusable definition correspondence

`HasSigmaLocallyFiniteBasis X` is exactly an existential `B : ℕ → Set (Set X)`
whose union is a Mathlib `IsTopologicalBasis`, with each subtype-indexed layer
locally finite under Mathlib `LocallyFinite`. The basis predicate ensures every
member is open and supplies the neighborhood refinement property. No condition
on the cardinality of a layer occurs. The expanded main theorem exposes this
formula directly, making the definition independently inspectable.

`basisShrinkLayer B U n` is the union of the members V of layer n with
`closure V ⊆ U`. Local finiteness makes the closure of this union the union of
the closures. Regularity ensures these layers jointly cover open U. This
countable cover is not asserted to be increasing.

`compatibleMetric h` applies Mathlib's generic compatible-metric extraction
after proving the substantive metrizability theorem from h. Its topology is
definitionally the original topology; `compatibleMetric_topology` certifies
that equality. This is a construction, not a new hypothesis in the criterion.

The coordinate theorem uses Mathlib `Function.support`, `C(X, ℝ)`, bounded
continuous functions and their existing uniform metric. The proof uses an
arbitrary index type with a discrete topology, without countability. The full
criterion constructs the necessary coordinates rather than assuming them.
