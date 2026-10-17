# Literal selected definitions

`SigmaFrechet.deviationSupport b x = {i | x i ≠ b i}`.

`SigmaFrechet.SigmaProduct b = {x : ∀ i, X i // (SigmaFrechet.deviationSupport b x).Countable}`.

Both definitions are topology-independent and use no axioms. The support is
relative to a supplied point in the product. It can be finite, countably
infinite or empty. The subtype admits only countable supports. Its topology
is the canonical subtype topology of the ordinary product; no replacement
topology is installed. The support predicate is exposed across module
imports, and the subtype is a transparent abbreviation. Definition comparison
must check values as well as types; both values have independent `rfl` tests.
