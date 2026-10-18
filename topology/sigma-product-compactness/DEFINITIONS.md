# Literal definitions

All selected definitions are public and exposed in both independent entrypoints.

```lean
def OmegaBounded (Y : Type w) [TopologicalSpace Y] : Prop :=
  ∀ s : Set Y, s.Countable → IsCompact (closure s)

def deviationSupport (b x : ∀ i, X i) : Set ι := {i | x i ≠ b i}

def activeCoordinates (b : ∀ i, X i) : Set ι :=
  {i | ∃ x : X i, x ≠ b i}
```

The auxiliary `SigmaProduct b` is the subtype of product points with countable
deviation support, carrying the inherited ordinary product topology. The index
and factor universes are independent; the explicit basepoint is a premise.

No first countability, nonempty support, countable-index assumption, or finite
support substitution is hidden in these definitions.
