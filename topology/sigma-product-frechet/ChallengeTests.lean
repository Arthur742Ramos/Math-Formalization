module

import SigmaChallenge

open Set Filter Topology

#check SigmaFrechet.exists_sequence
#check SigmaFrechet.frechetUrysohnSpace
#check SigmaFrechet.countable_closure_support
#check SigmaFrechet.isSeqClosed_countableSupport
#check SigmaFrechet.countable_tightness
#check SigmaFrechet.subspace_frechetUrysohnSpace
#check SigmaFrechet.dense_countableSupport
#check SigmaFrechet.boolean_cube_not_sequential

example {ι : Type*} {X : ι → Type*} (b x : ∀ i, X i) :
    SigmaFrechet.deviationSupport b x = {i | x i ≠ b i} := rfl

example {ι : Type*} {X : ι → Type*} (b : ∀ i, X i) :
    SigmaFrechet.SigmaProduct b = {x : ∀ i, X i // {i | x i ≠ b i}.Countable} := rfl

example {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, FirstCountableTopology (X i)] (b : ∀ i, X i)
    {s : Set (SigmaFrechet.SigmaProduct b)} {x : SigmaFrechet.SigmaProduct b}
    (hx : x ∈ closure s) :
    ∃ a : ℕ → SigmaFrechet.SigmaProduct b, (∀ n, a n ∈ s) ∧
      Tendsto a atTop (𝓝 x) := SigmaFrechet.exists_sequence b hx
