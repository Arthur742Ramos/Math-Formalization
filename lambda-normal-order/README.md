# Full beta normal-order normalization

The deterministic leftmost-outermost full-beta strategy reaches a beta-normal form whenever one is reachable. The theorem applies to all untyped de Bruijn terms, including open terms. The strategy stops exactly when a full beta-normal form exists; otherwise it has a next step at every finite stage. The one-step selector is primitive recursive, and normal forms reached are unique.

The strategy descends under binders and reduces the function before the argument when no root redex exists. These statements do not say that every beta strategy terminates; weak-head normality, absence of a Church-numeral result, and full beta-normality are distinct.

The proof builds on the inherited full-beta semantics and standard reduction, adapted from Stefan Berghofer’s Isabelle/HOL standardization development, which credits Ralph Matthes and Ralph Loader. `LambdaNormalOrderChallenge.lean` fixes the model, beta-step enumeration and strategy with isolated theorem obligations. `LambdaNormalOrderSolution.lean` imports the proof without importing Challenge. Targeted independent mathematical review of the source passed; integrated package review and hosted verification remain pending.
