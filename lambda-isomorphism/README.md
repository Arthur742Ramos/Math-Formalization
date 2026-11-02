# Effective isomorphism from one-one equivalence

For arbitrary predicates on natural numbers, mutually injective computable reductions yield computable inverse maps preserving membership. A corollary states the result as a computable permutation with computable inverse under Mathlib's `OneOneEquiv`.

The construction forms finite matching stages that keep prior edges, preserve membership and cover each natural number on each side. It formalizes the forward direction of the classical Myhill isomorphism theorem, as stated in Andrew Marks, *Computability theory*, Theorem 5.7. It does not assert a lambda-specific isomorphism without separately supplied effective encodings and reductions.

`LambdaIsomorphismChallenge.lean` contains two isolated theorem holes for comparison; `LambdaIsomorphismSolution.lean` imports the proved `LambdaTuring.FiniteOrbit` and does not import Challenge. Computability and one-one reducibility are the pinned Mathlib definitions. Standard Lean axioms reported for the main results are `propext`, `Classical.choice`, and `Quot.sound`.

The source theorem checkpoint received independent mathematical review. This package still requires integrated review, protected comparison and hosted verification. There is no claim of an executable extractor from arbitrary computability proofs or a practical runtime bound.
