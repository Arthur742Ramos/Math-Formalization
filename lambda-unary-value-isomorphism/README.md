# Value-preserving unary code–lambda isomorphism

There are total computable maps `F` from Mathlib partial-recursive codes to untyped lambda terms and `G` from terms to codes. Every `F` output is closed; `G (F c) = c` for every code; and `F (G t) = t` for every closed term. For every code and numerical input, the partial numerical function observed from `F c` equals the recursive code's evaluation at that input.

The companion theorem states exact membership and no-numerical-result correspondence under full beta reduction. It does not equate no numerical result with divergence. The reverse map is total on open terms, but its inverse law is stated only for closed terms. The result concerns Mathlib recursive-code syntax, not arbitrary conventional Turing-machine syntax; it does not assert an executable extractor from arbitrary computability proofs.

The construction uses injective code and lambda padding, a fixed uniform lambda evaluator code, and an equality-labelled effective back-and-forth. It formalizes a classical acceptable-numbering isomorphism argument; see Andrew Marks, *Computability theory*, Theorem 6.11.

`LambdaUnaryValueChallenge.lean` fixes the term model, numerical observation and syntax coding, with two isolated theorem holes for comparison. `LambdaUnaryValueSolution.lean` imports the proved module and does not import Challenge. The source checkpoint passed independent mathematical review; integrated package review, protected comparison and hosted verification remain pending.
