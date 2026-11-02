# A computable bijection with closed lambda terms

There are total computable maps `F` from Mathlib partial-recursive-code/input pairs to untyped lambda terms and `G` in the reverse direction. Every `F` output is closed, `G (F p) = p` for every pair, and `F (G t) = t` for every closed term. Evaluation of `p` is defined exactly when `F p` applied to Church zero reaches Church zero under full beta reduction.

The construction effectively enumerates canonical codes of all closed terms and applies the preceding classical Myhill effective-isomorphism theorem. It does not assert equality of computed numerical functions, an arbitrary Turing-machine syntax translator, or an inverse law for open terms. Absence of a numerical observation is not equated with divergence.

`LambdaClosedBijectionChallenge.lean` fixes the term model, numerical observation and syntax coding, with one isolated theorem hole for comparison. `LambdaClosedBijectionSolution.lean` imports the proved module and does not import Challenge. Standard Lean axioms reported are `propext`, `Classical.choice`, and `Quot.sound`. The proof source passed independent mathematical review; this package awaits integrated review, protected comparison and hosted verification.
