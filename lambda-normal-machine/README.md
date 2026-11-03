# A finite-machine observer for lambda normal forms

For every untyped de Bruijn term `t`, one explicitly constructed finite machine takes `directTermNumber t` as input. It outputs `n + 1` exactly when `t` reaches Church numeral `n`, outputs zero exactly when `t` reaches a nonnumerical beta-normal form, and never reaches a halting configuration exactly when `t` has no reachable beta-normal form. Every reached halt has a valid numerical output.

The theorem covers open as well as closed terms. It makes no claim about other term encodings, malformed numeric inputs, or practical machine size. A failed numerical observation alone does not mean nontermination: it can be a nonnumerical normal form. Challenge fixes the term and machine models and the direct input encoding. Its single theorem hole is a comparison obligation and is absent from the Solution proof closure.

The source builds on the public lambda/Turing and normal-order observer developments and the classical standardization work credited in the metadata. Earlier mechanized computability work includes Norrish’s HOL4 formalization and Forster and coauthors’ Coq weak-call-by-value development. Integrated validation, independent package review, and hosted checks are pending.
