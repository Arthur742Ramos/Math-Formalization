# Three outcomes of deterministic normal-order observation

For arbitrary untyped lambda terms, deterministic full-beta normal-order evaluation defines a partial-recursive `Part (Option Nat)` observer. A result `some n` means the term reaches Church numeral `n`; a defined `none` means it reaches a nonnumerical beta-normal form. An undefined observer means that no beta-normal form is reachable. The last statement concerns normalizability and the chosen normal-order strategy; it does not say every beta-reduction sequence diverges.

Bounded execution and observation are primitive recursive. The explicit-eliminator numeral recognizer is proved equal to the inherited Church decoder. The eta expansion `λf. λx. λz. x z` is a nonnumerical normal form, while Ω has no normal form. The exact numeral observer differs from an operational zero test: the preceding local CPS experiment shows the eta-expanded zero passes such a test without reaching a syntactic Church numeral.

The inherited standardization proof adapts Stefan Berghofer's Isabelle/HOL development, crediting Matthes and Loader. Challenge fixes the term model, normal-order runner, Church recognizer and observer; its isolated theorem holes are not imported by Solution. Independent source and integrated review and hosted preflight are pending.
