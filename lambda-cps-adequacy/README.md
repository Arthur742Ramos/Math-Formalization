# Weak call-by-name to call-by-value CPS adequacy

For every closed de Bruijn lambda term, weak call-by-name reaches an abstraction exactly when the concrete CPS translation, applied to the identity continuation, reaches an abstraction under deterministic weak left-to-right call-by-value. The proof gives exact translated-body readback. It includes a closed term that terminates by call-by-name and through the CPS translation but loops under direct call-by-value.

The weak relations do not reduce under abstractions. Open source terms may be stuck and are outside the adequacy equivalence. This result does not claim contextual equivalence, Church-numeral readback, full beta-normalization correspondence, or a complexity bound.

The classical reference is Gordon Plotkin, “Call-by-name, call-by-value and the lambda-calculus” (1975). The challenge fixes the source and target strategies, value notion, translation and continuation; its isolated theorem holes are not imported by Solution. The source checkpoint passed targeted independent mathematical review; integrated package review and hosted preflight are pending.
