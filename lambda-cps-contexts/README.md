# CPS adequacy for translated one-hole contexts

For a closed lambda term placed in a source context built from abstraction and either application side, the explicitly translated target context commutes exactly with plugging. Context-fixed terms may be open when bound by surrounding context binders, provided the whole source program is closed. Weak call-by-name value convergence then agrees with weak call-by-value convergence under the translated target test, with exact translated-value readback.

For closed programs, equivalence under all closing source contexts of this grammar is equivalent to equivalence under their translated target tests. This is not a claim about arbitrary target contexts. A checked counterexample demonstrates why literal plugging requires a closed hole. The package makes no claim about open-hole adequacy, divergence equivalence, numerical readback, full beta-normalization, or complexity.

The classical source is Gordon Plotkin, “Call-by-name, call-by-value and the lambda-calculus” (1975). Challenge fixes the context grammar, plugging, shifting, CPS translation and observations; its isolated theorem holes are not imported by Solution. The source checkpoint passed targeted independent mathematical review; integrated package review and hosted preflight are pending.
