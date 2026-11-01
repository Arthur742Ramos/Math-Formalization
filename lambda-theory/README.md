# Computability theory for closed lambda programs

Draft package. The independent Challenge gives concrete de Bruijn syntax, full-beta reachability, the canonical term encoding and ten theorem obligations. The Solution imports 125 proof modules from the public lambda/Turing checkpoint c695e9a1b47f0c9cb7031f5c13b8494180b7b948. The syntax encoder in `TermCode.lean` uses reordered structural equations and one helper proof in `FoldCode.lean` is written explicitly for module-independent comparison; the other 123 modules are byte-for-byte copies. Their original headers and third-party notices are preserved. Challenge holes are not Solution dependencies.

The results concern Church-numeral observations, including nonnumerical outcomes; absence of a result is not a divergence claim. The normal-form theorem has an explicit computable predicate and proves a computable many-one reduction. It selects a fixed recursive code in the proof and does not claim uniform code extraction from proofs.

Mathlib and its inherited dependencies remain pinned. Independent review of this package layout, protected comparison, mutation controls and service checks are pending. This directory is not submission-ready.
