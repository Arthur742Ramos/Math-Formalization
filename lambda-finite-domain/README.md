# Finite numerical domains of closed lambda programs

The package classifies finite numerical domains of closed untyped lambda programs under full beta reduction. It proves computable many-one completeness for existential-universal Boolean normal forms. The exact-gap theorem gives a primitive-recursive closed-program map for each fixed computable relation: successful instances have precisely the initial-segment domain below their least witness, while unsuccessful instances have a total numerical domain. This code is selected existentially; no extraction from arbitrary computability proofs is claimed.

Numerical observations are Church numerals reachable after applying a program to a numeral. No numerical observation does not by itself mean divergence. The independent Challenge fixes the syntax, encoding, numerical semantics and bounded witness and contains two theorem obligations. The Solution does not import the Challenge.

This is a classical computability classification adapted to the explicit lambda model. It reuses the registered lambda/Turing and closed-lambda computability packages, and is related to the registered refinement/equivalence package; all predecessor records remain unchanged. Independent package review, protected comparison, and service validation are pending.
