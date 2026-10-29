# Comparator and verification status

This package is a draft. Its eleven current Comparator Challenges contain complete
proofs without new axioms or proof holes. Each configuration must be checked against its own
exact source revision; local experiments are not protected verification or
editorial acceptance.

`comparator-pattern.json` selects the exact pattern theorem, its necessity
statement and the explicit witness. Its Challenge is 762 lines and 30,225
bytes. The two region configurations select the necessity and sufficiency
directions separately, as described in `REGION-COMPARATOR.md`; neither selects
the biconditional directly. The region Challenges are 522 and 698 lines. These
three Challenges exceed the observed 300-line readability warning.

`comparator-source.json` selects fixed-context agreement and the active-target
consequences of Proposition 10. Its Challenge is 264 lines. It does not cover
the paper's other families. `comparator-grounded.json` selects an established grounded-fixed-point
equivalence and its contextual specialization, credited to Bogaerts, Vennekens
and Denecker. Its 166-line Challenge is below the observed readability warning;
its eligibility as a standalone entry has not been established. A sixth draft selects the full labelled-spine relevant-mechanism theorem, its
forcing/gate characterizations, and the gate-equation intervention consequence
under opposite repeated gates. The selected intervention statement is not itself
a theorem about arbitrary full-carrier mechanisms. Its 816-line, 34,284-byte
Challenge exceeds both readability warnings. A seventh draft selects the
copy-majority representation, original-link interventions and the infinite
copy-clamp counterexample; its 442-line Challenge exceeds the 300-line
readability warning. It does not claim preservation for arbitrary added-copy
interventions. An eighth draft selects unrestricted uniform synthesis,
its forest construction and the finite-root-ancestry bridge; its 418-line
Challenge exceeds the 300-line readability warning. Two more drafts separately
select the accessible/reachable interval and fully relevant endpoint witnesses;
together these imply the fixed-context SOME/ALL criteria for target subsets
of the carrier. Their
Challenges are 565 and 787 lines and exceed the 300-line warning. The four
SOME/ALL biconditionals themselves are proved in the Lean package but are not
directly selected in these configurations. An eleventh, 223-line Challenge
selects the whole-carrier uniqueness and restricted-well-foundedness bridges.
The all-mechanism/all-context biconditionals remain separately proved in the
Lean package and are not directly selected by this bridge. Each configuration requires an explicit statement of its scope; a
single entry cannot be assumed to cover the whole manuscript.

Release preparation requires an independent final source and manuscript
crosswalk review; exact-source compilation and axiom audit; protected
Comparator, definition-value and negative-control checks; required independent
kernels; provenance and metadata checks; and rendering and visual review.
Current toolchain, import and size requirements must be checked against the
applicable policy. The currently available local checks do not establish those
release gates, editorial acceptance or registry registration.
