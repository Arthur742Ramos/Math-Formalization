# Comparator and verification status

This package is a draft. Its five current Comparator Challenges contain complete
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
its eligibility as a standalone entry has not been established. Further
configurations are needed for contextual SOME/ALL determinacy, uniform
synthesis, labelled spines and representation examples. Each configuration requires an explicit statement of its scope; a
single entry cannot be assumed to cover the whole manuscript.

Release preparation requires an independent final source and manuscript
crosswalk review; exact-source compilation and axiom audit; protected
Comparator, definition-value and negative-control checks; required independent
kernels; provenance and metadata checks; and rendering and visual review.
Current toolchain, import and size requirements must be checked against the
applicable policy. The currently available local checks do not establish those
release gates, editorial acceptance or registry registration.
