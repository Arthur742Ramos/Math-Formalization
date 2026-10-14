# Statement and overlap audit

The primary exercise is Munkres, *Topology*, second edition, section 41,
exercise 8(a),(b), printed page 260. The perfect-map definition is section 31,
exercise 7. Its explicit map conditions are retained: continuous, closed,
onto, and compact singleton fibres. The forward theorem proves, rather than
assumes, separation of the target. The inverse theorem removes the unnecessary
separation and onto conditions. No selected conclusion assumes paracompactness
of both spaces, a supplied refinement, an optimizer, a retraction, or a lifting
oracle. The only refinement hypothesis is the classical criterion in the
theorem which explicitly characterizes it.

Sakai's author-uploaded second-edition chapter, dated November 2, 2023,
Theorem 2.6.3(a),(e), supplies the regular-space criterion. The implementation
uses two refinements and neighbourhoods determined by locally finite closed
unions. It does not formalize the other equivalent conditions (star and
sigma-discrete refinements) in that theorem.

All six statements use Mathlib's actual `Continuous`, `IsClosedMap`,
`IsCompact`, `Surjective`, `LocallyFinite`, `RegularSpace`, `T2Space` and
`ParacompactSpace`. There are no custom definitions or typeclass surrogates.
The fibres are actual preimages of singleton sets, allowing empty fibres.
There is no uniform finite fibre bound. Main transfer is universe-polymorphic
in X and Y; the indexed-family transfer also has an independent index universe.
The refinement criterion uses the ambient universe of `ParacompactSpace`, and
its forward implication follows directly from that class's cover quantifiers.
The inverse proof converts a sigma-indexed family to its range to respect that
universe without truncating the cover.

The pinned Mathlib checkout reports HEAD
`065356127b1dc0016f66b7283ce0ce2c4055aa55` with matching Lean 4.35.0-rc2.
Source searches for transfer and arbitrary-refinement statements, and inspection
of Compactness/Paracompact, LocallyFinite, Compactness/LocallyFinite,
Maps/Proper/Basic and Separation/Regular found ingredients and special cases
but no equivalent selected theorem. Proper-map compact-preimage and product
theorems are reused with attribution, not represented as new results.

The public project index and all remote branches were inspected. Existing
topology packages concern composants, order arcs, hyperspace components,
Sorgenfrey covering, Whitney reversibility, Michael biquotient maps and Dowker.
Open PRs were Dowker and repository guidance. The active compact-topology
thread's latest recorded work concerns a separate AFP submission. Registry
search `perfect paracompact` returned no entry on 2026-10-12 (revision 244).
Searches and current registration identities are checked again before intake.
This audit supports local nonduplication, not a worldwide priority claim.

Challenge imports only canonical Mathlib and contains complete proofs. The
proof development adds neither holes nor axioms. The declaration axiom closure
audit is separate from text searches. Exact-commit hosted verification is
required before intake, including Comparator, Lean kernel export, NanoDa,
con-ron and canonical renderer. Actual run URLs and reports are supplied in the
submission packet; this source document makes no advance claim of those runs.
