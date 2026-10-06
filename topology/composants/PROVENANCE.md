# Provenance

The headline result is Theorem 3.3 of V. Todorov and V. Valov,
*Generalized Cantor manifolds and indecomposable continua*, Questions and
Answers in General Topology 30 (2012), 93–102. Definition 1.1 gives the
open-cover formulation on page 94; the theorem and proof are on pages 98–99.
[Primary paper](https://www.jstage.jst.go.jp/article/qagt/30/2/30_93/_pdf/-char/en).

The proof follows the compact-limit argument for shrinking-fiber maps. A
different dense composant supplies a compact connected bridge avoiding the
single proper limit subcontinuum. The final step proves the actual cover
obstruction using ambient metric balls. No equivalence with an unproved
metric reformulation is assumed.

`Foundations.lean` is the published baseline `Solution.lean`, retained byte
for byte under a new module filename from
[Math-Formalization at 50addf6b95fcc755aa6b30017cb34416a740aef2](https://github.com/Arthur742Ramos/Math-Formalization/blob/50addf6b95fcc755aa6b30017cb34416a740aef2/topology/composants/Solution.lean).
It contains the eight classical composant results. Their reference is Frank
Sturm, *Indecomposable and Chainable Continua*, Auburn University master's
thesis (2009), Definition 1.7 and Theorems 1.8, 1.10, 1.11 and 1.13, pages 14–16.
[Original thesis](https://etd.auburn.edu/bitstream/handle/10415/1827/Sturm-ThesisComplete.pdf?isAllowed=y&sequence=1).
The countable-family argument uses a countable open basis. Nondegeneracy is
explicit wherever base-point membership is needed. Corollary 1.12 is not used.

`Boundary.lean` retains the complete `Solution.lean` from
[boundary-bumping-lean at 58831416a12f73312ac01cdaec19c060a6d4b142](https://github.com/Arthur742Ramos/boundary-bumping-lean/blob/58831416a12f73312ac01cdaec19c060a6d4b142/Solution.lean),
Git blob `6ece552b0140585130e2b9cf68d7bb4c7da97ad5`.
`Interior.lean` retains the complete `Solution.lean` from
[indecomposable-continuum-lean at a5a85f8b7e2be3cff582b5cff7c35895cd7c4d1e](https://github.com/Arthur742Ramos/indecomposable-continuum-lean/blob/a5a85f8b7e2be3cff582b5cff7c35895cd7c4d1e/Solution.lean),
Git blob `f474e45865ef807138424be2d32e314d81c59680`.
Their only adaptations are filenames, LF newline normalization and one added
terminal blank line. `reuse.json` records their source comparisons. The
indecomposability characterization follows Paul Bankston's *Metric Topology:
A First Course*, Propositions 29.1 and 29.2.
[Lecture notes](https://www.mscsnet.mu.edu/~paul/Paper/4450102text.pdf#page=91).

Support modules are built from source. Previous compiled project artifacts
are not supplied. `Challenge.lean` imports only pinned dependencies and
independently states all nine selected results with seven complete project
predicates. Its explicit set-order instance in the equal-or-disjoint theorem
preserves the exact expression emitted by the published foundation despite
the additional compact-set imports. Raw comparison performs no normalization.

Complete upstream definition files retain original attribution and licenses.
The paper, thesis and notes are linked rather than redistributed. New
definition source bodies were compared byte for byte with authenticated reads
at their recorded commits. Author verification uses a qualified copied cache;
it does not establish a clean dependency rebuild. No mathematical priority,
source-author endorsement or registry acceptance is claimed.
