# Provenance

The principal reference is Frank Sturm, *Indecomposable and Chainable
Continua*, Auburn University master's thesis (2009), Definition 1.7 and
Theorems 1.8, 1.10, 1.11 and 1.13, printed pages 14 to 16.
[Original thesis](https://etd.auburn.edu/bitstream/handle/10415/1827/Sturm-ThesisComplete.pdf?isAllowed=y&sequence=1).
The thesis spells the term "compossant". Its metric countable-family argument
is adapted to a countable open basis. Nondegeneracy is explicit wherever
membership of the base point is needed. Corollary 1.12 is not used because
its wording omits the indecomposability hypothesis. No exact cardinality
claim is made. The source author has not been contacted.

`Boundary.lean` retains the complete `Solution.lean` from
[boundary-bumping-lean at 58831416a12f73312ac01cdaec19c060a6d4b142](https://github.com/Arthur742Ramos/boundary-bumping-lean/blob/58831416a12f73312ac01cdaec19c060a6d4b142/Solution.lean),
Git blob `6ece552b0140585130e2b9cf68d7bb4c7da97ad5`.
`Interior.lean` retains the complete `Solution.lean` from
[indecomposable-continuum-lean at a5a85f8b7e2be3cff582b5cff7c35895cd7c4d1e](https://github.com/Arthur742Ramos/indecomposable-continuum-lean/blob/a5a85f8b7e2be3cff582b5cff7c35895cd7c4d1e/Solution.lean),
Git blob `f474e45865ef807138424be2d32e314d81c59680`.
The only adaptations are the module filenames, LF newline normalization and
one added terminal blank line.
The source declarations, imports, copyright and authorship are retained.
Both modules are built afresh. No old compiled project artifact is supplied.
Only these proof modules are reused; the old repositories and build systems
are not copied. Their three credited authors are also credited in the
current project headers and metadata. Source hashes and reuse comparisons
are recorded in `reuse.json`.

The indecomposability characterization follows Paul Bankston,
*Metric Topology: A First Course*, Propositions 29.1 and 29.2,
[printed pages 91 and 92](https://www.mscsnet.mu.edu/~paul/Paper/4450102text.pdf#page=91).
The proofs of the new composant results are in `Solution.lean`. Challenge
contains complete identical definitions and eight independent statements;
it imports only pinned Mathlib, without either reused module or Solution.

Project code is Apache-2.0, under the repository root license. The complete
pinned source files in `definition-evidence` retain original attribution and
the supplied dependency license. The thesis and lecture notes are cited by
link and are not redistributed. Author checks use a byte-qualified local
dependency cache; this is inherited revision evidence with fresh byte
comparisons, not a claim of a clean dependency rebuild. No mathematical
novelty, source-author endorsement or registry acceptance is claimed.
