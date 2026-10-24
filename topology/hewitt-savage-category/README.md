# Category Hewitt–Savage zero-one law

For any infinite index type J and topological space X whose product X^J is
Baire, a Baire-property subset A of X^J invariant under every finite-support
coordinate permutation is meagre or has meagre complement. The Polish-sequence
corollary covers X^Nat for every Polish X. No nonemptiness or mixing premise is
supplied to either result. An empty product space is included. These are the
two Comparator-selected declarations category_zero_one and
polish_sequence_zero_one in namespace HewittSavage.

FiniteMoves σ means exactly that {j | σ(j) ≠ j} is finite. The proof inductively
builds such a permutation displacing a finite coordinate set, patches actual
tuples in two finite cylinders, and proves mixing. Two open approximations to
the Baire-property set and its complement give global residual sets. Pullback
through the coordinate homeomorphism and the Baire theorem give the dichotomy.
There is no uncountable union of meagre error sets.

M. Bhaskara Rao and K. P. S. Bhaskara Rao, A category analogue of the
Hewitt–Savage zero-one law, Proceedings of the AMS 44(2), June 1974,497–499,
DOI10.1090/S0002-9939-1974-0345084-9, Theorem (2⇒4) and Corollary1, are the
classical source. Their original corollary is stronger: it allows arbitrary X
without assuming the product Baire. That full generality is not claimed here.
The original published scan was directly inspected through a mirror:
https://scispace.com/pdf/a-category-analogue-of-the-hewitt-savage-zero-one-law-4esscf6sv3.pdf

D. Osin, arXiv2004.07479v6, section3.1 Theorem3.4, gives a directly inspected
modern category argument and illustrates research applications to generic
algebraic structures. Those applications are not formalized here.
https://arxiv.org/abs/2004.07479v6

Bounded repository and pinned-Mathlib searches found no equivalent zero-one
result. A public registry search for Hewitt found only the unrelated density
theorem; Savage found no result. A broad zero-one query was inconclusive.
No novelty, priority or exhaustive private-intake clearance is claimed.

Category.lean proves the residual argument; Permutation.lean proves finite
support and displacement; Product.lean proves mixing and both final theorems.
The open-residual witness and its semantic bridge adapt the credited earlier
campaign CategoryGame helper at immutable commit a07507e8cd572566d58d17aa8a8c03ef27cbf3ec.
Mathlib supplies the credited finite-cylinder, reindexing, residual and Baire
infrastructure. HSChallenge contains the complete standalone proof from
Mathlib imports. HSSolution imports the separate project modules. There are
zero definition holes; the fixed FiniteMoves body remains protected in the
selected statement closure.

Independent internal AI scope and implementation/source-fidelity reviews pass.
Exact-source release readiness is established by immutable external local
verification, rendered-readability and review receipts. A build alone is not
full release certification. Only propext, Quot.sound and Classical.choice are
permitted axioms. No registry submission or registration is claimed here.

Campaign authors and responsible maintainers: Arthur Freitas Ramos, David
Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex performs the
formalization; no human proof contribution or human/external review is inferred.
All necessary validation runs locally under root AGENTS.md. Lean4.35.0-rc2 and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain exactly pinned.
