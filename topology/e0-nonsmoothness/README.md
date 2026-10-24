# Generic ergodicity and non-smoothness of E₀

The sole target is the category obstruction to classifying eventual equality
on Cantor space by equality in a second countable T0 target. CantorSpace is
the actual product Nat→Bool, and E0 x y means that some N satisfies x n=y n
for every n≥N. This is finite change of values, not finite permutations of
coordinates. BPPreimages means that every open inverse image has the property
of Baire. The development proves an invariant BP-set zero-one law and a
comeagre constant fiber for invariant BP maps, then rules out BP reductions
to equality. An explicit Borel-to-BP bridge and Borel corollary back the
standard non-smoothness claim. No HKL dichotomy or larger classification
theorem is claimed.

Christian Rosendal, Baire Category author-hosted notes, Exercise18, directly
states generic constancy for E0-invariant BP maps to Polish targets:
https://homepages.math.uic.edu/~rosendal/WebpagesMathCourses/MATH511-notes/DST%20notes%20-%20Kuratowski-Ulam08.pdf
John D. Clemens, Clinton T. Conley and Benjamin D. Miller, The Smooth Ideal,
DOI10.1112/plms/pdv069, section1.3 Propositions1.3.7–8, directly supplies the
finite-prefix homeomorphism and countable-basis category arguments:
https://glimmeffros.github.io/publications/smooth.pdf
Our target assumptions are second countability and T0, rather than Polish.
This generalization is explicit; T0 is material. The larger smooth-ideal and
Harrington–Kechris–Louveau results explain the research audience but are not
formalized here. No novelty or external editorial acceptance is promised.

The complete standalone E0Challenge concatenates Definitions, Category,
Mixing and Generic from Mathlib imports. E0Solution imports the separate EZero
package. The five selected names in namespace EZero are finite_flip_mixing,
zero_one, generically_constant, no_baire_reduction and no_borel_reduction.
The selected core proofs expose finite-cylinder mixing, open category mixing,
countable-basis synchronization and the complement-map contradiction to review.
No E0 class-size theorem or Borel-equivalence-relation bundle is claimed.

The generic open-mixing category helper is adapted from the campaign's
HewittSavage/Category.lean at immutable71717137cf598bbc17b97b9424b3d47cb6db66dc;
its original Mathlib upstream credits are retained. The BP semantic audit follows
the prior Baire regularization package at that same immutable commit.

Independent internal AI scope and complete implementation/source-fidelity
reviews pass. Exact-source release readiness is established by immutable
external local native, canonical, rendering, visual and review receipts. A build
alone is not full certification. Only propext, Quot.sound and Classical.choice
are allowed. The literal CantorSpace, E0, BPPreimages, maskHomeomorph and flip
definitions are fixed, with zero definition holes. No intake or registration
is claimed here.

Campaign authors and responsible maintainers: Arthur Freitas Ramos, David
Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex performs
formalization; no human proof contribution or human/external review inferred.
All necessary validation runs locally under AGENTS.md. Lean4.35.0-rc2 and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain exactly pinned.
