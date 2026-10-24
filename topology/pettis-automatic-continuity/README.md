# Pettis automatic continuity

The sole target is continuity of a group homomorphism f:G→H when G is a Baire
topological group, H is a separable topological group, and inverse images of
all open sets have the property of Baire. No injectivity, surjectivity,
source-Polish or separation hypothesis is supplied. The essential Pettis lemma
states that AA⁻¹ is a neighborhood of the identity when A has the property of
Baire and is nonmeagre. Its proof and the countable right-translate cover must
be constructed internally; no such conclusion is supplied as a premise.

B. J. Pettis, On Continuity and Openness of Homomorphisms in Topological Groups,
Annals of Mathematics 52 (1950),293–308, DOI10.2307/1969471, is the classical
source. The original full text was inaccessible; direct original-proof
inspection is not claimed. Christian Rosendal's author-hosted November2008
survey, Automatic Continuity of Group Homomorphisms, section2.1 Lemma2.1 and
Theorem2.2, was directly inspected in its stated Polish scope.
https://homepages.math.uic.edu/~rosendal/PapersWebsite/AutomaticContinuity06.pdf
Taras Banakh, arXiv2206.02481v3, introduction, explicitly states the classical
Baire-to-omega-narrow BP-continuity result. We target the separable-codomain
case with its cover proved here, not Banakh's new Cech-complete or universal
measurability results. https://arxiv.org/abs/2206.02481v3

Bounded pinned-library/repository searches found no category Pettis automatic
continuity theorem. Public registry Pettis search had no result; automatic
continuity found only a Busch/Born-rule matrix theorem, whose actual compared
statements were inspected and are unrelated. No novelty or exhaustive private
intake clearance is claimed. Independent internal AI scope review approves
the precise Baire/separable topological-group theorem, including its absence
of a Hausdorff requirement.

The two Comparator-selected declarations are PettisAutomatic.mul_inv_mem_nhds_one
and PettisAutomatic.continuous_of_baire_preimages. Category.lean proves the
neighborhood lemma using two residual sets in a nonempty open intersection.
Automatic.lean uses a countable dense target set to cover the source by right
translate preimages. One is nonmeagre, and common right factors cancel in
pairwise differences. Centers need not lie in the homomorphism image. There
is no uncountable union of meagre sets. BPPreimages is a fixed transparent
abbreviation for the quantified open-preimage hypothesis, with no definition
holes. Its body is protected in the selected Comparator type closure.

The short open-residual witness and open-modulo-meagre semantic bridge adapt
the credited campaign helper at immutable commit ac523b3beacafa744cdf2496a43e14803c2147e6,
topology/hewitt-savage-category/HewittSavage/Category.lean. Mathlib supplies the
credited category and topological-group infrastructure. PettisChallenge holds
the complete standalone proof with Mathlib imports; PettisSolution imports
the separate project modules.

Independent internal AI scope and implementation/source-fidelity review and
exact-source release readiness are recorded by immutable external local
verification, rendered-readability and review receipts. A build alone is not
full release certification. Only propext, Quot.sound and Classical.choice are
permitted axioms. No registry submission or registration is claimed here.

Campaign authors and responsible maintainers: Arthur Freitas Ramos, David
Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex performs the
formalization; no human proof contribution or human/external review is inferred.
All necessary validation runs locally under AGENTS.md. Lean4.35.0-rc2 and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned.
