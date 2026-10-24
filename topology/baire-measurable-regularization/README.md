# Baire-measurable regularization

The one target is the characterization of maps into a second countable
topological space whose inverse images of all open sets have the property of
Baire: exactly those maps whose restriction to some comeagre Gδ subset is
continuous in the subspace topology. The domain is an arbitrary topological
space. A companion for Baire domains makes density explicit. A residual set
can be empty in a non-Baire space. Density is proved only in the Baire-source
corollary; nonemptiness would additionally require a nonempty source. This is not ambient continuity at points of that
set, the Baire-class-one continuity-points theorem, or sigma-continuity.

Christian Rosendal, Baire Category author-hosted lecture notes, Exercise17,
directly states the forward theorem for arbitrary domain and second countable
codomain. Its exercise statement, not a supplied proof, was directly read:
https://homepages.math.uic.edu/~rosendal/WebpagesMathCourses/MATH511-notes/DST%20notes%20-%20Kuratowski-Ulam08.pdf
The converse is proved from the actual subspace topology and comeagre
agreement. Kechris, Classical Descriptive Set Theory (1995), Theorem8.38,
is classical attribution cited by the research sources; direct inspection of
the original book proof is not claimed.

Raphael Carroy and Benjamin D. Miller, Bases for functions beyond the first
Baire class, JSL85(3)(2020), DOI10.1017/jsl.2020.60, Proposition3.1, and Anton
Bernshteyn, On Baire Measurable Colorings of Group Actions, arXiv1708.09821v2,
section4.1 Lemma4.2, directly use continuous restrictions on comeagre sets in
research on descriptive function bases and measurable graph colorings.
Those larger applications are not formalized here.

Bounded pinned-library, repository/open-PR and public-registry overlap audits
are recorded privately. No novelty, priority or exhaustive private-intake
clearance is claimed. Scope review precedes proof development.

The complete BaireRegularization proof synchronizes open approximations for
an actual countable basis, shrinks the residual agreement set to a comeagre
Gδ and proves restricted continuity by the basis criterion. The converse uses
ambient open representatives of relatively open preimages and residual
agreement. No continuous-restriction conclusion is assumed as a premise of
the forward theorem. RegularChallenge contains the complete standalone proof
from Mathlib imports; RegularSolution imports the separate source module.
The two selected names are bpPreimages_iff_continuous_restriction and
exists_dense_continuous_restriction in namespace BaireRegularization.

Independent internal AI scope and implementation/source-fidelity reviews pass.
Exact-source release readiness is established by immutable external local
native, canonical, rendering, visual and review receipts. A build alone is not
full certification. Only propext, Quot.sound and Classical.choice are allowed;
zero definition holes. The fixed BPPreimages abbreviation is protected in the
selected type closure. Its body and the BP/open-meagre semantic bridge follow
the credited prior Pettis package at immutable commit5ab727c55f72496e0603dad7c84c9e1e1b4f6610.
No registry intake or registration is claimed here.

Campaign authors and responsible maintainers: Arthur Freitas Ramos, David
Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex performs
formalization. No human proof contribution or human/external review inferred.
All necessary validation runs locally under AGENTS.md, with the exact pinned
Lean4.35.0-rc2/compiler11acb17 and Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.
