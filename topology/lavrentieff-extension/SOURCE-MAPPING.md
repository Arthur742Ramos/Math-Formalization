# Source, scope, and overlap

M. M. Lavrentieff, *Contribution à la théorie des ensembles homéomorphes*,
Fundamenta Mathematicae6 (1924),149–160, DOI10.4064/fm-6-1-149-160:
https://eudml.org/doc/214269 and https://matwbn.icm.edu.pl/ksiazki/fm/fm6/fm6118.pdf.
The scanned printed pages149–150 were directly read. They state the finite-dimensional
Euclidean theorem and prove it through zero oscillation and restricted inverse extensions.
Original PDF SHA256: eeb0fe02c251ff544250ba9028929f95a988e127d060482620a62deff13e72e5.

Michael Müger, *Topology for the working mathematician*, Theorem3.4.15,
printed p61, https://www.math.ru.nl/~mueger/topology.pdf, states the modern
complete-metric form with arbitrary subsets and Gδ supersets inside their closures;
Exercise3.4.16 gives the restriction construction. This exact scope was directly
checked independently. PDF SHA256: fea8e1c9760c31387175f84130e1199c1a41b604fa38f66ac8e63cd78630f9f9.
The final topological wrapper uses the equivalent compatible-complete-metric assumption.
The original paper alone is not cited as having arbitrary complete-metric scope.

Hart and van Mill, *Homogeneity and rigidity in Erdős spaces*, arXiv1802.04352v1,
https://arxiv.org/html/1802.04352v1, introduction and section1, use the extension
principle to enumerate and eliminate unwanted homeomorphisms. This provides a
concrete general/descriptive-topology audience. Those applications and the original
paper's further applications are not claimed as formalized. Completeness is retained
despite the broad informal introductory wording in that research paper.

On 2026-10-23 the clean repository base was the Sierpiński PR41 merge `6c92267`.
The catalog and all open PRs were inspected: #36 open Polish images, #37 open Baire
representation, #39 Cantor characterization, #40 Hodge, #42 sparse equilibrium.
Alexandrov–Urysohn Baire and Sierpiński rational characterizations were also excluded
as existing work. This extension theorem has a different conclusion and construction.
The new package modifies none of those packages or PR branches.

Palomar public query revision509 was inspected. Searches for `Lavrent`, `Lavrentieff`, and `homeomorphism extension` returned no entries.
The `oscillation` query returned two unrelated entries. The broader `extension`
query returned32 entries over two pages, none formalizing this theorem. The
`Gδ extension` query returned the broad extension results and supplies no narrower evidence.
This is a bounded public duplicate audit, not proof of global formalization priority
or absence of private pending attempts. Sierpiński's reported public registration
PALOMAR-2026-10-23-000003 v1 is treated as existing; no duplicate intake is performed.

Pinned Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 was searched independently
across topology, Gδ, extensions, completions, Polish and partial-homeomorphism APIs.
No equivalent theorem was found. `continuousOn_extendFrom` assumes every required
limit exists, so it does not already establish the Gδ extension-domain theorem.
`IsGδ.setOfPred_continuousAt` concerns an existing total function's continuity locus.
These are credited reusable infrastructure, not replacements for the missing proof.
