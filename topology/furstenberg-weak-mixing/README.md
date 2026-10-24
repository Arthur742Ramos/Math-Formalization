# Furstenberg weak mixing and finite diagonal powers

One target: a continuous self-map of a nonempty topological space whose
square is topologically transitive has every finite diagonal power transitive.
Transitivity means nonempty-open-set hitting at some natural forward iterate,
including time zero. It does not mean the existence of a dense orbit here.
The core proves a hitting-time refinement lemma and finite common
hitting times; product transitivity is connected to the literal two-pair
weak-mixing condition by a proved equivalence using the actual product topology.
The zero-coordinate power is included. No Baire, second-countability, metric,
compactness, surjectivity or perfection premise is used.

Michael Hochman, Notes on Topological Dynamics, June15 2022, section6.2,
Lemmas6.6–7 and Proposition6.8, directly read including proof:
https://math.huji.ac.il/~mhochman/courses/TD2022/notes-v3.pdf
Anima Nagar, Revisiting Variations in Topological Transitivity,
arXiv1906.00712v4, section2.3 Proposition2.28/Lemma2.29, directly read:
https://arxiv.org/html/1906.00712v4
Those sources present compact-system or broader Abelian-action settings.
This package explicitly treats natural iterates of one continuous map on an
arbitrary nonempty topological space. The monoid-action generalization,
measure mixing, transitive-point, thick-hitting and minimal-product theorems
are research context only, not claims of this target.

The complete standalone MixingChallenge contains all proof code from Mathlib
imports; MixingSolution imports the separate WeakMixingPower source. The five
selected names in namespace Furstenberg are weakMixing_iff_product_transitive,
hitting_refinement, finite_refinement, finite_simultaneous_hitting and
finite_power_transitive. Selecting finite_refinement exposes the induction
invariant rather than hiding the accumulated construction behind a helper.
Only the finite-family/power statements assume Nonempty X; the square
equivalence and pair refinement do not. Empty finite families and power zero
are checked through both semantic entrypoints.

Independent internal AI scope review precedes development; complete
implementation/source-fidelity and packaging review are recorded separately.
Exact-source release readiness is established by immutable external local
native, canonical, rendering, visual and review receipts. A build alone is
not full certification. Only propext, Quot.sound and Classical.choice are
allowed; no holes or added axioms. Literal Hit, Transitive, WeakMixing,
pairMap and diagonal definitions are fixed with zero definition holes.
No intake or registration is claimed here.

Campaign authors and responsible maintainers: Arthur Freitas Ramos, David
Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex performs
formalization; no human proof contribution or human/external review inferred.
All necessary validation runs locally under AGENTS.md. Lean4.35.0-rc2 and
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain exactly pinned.
