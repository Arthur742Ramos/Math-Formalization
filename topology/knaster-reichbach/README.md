# Knaster–Reichbach extension: local development

The sole intended final target is: every homeomorphism between closed nowhere-dense subsets of Cantor space extends to an autohomeomorphism of the whole Cantor space, agreeing pointwise on the prescribed subset. Empty prescribed subsets are included. Cantor space means the usual product topology on `ℕ → Bool`.

This is preparation, not a completed proof or verified submission. The final extension theorem is not yet declared. Each declaration in the source is proved without holes or new axioms; foundational cylinder lemmas are being developed first. No provider PR, intake or registry claim is made for this package.

## Mathematical sources and scope

- B. Knaster and M. Reichbach, *Notion d’homogénéité et prolongements des homéomorphies*, Fundamenta Mathematicae 40 (1953), 180–193, DOI 10.4064/fm-40-1-180-193, https://eudml.org/doc/213323. Bibliography verified; original scan access currently403, so no direct original-proof inspection is claimed.
- E. Shchepin and V. Valov, *On homogeneity of Cantor cubes*, arXiv:2109.07214v2, introduction: directly inspected modern formulation for compact perfect zero-dimensional metric spaces and closed nowhere-dense subsets. We initially target its canonical Cantor-space case, not its nonmetrizable generalization.
- A. Gutek, 2012 technical report, Theorem 2.5, https://www.tntech.edu/cas/pdf/math/techreports/TR-2012-4.pdf: independently inspected formulation of the Cantor-space extension theorem.
- W. Kubiś, A. Kucharski and S. Turek, *Homogeneity of profinite graphs*, arXiv:2602.15696v2 (2026): a current Knaster–Reichbach type theorem illustrates a research audience; its graph-structure extension is not a target here.

The substantive construction will be a compatible back-and-forth refinement of clopen partitions, preserving the given partial homeomorphism and forcing vanishing mesh on both sides. Existence of that refinement and the global extension are proof obligations, not hypotheses to be assumed. No mathematical novelty or global formalization priority is claimed.

## Implemented groundwork

`KnasterReichbach/Cylinders.lean` proves cylinder nesting, equal-depth disjointness,
arbitrarily deep avoidance of a closed nowhere-dense set, and the first-escape
decomposition of the complement of a closed set into countably many nonempty,
pairwise disjoint clopen cylinders. The empty prescribed set is permitted.
These are construction lemmas, not the ambient extension theorem.

The next obligations are compatible matched refinements around the given
homeomorphism, shrinking mesh on both sides, total mutually inverse limit maps,
continuity and exact agreement on the prescribed closed set.

An internal independent scope audit approved this target for development;
it did not certify the unfinished extension theorem. Public registry searches
for Knaster and Reichbach returned no matches on 2026-10-23; a broader
homeomorphism search returned seven results and no equivalent title.
This is a bounded overlap audit, not a global novelty claim.

## Attribution and validation

Established campaign authors and responsible maintainers remain Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; these roles do not assert a human proof contribution or review. OpenAI Codex authors the formalization. Independent internal AI review is separate from human or external editorial review.

Lean is pinned to 4.35.0-rc2 and Mathlib to 065356127b1dc0016f66b7283ce0ce2c4055aa55. All necessary validation runs locally under root AGENTS.md. Source-bound proof, comparison, negative-control, axiom, independent-kernel, rendering and release review gates remain required before any verified handoff or submission. Dependency cache reuse is upstream infrastructure only, never a claim of fresh project verification.
