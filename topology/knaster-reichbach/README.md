# Knaster–Reichbach extension: local development

The sole intended final target is: every homeomorphism between closed nowhere-dense subsets of Cantor space extends to an autohomeomorphism of the whole Cantor space, agreeing pointwise on the prescribed subset. Empty prescribed subsets are included. Cantor space means the usual product topology on `ℕ → Bool`.

The full theorem is implemented as `KnasterReichbach.exists_homeomorph_extension`.
It constructs a genuine ambient homeomorphism, taking only closedness,
nowhere-density and the prescribed subtype homeomorphism as assumptions.
All proof/library declarations have proofs without holes or new axioms.
Independent internal AI mathematical/source review found no blocker.
The source is published in [PR45](https://github.com/Arthur742Ramos/Math-Formalization/pull/45).
Local canonical full verification and rendering passed on 2026-10-23 for
source `caf9b142e9b7061c364499b5994dae4ab5bf4071`. The full report SHA-256 is
`d48ccb356f846e5b389a88c578bb72f84ea963e123642088277b9b04fbb4b1b8`;
the render report SHA-256 is
`d7de474965b1b6fab41c188394c1b197795d8d70f81f298521a2e7a1f95e5cb0`.
The selected rendered theorem and proof were inspected; final proof-state
expansion was not visibly confirmed. An independent internal AI final packet
review was completed for that source. Earlier predecessor results remain in
[local validation history](verification/local-history.json).

An intake for `caf9b142` was submitted on 2026-10-27. Its mechanical
verification and rendering passed. Registration was not established at the
last observation. These historical results do not certify this later source;
its exact-source checks and review must be recorded separately.

## Mathematical sources and scope

- B. Knaster and M. Reichbach, *Notion d’homogénéité et prolongements des homéomorphies*, Fundamenta Mathematicae 40 (1953), 180–193, DOI 10.4064/fm-40-1-180-193, https://eudml.org/doc/213323. Bibliography verified; original scan access currently403, so no direct original-proof inspection is claimed.
- E. Shchepin and V. Valov, *On homogeneity of Cantor cubes*, arXiv:2109.07214v2, introduction: directly inspected modern formulation for compact perfect zero-dimensional metric spaces and closed nowhere-dense subsets. We initially target its canonical Cantor-space case, not its nonmetrizable generalization.
- A. Gutek, 2012 technical report, Theorem 2.5, https://www.tntech.edu/cas/pdf/math/techreports/TR-2012-4.pdf: independently inspected formulation of the Cantor-space extension theorem.
- W. Kubiś, A. Kucharski and S. Turek, *Homogeneity of profinite graphs*, arXiv:2602.15696v2 (2026): a current Knaster–Reichbach type theorem illustrates a research audience; its graph-structure extension is not a target here.

The substantive construction alternates compatible finite clopen refinements, preserving the given partial homeomorphism and forcing agreement on longer prefixes on both sides. Refinement existence and the global extension are proved internally. No mathematical novelty or global formalization priority is claimed.

## Proof construction

`Cylinders.lean` proves the countable first-escape clopen partition of a closed
set's complement and arbitrarily deep avoidance of a closed nowhere-dense set.
`ClopenExtension.lean` lifts clopen traces while reserving opposite outside points.
`MatchedPartitions.lean` alternates source and target binary coordinate splits,
retaining matched empty cells and preserving the exact trace of the given map.
`CompatibleLimit.lean` uses compact nested fibers, coordinatewise uniqueness and
the compact-codomain closed-graph theorem to construct a homeomorphism.
`Extension.lean` constructs all those relations and proves exact agreement.
No refinement or extension existence premise is assumed in the final theorem.

The Comparator selects the final theorem with zero definition holes. The
`CantorSpace` abbreviation is protected through the statement dependency closure. `KRChallenge` contains a standalone proof from
Mathlib imports; `KRSolution` imports the independently compiled project modules.
Challenge and Solution semantic entrypoints check the literal `Nat -> Bool`
product-space formulation separately. Standard allowed axioms are only
`propext`, `Quot.sound` and `Classical.choice`.

Public registry searches for Knaster and Reichbach returned no matches on
2026-10-23; a broader homeomorphism search found no equivalent title.
This is a bounded audit, not a global novelty or priority claim.

## Attribution and validation

Established campaign authors and responsible maintainers remain Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; these roles do not assert a human proof contribution or review. OpenAI Codex authors the formalization. Independent internal AI review is separate from human or external editorial review.

Lean is pinned to 4.35.0-rc2 and Mathlib to 065356127b1dc0016f66b7283ce0ce2c4055aa55. All necessary validation runs locally under root AGENTS.md. Source-bound proof, comparison, negative-control, axiom, independent-kernel, rendering and release review evidence must be assessed for the exact source before a verified handoff or submission. Dependency cache reuse is upstream infrastructure only, never a claim of fresh project verification.
