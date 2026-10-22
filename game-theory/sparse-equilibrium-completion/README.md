# Sparse equilibrium completion: sparse witnesses and two-anchor rigidity

This independent Lean project develops the mathematics of *Sharp Sparse Witnesses
for Incomplete Zero-Sum Games*, anonymous revision `1a424f297925294ae5818ff1ee7512304af1d460`
in `Arthur742Ramos/aoe2-equilibrium-balance`, under
`research/sparse-equilibrium-completion`. It is a partial development, not a
whole-paper formalization or a submission-ready entry.

The development proves the weighted completion criterion in both directions,
including zero-weight row guards, the quadratic call-envelope equivalence and the
finite quadratic grid implication. Finite-feature recombination gives actual
original-label sparse completed-game witnesses with exact anchor responses and
residual support at most `k+1+ceil(sqrt(Mr/η))`, improved to `k+ceil(sqrt(Mr/η))` for exact
equilibria. The skew completion is reconstructed by finite layer-cake duality and
classical compact-convex separation. All original rows satisfy the resulting
response bound. This is an existence proof over reals; executable rational
reconstruction and complexity claims remain open. Definitions and all proof
helpers have stable public exposed declaration names. The theorem map, including
outstanding sharp support rates and uncertainty work, is in [SCOPE.md](SCOPE.md).

The two-anchor construction now realizes every strictly positive residual target
of mass `1/4` using bounded observations. Under the two minimum shares `3/8`,
exact equilibrium forces both shares to be tight, the target distribution, and
every residual edge. Its uniform specialization is bridged to the paper's
explicit score and quadratic weight formulas. The normalized sparse-witness
wrappers distinguish residual support from total support, including anchors.
Quantitative inverse-square support and uncertainty laws remain unfinished.

The project pins Lean `v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; its dependencies are package-owned.
Build from this directory with `lake build`. Verification receipts outside the
frozen source identify the exact tested commit and the scope of each check.
Native checks do not stand in for the registry's canonical sandbox pipeline.

The pinned source is an anonymous AI-assisted draft. The user subsequently named
Arthur, David and Ruy as paper authors, with Ruy in the institutional role; full
names, affiliations and explicit human proof roles remain unspecified. Human formalization authorship,
responsible maintainers, and submission authorship have not been supplied for
this project. Existing topology-package author lists confer no membership here.
The implementation and documentation were produced with OpenAI Codex. Classical
Caratheodory recombination is reused from the Mathlib Sphere Eversion development,
not claimed as new mathematics. Mathlib compact-convex Hahn–Banach separation is
also reused and credited in the material-definition inventory. Internal
AI review, machine checks, human review, and external peer review are separate.
Project code follows the repository's Apache-2.0 license; upstream definitions
retain their own attribution. No paper copyright or authorship is reassigned.

Local research and verification are authorized. This task performs no registry
submission, publication, account changes, permission changes, or security changes.
Current registry editorial eligibility and metadata acceptance are not established.
