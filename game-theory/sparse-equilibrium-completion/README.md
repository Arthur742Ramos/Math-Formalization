# Sparse equilibrium completion: foundation tranche

This independent Lean project develops the mathematics of *Sharp Sparse Witnesses
for Incomplete Zero-Sum Games*, anonymous revision `1a424f297925294ae5818ff1ee7512304af1d460`
in `Arthur742Ramos/aoe2-equilibrium-balance`, under
`research/sparse-equilibrium-completion`. It is a partial development, not a
whole-paper formalization or a submission-ready entry.

The initial module proves finite weighted skew cancellation, necessary completion
guards and cuts, the quadratic call-envelope equivalence, and the finite quadratic
grid implication. A matrix-response perturbation bound is also included. Definitions
and all proof helpers have stable public declaration names. The full theorem map,
including outstanding mathematical work, is in [SCOPE.md](SCOPE.md).

The project pins Lean `v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; its dependencies are package-owned.
Build from this directory with `lake build`. Verification receipts outside the
frozen source identify the exact tested commit and the scope of each check.
Native checks do not stand in for the registry's canonical sandbox pipeline.

The source is an anonymous AI-assisted draft. Human formalization authorship,
responsible maintainers, and submission authorship have not been supplied for
this project. Existing topology-package author lists confer no membership here.
The implementation and documentation were produced with OpenAI Codex. Internal
AI review, machine checks, human review, and external peer review are separate.
Project code follows the repository's Apache-2.0 license; upstream definitions
retain their own attribution. No paper copyright or authorship is reassigned.

Local research and verification are authorized. This task performs no registry
submission, publication, account changes, permission changes, or security changes.
Current registry editorial eligibility and metadata acceptance are not established.
