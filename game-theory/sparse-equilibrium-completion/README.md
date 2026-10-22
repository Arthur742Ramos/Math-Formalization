# Sparse equilibrium completion: analytic sparsification

This independent Lean project develops the mathematics of *Sharp Sparse Witnesses
for Incomplete Zero-Sum Games*, anonymous revision `1a424f297925294ae5818ff1ee7512304af1d460`
in `Arthur742Ramos/aoe2-equilibrium-balance`, under
`research/sparse-equilibrium-completion`. It is a partial development, not a
whole-paper formalization or a submission-ready entry.

The development proves finite weighted skew cancellation, necessary completion
guards and cuts, the quadratic call-envelope equivalence, and the finite quadratic
grid implication. Finite-feature recombination now gives original-label sparse
cut certificates with exact anchor moments, including both the general `k+1+H`
count and the exact-equilibrium improvement `k+H`. A full block-game bridge derives
the exact-case zero score mean and supported score bounds. Compact certificate
reconstruction and matrix-response perturbation are also covered. Reconstruction
of a new bounded skew block from arbitrary feasible cuts remains open, so these
sparse cut certificates are not yet the paper's completed game witnesses. Definitions
and all proof helpers have stable public exposed declaration names. The theorem map,
including outstanding mathematical work, is in [SCOPE.md](SCOPE.md).

The project pins Lean `v4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; its dependencies are package-owned.
Build from this directory with `lake build`. Verification receipts outside the
frozen source identify the exact tested commit and the scope of each check.
Native checks do not stand in for the registry's canonical sandbox pipeline.

The source is an anonymous AI-assisted draft. Human formalization authorship,
responsible maintainers, and submission authorship have not been supplied for
this project. Existing topology-package author lists confer no membership here.
The implementation and documentation were produced with OpenAI Codex. Classical
Caratheodory recombination is reused from the Mathlib Sphere Eversion development,
not claimed as new mathematics. Internal
AI review, machine checks, human review, and external peer review are separate.
Project code follows the repository's Apache-2.0 license; upstream definitions
retain their own attribution. No paper copyright or authorship is reassigned.

Local research and verification are authorized. This task performs no registry
submission, publication, account changes, permission changes, or security changes.
Current registry editorial eligibility and metadata acceptance are not established.
