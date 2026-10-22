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
residual support at most `min(m,k+1+ceil(sqrt(Mr/η)))`, improved to
`min(m,k+ceil(sqrt(Mr/η)))` for exact equilibria, for every residual mass r≥0.
The d-extra-moment wrappers preserve arbitrary specified linear measurements
with d added to the support bound, while the number of anchors remains k.
Their total-support bounds also include the full finite-cardinality cap k+m. The skew completion is reconstructed by finite layer-cake duality and
classical compact-convex separation. All original rows satisfy the resulting
response bound. This is an existence proof over reals; executable rational
reconstruction and complexity claims remain open. Definitions and all proof
helpers have stable public exposed declaration names. The theorem map, including
completed results and outstanding algorithmic, graph, interval-conic and joint-support work, is in [SCOPE.md](SCOPE.md).

For `m≥2`, the two-anchor construction realizes every strictly positive residual
target of mass `1/4` using bounded observations. Under the two minimum shares `3/8`,
exact equilibrium forces both shares to be tight, the target distribution, and
every residual edge. Its uniform specialization is bridged to the paper's
explicit score and quadratic weight formulas. The normalized sparse-witness
wrappers distinguish residual support from total support, including anchors.
Quantitative lower bounds and matching existential upper support order are proved.
For `m≥2`, the attained total-support minima for fixed and minimum shares equal `m+2` at
zero tolerance; for `0<ε≤1` they lie between
`sqrt(3/1216) min(m+2,1/sqrt ε)` and `5 min(m+2,1/sqrt ε)`.
The minimum is noncomputable over actual strategies and completions, with
nonemptiness, attainment, minimality and actual support-cardinality bridges.
Residual minima are also attained: their sharp-order constants are
`sqrt(3/1216)/2` and `3`, for `0<ε≤1` under fixed shares and
`0<ε≤1/1024` under minimum shares. Interval-compatible support minima have
support-preserving restoration lower bounds at `ε+δ`; uncertainty in only the
anchor-core entry has the sharper lower scale `ε+3δ/8`. Both models match the
central exact-observation minimum at radius zero and have origin minimum `m+2`
for `m≥2`. Matching upper uncertainty laws are proved by original-label
middle-action compression of balanced consecutive bins, followed by bounded skew
completion and a clipped adjustment of only the core payoff. At
`0<ε+δ≤1`, both commitment classes have interval-support constants
`sqrt(3/1216)` and `5 sqrt(8/3)`. The fixed-share one-core model has constants
`sqrt(3/1216)` and `5` at `0<ε+3δ/8≤1`. These are existential compatible
witnesses. Exact global odd/even bin-error formulas are also proved. For equal
odd bins with m=h*s, the midpoint witness has exactly h residual actions and
exploitability r²/12 (1/h²−1/m²), with r=1/4: every row is bounded and anchor 0
attains that value. Balanced bins additionally satisfy the sharper finite bound
d≤r²/12 (1/h+1/m)² with support≤min(m,2h). The source's explicit
residual-payoff algorithm remains open.

The score-prefix reduction and fixed-tolerance conic characterization are proved.
For nonincreasing scores, every strict score threshold is an actual prefix, including ties and the empty
case. The displayed linear and quadratic constraints exactly characterize a
bounded skew residual completion and all original response inequalities; the
quadratics have explicit rotated-Lorentz representations. The q-system is proved
convex for a fixed tolerance and convex repertoire, including literal families
of linear inequalities. Fixed core/cross observations and normalized strategy
premises determine the full game model. Interval-conic extensions and numerical
separation/solver complexity remain separate.

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
