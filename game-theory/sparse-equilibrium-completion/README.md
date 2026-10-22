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
response bound. The central geometric proof is existential over reals. The rational algorithm
below now computes completions; polynomial complexity remains open. Definitions and all proof
helpers have stable public exposed declaration names. The theorem map, including
completed results and remaining rational algorithm and operation/bit-cost work, is in [SCOPE.md](SCOPE.md).

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
premises determine the full game model. Interval-conic algorithm extensions and numerical
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

The interval and graph-cover tranche proves exact perspective recovery at fixed
q,K, arbitrary original-vertex cover sparsification, and weak-cover sparsification
with the explicit maximum interval-loss penalty β_C r. The maximum has an
inserted zero and agrees with the ordered-pair convention under reverse interval
symmetry. Cover probabilities, incident entries and responses remain unchanged;
original residual-support containment and declared extra moments are preserved. See SCOPE.md
for hypotheses and the remaining rational algorithm, executable separation and cost gaps.
These results extend the source mathematical coverage; integrated review and an
exact-source receipt must identify the tested bytes before a verification claim.

Joint interval geometry now includes variable q,V,K, declared repertoire
constraints and candidate-dependent positive-mass threshold separation. General
compact-class optimistic values and their support-budget restrictions attain
actual minima and satisfy the endpoint perturbation bound. Actual anchor-clone
games and universal sparse upper witnesses give the quantified joint-k order.
Finite-grid gap correctness, exclusion and monotonicity are proved over the reals.
The remaining sparse-output selection, source-specific flow construction, executable sorted
separation and operation/bit-cost clauses are tracked in
SCOPE.md; whole-paper and submission readiness remain unestablished.

The algorithm tranche proves an actual computable rational certificate checker,
compact attained fixed/gap optima and the additive enclosure W≤V≤W+η.
Perspective-grid feasibility yields an actual normalized interval-compatible game
at ρ+η, including zero-mass rows. Floor-preserving anchor round-down and transfer
to a specified residual action yield a finite allocation grid, exact normalization,
L1 error≤2kδ and actual optimistic-value bound V≤Vgrid≤V+2Mkδ.
Conditional rational bisection has exact halving, bracket and witness contracts;
the generic version retains an explicit decider input. The rational elimination
tranche below supplies an actual decider for finite rational linear repertoires.
Polynomial bit-cost guarantees remain open.

Feasible gap points can also be sparsified without a second tolerance slack:
the original anchor and H call moments are preserved, and actual normalized
completed witnesses have residual support≤min(m,k+1+H) at ρ+η. The interval
version freezes the recovered anchor data first. Arbitrary extra repertoire
constraints are not asserted to survive this compression.

The computable rational grid uses H=Nat.sqrt(Nat.ceil(Mr/η))+1, with an exact
proof of admissibility and H≤sqrt(Mr/η)+2 on nonnegative valid input. This H can
differ from the canonical real grid count. Rational nodes, calls and envelope
agree with the real definitions by proved cast contracts. A genuine finite
rational checker validates a supplied gap point and acceptance yields an actual
normalized bounded skew game under explicit premodel premises. The elimination tranche now strengthens this supplied-point theorem with actual
rational strategy and payoff reconstruction, as described below.


The rational elimination tranche supplies a total exact finite rational LP
feasibility algorithm, including empty and inconsistent systems. Structural
Fourier–Motzkin elimination returns rational coordinates, and its failure is
proved equivalent to infeasibility over both rationals and reals. The literal
gap matrix has 2m+2+k+H rows before the supplied rational linear repertoire is
appended. A separate matrix LP returns actual rational bounded skew payoffs.
Zero-weight residual rows retain their constraints.

`rationalGapApproximation` combines this decider, bisection and payoff
reconstruction. Under the explicit bounded rational premodel, M>0, η>0 and a
nonempty residual repertoire, it returns rational q,B and a bracket [L,U].
The actual compact-class value satisfies L≤V≤U+η, with U−L≤M/2^n after n
steps. Upper feasibility at M is proved from the game premises; no LP oracle is
supplied. Returned data also satisfy the normalized full-game reconstruction
contracts and the declared repertoire. The resulting shifted enclosure has width
at most η+M/2^n. Fourier–Motzkin elimination may be exponential: this does not
prove the paper's polynomial LP/flow or bit-cost guarantee. Efficient separation, sparse-output selection and source-specific
residual payoff algorithms remain tracked in SCOPE.md. Native exact-source
verification must be tied to the frozen commit by its external receipt.


The actual rational interval program now encodes q,V,K and finite call epigraph
variables. Its matrix is proved equivalent over both Q and Real to the intended
constraints. For M,η>0 and p≥0, any compatible real completion at ρ forces rational program success;
with explicit endpoint containment and normalization, its returned game obeys
the original intervals and all response bounds at ρ+η. The augmented program below also preserves finite physical q,V,K constraints
and implements actual interval value search.

For fixed observations and finite rational linear repertoires, automatic rounds
n=Nat.log2(Nat.ceil(M/ζ))+1 yield an actual returned certificate and value bracket
of shifted width<η+ζ for ζ>0. The Boolean checker validates original anchors and
repertoire membership. This full support container may include zero weights;
it does not certify the paper's sparse-output algorithm or polynomial cost.


The augmented interval solver preserves finite rational linear constraints R on
physical q,V,K, independently of epigraph auxiliaries. For positive M,η,
nonnegative normalized anchors, bounded consistent intervals and a nonempty
compatible game class, its bisection program automatically succeeds. The class
contains all original q,D,K,B satisfying intervals and R(q,qD,K); its actual
exploitability optimum is attained. The returned rational game gives L≤V≤U+η
and automatic shifted bracket width<η+ζ for ζ>0. Physical consistency assumes
neither a tolerance bound nor solver success. Full action nonemptiness is
explicit for exploitability/value. Sparse-output selection and polynomial operation/bit guarantees remain open.


The initializer now computes physical consistency for admissible rational
parameters: M,η>0, nonnegative anchors, normalization, bounded endpoints and
ordered cross intervals are explicit proof fields; physical nonemptiness is not.
Its actual rational solver determines the Boolean branch of a genuine Decidable
instance for compatible real games. Initialization and the combined approximation
return None exactly for incompatibility. Returned fixed-dimension rational
q,K,D,B belong to the original class and have all responses at most U+η. With
nonempty full action type and ζ>0, L≤V≤U+η and shifted width<η+ζ. This is not
a parser validating arbitrary untrusted rational inputs. It supplies neither
sparse output nor a polynomial-time bound.


The floor-constrained global allocation algorithm now executes rational grid
enumeration, physical consistency checks, interval value search and min-upper
selection. Its actual real game class varies both anchor and residual weights
with the original core/cross intervals and all declared nonnegative floors.
The global minimum V is attained. For ε>0, the total program chooses η=ζ=ε/3
and δ=ε/(6M(k+1)), returns actual rational game data and τ=U+ε/3 with
V≤τ<V+ε, and preserves every original interval and floor. A residual coordinate
receives removed mass when m>0; an existing anchor is the reservoir when m=0.
The fully empty class returns None. For positive ε, None is equivalent to
physical incompatibility and a genuine solver-derived Boolean decision is
provided. Parameters still carry explicit admissibility proofs. Global search
requires the literal floor-only repertoire; arbitrary extra R is supported by
the fixed-anchor algorithm, without an asserted rounding-invariance theorem.

These are functional correctness results. Explicit lists contain
(1+floor(1/δ))^k nodes; Fourier–Motzkin may grow exponentially. No FPTAS
running-time or sparse-output algorithm guarantee is inferred. Efficient sorted
separation/flow, polynomial arithmetic/bit bounds, actual sparse selection and
the paper's explicit within/across-bin payoff construction remain unformalized.
