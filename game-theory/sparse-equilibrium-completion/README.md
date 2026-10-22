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
d≤r²/12 (1/h+1/m)² with support≤min(m,2h). The source's explicit within/across-bin residual-payoff construction is now proved in the source-explicit bin tranche below; its same matrix and exact rows are verified directly.

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
The zero-floor global sparse-output composition is proved below. Efficient flow
reconstruction, executable sorted separation and polynomial operation/bit-cost
clauses remain tracked gaps in SCOPE.md; whole-paper readiness is unestablished.

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
prove the paper's polynomial LP/flow or bit-cost guarantee. Efficient separation, polynomial sparse selection and source-specific
polynomial payoff reconstruction remain tracked in SCOPE.md. Native exact-source
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
explicit for exploitability/value. The zero-floor global sparse-output composition is proved below. Polynomial operation/bit guarantees remain open.


The initializer now computes physical consistency for admissible rational
parameters: M,η>0, nonnegative anchors, normalization, bounded endpoints and
ordered cross intervals are explicit proof fields; physical nonemptiness is not.
Its actual rational solver determines the Boolean branch of a genuine Decidable
instance for compatible real games. Initialization and the combined approximation
return None exactly for incompatibility. Returned fixed-dimension rational
q,K,D,B belong to the original class and have all responses at most U+η. With
nonempty full action type and ζ>0, L≤V≤U+η and shifted width<η+ζ. This is not
a parser validating arbitrary untrusted rational inputs. The original dense initializer supplies no polynomial-time bound; the sparse extension below uses the same physical decision.


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
running-time guarantee is inferred. Efficient sorted
separation/flow, polynomial arithmetic/bit bounds and
the canonical release gates remain open; the explicit bin construction is covered below.


An actual finite-support algorithm now handles fixed-anchor rational games and
interval observations. It enumerates all 2^m residual support masks and solves
the corresponding rational linear programs, then reconstructs rational residual
payoffs once at the original rho+eta. Every returned q satisfies the original
finite gap and physical repertoire. Its support is at most
min(m,k+H+card(I)+1), where H is the actual rational grid size and I indexes the
additional physical rows. In a normalized full game, total support is at most
min(k+m,2k+H+card(I)+1). The row term is necessary for arbitrary repertoires;
positive residual floors can force every residual action to remain supported.

For interval input, the program first recovers rational K,D at the original rho,
then exactly substitutes qD and fixed K into the original physical constraints.
Sparse output belongs to that original interval class and all responses are at
most U+eta. Automatic bisection retains L<=V<=U+eta and shifted width<eta+zeta
for positive zeta. The compatibility initializer produces actual fixed-dimension
rational q,K,D,B, with None exactly for incompatibility. Zero residual mass and
empty indices are included. This proof gives functional correctness, not the
paper's polynomial-time sparsification algorithm. The original global floor-grid entrypoint
returns its possibly dense output. The subsequent zero-floor global composition
now supplies sparse output; arbitrary extra physical rows and positive residual
floors are outside that sparse composition. The final rational LP point preserves
feasibility and support bounds; equality to an arbitrary original real witness's
individual moments or support is not claimed for that final point.


The source-explicit bin construction is now a literal rational program. It
decodes original action labels, coalesces the two central labels in odd bins,
uses cross-bin payoffs of opposite unit signs, and uses opposite 2/L payoffs
for the distinct centers within an even bin. Omitted rows use the closed
coefficient -(m-2j-1)/m; its equivalence to -t_j/r requires nonzero r, while
the implemented formula remains valid at r=0. Every actual rational residual
row has exactly zero response under the computed bin weights. The cast of
that same rational matrix has exactly zero response for all real r, by proved
homogeneity. Its entries are bounded and it is skew, including singleton bins.

For arbitrary positive bin lengths and total m>0, the actual same matrix with
r=1/4 gives residual support<=min(m,2h), anchor responses d and -d, and exact
error d=r^2/(12m^3)*sum_b L_b*(L_b^2-c_b), with c_b=4 for even lengths and
c_b=1 for odd lengths. The clipped core-only uncertainty theorem retains that
q and residual matrix whenever d<=epsilon+3delta/8. This replaces existential
residual completion in this construction; it does not supply a polynomial
generic flow/LP algorithm. The zero-floor global sparse-output composition is separate and described below.


The zero-residual-floor global program now returns an actual sparse rational
game and an actual additive value certificate. It first runs the global dense
search at e=epsilon/2, preserves its chosen p,K,D, then runs the actual sparse
finite-gap solver at that same e. True-game necessity supplies its input at
rho=U+e/3 without a first reconstruction loss. One sparse reconstruction gives
tau=rho+e with V<=tau<V+epsilon. Every game row is at most tau. Original anchor
floors and all anchor-incident intervals are retained; residual floors must be
literally zero. Positive residual floors may force full support and remain
covered by the separate dense floor program.

Residual support is at most min(m,k+H+1), full support at most
min(k+m,2k+H+1), with H the actual rational grid size at residual mass r and
eta=epsilon/2. The proved real bound is 2k+sqrt(2M/epsilon)+3. The first sparse
program stores (0,tau), which has no asserted epsilon width. The subsequent
computed certificate wrapper stores (tau-epsilon,tau), proves strict L<V<=U
and exact rational width epsilon, and leaves all game fields unchanged. Both
programs return None exactly on physical incompatibility when epsilon>0;
epsilon<=0 returns None without an incompatibility conclusion.

These are functional exhaustive programs with genuine computed decisions,
including empty, residual-only and zero-residual-mass cases. They do not
establish polynomial LP/flow or bit-complexity guarantees. The two rational
bin-label definitions now reuse the prior public, executable bin algorithms;
this removes duplicate proof-hoisting sites while retaining the same actual
label values and the unchanged protected dependency comparison.

## Instrumented compact certificates and source refinements

The finite-table certificate checker stores anchor weights, an injectively
labelled residual support, its weights and its square residual payoff table in
`Vector` data. Its Boolean acceptance is equivalent to the existing compact
certificate conditions and yields an actual normalized bounded skew game with
all response bounds, including omitted rows. The attached counter bounds unit
rational additions, multiplications, negations, arithmetic comparisons and
equalities. For an accepted certificate, with n=k+m and injective support-container length s,
the base counter is at most 128(nk+s²). Stored zero weights are allowed, so
the actual nonzero residual support can be smaller than s; fixed-share or anchor-floor checks use
at most 256(nk+s²), and adding chosen interval-observation checks uses at most
512(nk+s²). The witness stores k+s+s² rational scalars, at most k+2s²;
chosen anchor-incident observations use nk additional scalars. These are proved
source-level arithmetic ledgers. Table loading, index and Boolean bookkeeping,
raw-input validation, bit complexity and compiled machine time are outside
these counters. No polynomial-time LP or flow algorithm is established.

For η≥Mr and positive residual mass, preserving only the anchor and d extra
moments gives residual support at most k+d+1 and total support at most
2k+d+1. The proof supplies the explicit zero residual payoff block. Another
result shows that a score prefix dominates the numerical violation of every
subset, which strengthens the zero-threshold feasibility equivalence. A uniform
observation-cover corollary eliminates r and bounds total support by
min(n,2|C|+ceil(sqrt(M/η))) for every supplied cover, including a minimum one.
It does not compute that cover or transport an executable program through it.

The dense rational allocation program also returns a certified global bracket
for arbitrary nonnegative coordinate floors: L<V≤U, U−L=ε, with an actual
compatible game whose every response is at most U. Positive residual floors
are retained and can force dense support. The separate zero-floor sparse
program retains its own proved support guarantee.

The complete original-source coverage table, including remaining algorithmic
and mathematical packaging gaps, is in WHOLE-PAPER-COVERAGE.md. These additions
passed all12 native gates at f3c300572e22fb88de71183aee09ccc66785c3da,
with the retained-source qualification recorded in VERIFICATION.md. The later878941b
source corrected that inventory and passed all12 native gates. The current59
additions have their own source-retention corrections and require their own
complete exact-source receipt. No registry or journal submission is authorized or made.

## General payoff bounds and actual worst-case support

The 43-proof follow-on adds payoff rescaling, general-M upper and hard-instance
lower bounds, and actual attained per-instance support minima and their attained
worst-case maximum. For every k≥2, m>0, M>0 and 0<η≤M, in both fixed-anchor and
minimum-anchor-share classes, the maximum of those minima lies between
`(sqrt(3/1216)/2) * min(k+m,k+sqrt(M/η))` and
`2 * min(k+m,k+sqrt(M/η))`. The hard input is an actual finite-label scaled clone
game; responses, anchor commitments and support cardinality are transported
through an equivalence. The zero game only establishes nonemptiness.
`worstCaseSupport_sharp_general` proves the two-sided bound.

`PhysicalAnchoredWitness`, `AnchoredSupportProblem`, `physicalMinimumSupport` and
`supportProblemMinimum` quantify over actual bounded skew completions and
normalized strategies satisfying every response inequality. Existence of their
least support is proved from original feasible data. `worstCaseSupport` takes
the maximum over all such problems using the proved finite cardinality cap.
`supportProblemMinimum_observation_invariant` proves that the original feasible
certificate does not affect that minimum when observed K,D and floors agree;
`anchored_support_problem_representation` represents every raw feasible input.
These extrema use genuine classical predicates and do not provide an executable
optimizer or a polynomial-time decision procedure.

At the historical43 source, the package had246 mathematical modules,953 source theorem audits and843
protected selected contracts. Strict scratch compilation and independent
internal AI mathematical review cover the43 additions. Final integrated builds,
separate protected identities, altered-helper rejection, exports and kernel
checks require a new immutable exact-source receipt. Those predecessor receipts
remain evidence for their own source only.

## Executable rational cut checks and the source-scale allocation mesh

The current follow-on adds59 proofs in17 mathematical modules:45 cover actual
balanced sorting, original action labels, running-sum prefix scanning and raw
or interval perspective cut checks;14 cover the allocation step proportional to
`epsilon/(M*k)` and its actual dense floor-search output. The resulting package
has263 mathematical modules,1012 source theorem axiom audits and902 selected
protected contracts. Independent internal AI mathematical reviews cover these
additions; these are not human or external peer reviews. Only an immutable report for this candidate's complete source certifies the
checks named in that report. Reports are stored outside the frozen package.
A predecessor's receipt only certifies that predecessor.

`rationalSortedCutCheck` computes a descending score order and scans every prefix
until a violation occurs, carrying mass and payoff sums. For nonnegative M and
weights, `rational_sorted_cut_check_iff` proves its returned Boolean is true iff
all original cuts have violation at most delta. The bound
`m*(Nat.log2 m+2)+1` is the returned same-program **comparison count**: sorting
score comparisons plus quadratic prefix comparisons. It excludes arithmetic,
effective-score formation, equality guards, moment formation, getter and
administrative work, bit operations and machine runtime. No stability of sorting
or equality with the entire upstream mergeSort algorithm is asserted.

`rational_perspective_cut_check_iff` uses candidate-dependent H/q scores with
zero-mass H=0 explicitly required. `rational_interval_cut_check_iff` earns that
condition from the actual linear perspective bounds and forms H as sum(p*V).
The returned Boolean checks the quadratic cut component. Other linear, anchor,
core and global zero-row guards remain separate. It does not return a violating
subset or separating hyperplane; those outputs and full candidate-guard
composition remain open. M>=0 suffices for this cut checker; the existing
interval completion equivalence retains its explicit M>0 assumption.

For M>0, epsilon>0 and k>0, `rationalSourceFloorAllocationStep` equals
epsilon/(6*M*k); the k=0
branch uses the previous safe positive step. The actual generated allocation-node
count is `(1+floor(6*M*k/epsilon))^k`, including nodes later skipped as inadmissible.
This is neither a count of feasible nodes nor an algorithm-time bound.
`rational_source_floor_certified_value` supplies an actual compatible dense
rational game, all row bounds and a global interval of exact width epsilon.
No additional reconstruction error eta is hidden in that width. The older sparse
floor program still uses its conservative k+1 step; this dense variant does not
silently replace it or prove arbitrary-repertoire sparsification.

Source-inventory correction: authenticated compiler list recipes, including
logical/runtime length contexts, now retain precise supporting contexts for53
historical declarations. The existing finite-equivalence choice recipe is also
expanded through Trunc.out, Quot.out and Classical.choose for its exact19 users;
Nodup/Pairwise/list membership contexts are assigned to their actual affected
subgroups. These are source-retention corrections. Historical build, protected
comparison and kernel receipts remain evidence for their own source; the new
candidate requires its own checks. The literal Unit=PUnit alias additionally
receives its exact42 missing historical contexts; newly added Unit users carry
the same PUnit support. The specialized WellFounded.Nat.fix recipe is retained
for its exact final-trace new-target group, distinct from generic WellFounded.fix.
No blanket assignment to all1012 targets is
made, and the generic comparator, permitted axioms and dependency pins are
unchanged.

Whole-paper readiness remains false. Remaining work includes explicit violating
cuts, full candidate guards, arithmetic and bit complexity, polynomial rational
LP/flow guarantees, efficient sparse vertex selection and executable arbitrary
cover transport. Native macOS checks do not establish canonical Linux sandbox,
rendering, release-role or editorial readiness. No submission is authorized.
