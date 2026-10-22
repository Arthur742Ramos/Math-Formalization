# Whole-paper source coverage

Source: *Sharp Sparse Witnesses for Incomplete Zero-Sum Games*, manuscript
revision `1a424f297925294ae5818ff1ee7512304af1d460`. The original-source audit
counts 27 formal environments (26 labeled and one unlabeled) and 32 additional
substantive claim groups. These tables distinguish mathematical existence,
actual functional programs and arithmetic/bit-cost assertions.

The 71-proof tranche passed all12 native gates at predecessor
f3c300572e22fb88de71183aee09ccc66785c3da, with a historical retained-source
completeness qualification. The later878941b source corrected its Find/WF/Classical contexts and passed
all12 native gates. The current59 additions also correct later list and finite-
equivalence recipe omissions and require their own exact-source evidence;
predecessor checks do not certify altered source or whole-paper readiness. The no-grid zero-block result assumes
positive residual mass; earlier separate results cover zero-mass branches.

## All 27 formal result environments

“Covered” below means the actual mathematical statement or stated functional contract, subject to its explicit hypotheses. Algorithm/cost clauses are separately qualified. The integrated additions do not retroactively change the frozen baseline.

| Source result | Actual coverage and declarations | Precise remaining scope |
| --- | --- | --- |
| `sp:thm:sparse` — Sparse approximate completion (sections/main_theorem.tex:1) | Canonical-H mathematical theorem, all mass branches, original support and anchor moments, d extra moments, general k+d+1+H and exact k+d+H; total finite-cardinality caps. `normalized_sparse_witness_extra_moments_all_mass`, `normalized_exact_sparse_witness_extra_moments_all_mass`. Integrated `large_tolerance_sparse_moments` improves arbitrary starting tolerance to k+d+1 when r>0 and eta>=Mr. | No source-faithful executed supplied-input compression wrapper with canonical sharp counts and returned original moments/zeros. Generic executed gap support search is a different correct contract. Polynomial LP-vertex/flow construction remains open. |
| `sp:lem:flow` — Residual completion criterion (sections/completion.tex:4) | Exact bounded-skew completion iff global guards and all weighted cuts, including zero-mass rows; stronger zero-total-mass/M=0 cases. `weighted_completion_iff`, `cuts_dual_bound`, `cuts_weighted_completion`; actual rational matrix reconstruction in `rational_residual_completion_complete`. | Existence and rational reconstruction are proved; no executed capacitated-flow algorithm/complexity. The source proof itself already includes separation and level-set duality. |
| `sp:lem:call` — Quadratic call envelope (sections/completion.tex:35) | Exact quadratic call-envelope equivalence and positive-support score cap. `cuts_iff_call_bound`, `supported_score_cap`. | The source integrated-score curve Lambda is an unused alternate proof ingredient, not a missing envelope conclusion. |
| `sp:lem:grid` — Finite-grid implication (sections/sparsification.tex:11) | Actual quadratic interpolation, truncated last interval and canonical ceiling-root bridge. `finite_grid_implication`, `canonical_grid_implication`, `quadratic_grid_identity`, `truncated_grid_error`. | Executed rational programs use a different valid computable H; do not identify that H with canonical ceiling sqrt. |
| `lb:thm:dense` — Unique dense equilibrium-compatible completion (sections/rigidity.tex:25) | Uniform and arbitrary-positive-target fixed-share strategy/completion rigidity. `uniform_two_anchor_dense`, `bounded_two_anchor_fixed_share_rigidity`, `tight_prefix_completion_unique`. | No central mathematical conclusion missing; stronger numerical observation margins are not separate contracts. |
| `lb:thm:universalrigidity` — Two-anchor inverse rigidity (sections/rigidity.tex:97) | Any positive target of mass1/4, two minimum shares forced tight, unique strategy and transitive residual block. `bounded_two_anchor_minimum_share_rigidity`, `two_anchor_target_feasible`. | Actual construction bounded in[-1,1]; literal finer margins5/6 and1/3 are not packaged separately. |
| `lb:thm:support` — Support lower bound (sections/rigidity.tex:151) | Exact finite m,h lower bound and 3/1216 inverse-square specialization from genuine cumulative quantization. `uniform_fixed_share_support_lower`, `uniform_fixed_share_inverse_square`, `finite_subset_quantization_bound`, `sparse_cumulative_quantization`. | No central mathematical gap; variable-share endpoint partition is handled separately. |
| `lb:thm:upperrate` — Matching inverse-square upper rate (sections/rigidity.tex:172) | Exactly h original labels for equal odd bins, exact attained exploitability r²/12(1/h²−1/m²). `uniform_odd_midpoint_witness`, `binned_odd_support_exact`, `explicit_binned_game_witness`. | The later explicit-payoff implementation now supplies the source matrix; existence is not substituted for it. |
| `lb:thm:allm` — A uniform sparse upper bound, without parity conditions (sections/rigidity.tex:199) | Balanced bins without parity restriction; support<=min(m,2h), exact parity error and both source error upper bounds. `balanced_finite_game_witness`, `balanced_game_witness`, `explicit_binned_game_witness`. | No central mathematical gap. |
| `lb:cor:rate` — Sharp order of approximate support complexity (sections/rigidity.tex:220) | Actual attained residual-support minimum, zero=m and matching constants on0<epsilon<=1. `uniformMinimumResidualSupport_attained`, `uniformMinimumResidualSupport_zero`, `uniformMinimumResidualSupport_fixed_sharp`. | No infimum/surrogate replacement. |
| `lb:thm:naturalapprox` — Robust support obstruction for two lower bounds (sections/rigidity.tex:236) | Actual minimum-share residual minimum and matching small-positive-tolerance law; exact origin rigidity. `uniformMinimumResidualSupport_natural_sharp`, `uniform_minimum_share_inverse_square`. | Tolerance restriction epsilon<=1/1024 is retained. |
| `UNLABELED:uniform-total-support` — Uniform total-support law for two minimum shares (sections/rigidity.tex:267) | Actual attained total-support minimum, both commitment classes, origin=m+2 and constants sqrt(3/1216),5 for0<epsilon<=1. `uniformMinimumTotalSupport_sharp`, `uniformMinimumTotalSupport_zero`, `uniform_witness_total_support_card`. | This is the sole unlabeled theorem-like environment and must remain in the result count. |
| `sp:cor:sharpk` — Sharp dependence on the number of anchors (sections/joint_support.tex:1) | Every exact-feasible normalized instance has the upper witness; actual mandatory-clone family forces source lower constant in both commitment classes for every k>=2. `joint_anchor_support_order_general`, `cloned_uniform_total_support_lower`, `normalized_joint_support_upper`. | The integrated43 tranche constructs actual attained minima and their attained worst-case operator; general-M payoff rescaling and actual finite clone family prove `worstCaseSupport_sharp_general`. Exact-source verification remains external to this source. |
| `sp:thm:gap` — Linear programming gap decision (sections/algorithms.tex:4) | Actual rational LP decision, true Real-to-Q necessity/completeness, rejection excludes true compatible games, and actual rational q,B returned at rho+eta. `rational_gap_solve_none_excludes_real_completion`, `rational_gap_algorithm_sound`, `rational_gap_algorithm_complete`, `rational_gap_encoding_rows`. | Fourier–Motzkin may be exponential; no polynomial LP or flow claim. Executed H is Nat.sqrt(ceil(Mr/eta))+1, not literal source H. Extra trivial guard/normalization rows are counted honestly. |
| `sp:cor:certificate` — Compact witness and direct verification (sections/algorithms.tex:30) | Committed compact certificate iff/full-game checker. Integrated71 adds actual finite tables, connected Rat-operation ledger, fixed/floor commitments, selected interval checks, storage and accepted-input rates. Committed `compact_block_certificate_iff`, `RationalCertificate.accepted_full_game`; integrated `rational_counted_certificate_full_game`, `rational_counted_interval_fixed_bound`, `rational_counted_interval_fixed_valid_rate`. | Integrated unit-Rat arithmetic model only, not machine/bit/runtime-parser or arbitrary-R cost. The integrated71 passed all12 native gates at f3c300572e22fb88de71183aee09ccc66785c3da. The later878 checkpoint passed all12 native gates after its Find/WF/Classical correction. The current59 source also corrects later list and finite-equivalence recipe findings and binds its verification separately. |
| `sp:cor:fixedapprox` — Fixed-anchor additive approximation (sections/algorithms.tex:49) | Actual attained gap optimum W and game optimum V, W<=V<=W+eta, executable rational decision/bisection and logarithmic round choice, actual game/value bracket. `gap_original_infimum_eq`, `fixed_anchor_additive_value_enclosure`, `rational_certified_approximation_sound`, `rational_log_rounds_width`. | Polynomial coefficient encoding, LP/flow operations and end-to-end bit-time remain open. Round count alone is not polynomial total cost. |
| `sp:prop:interval` — Interval-anchor LP gap decision (sections/algorithms.tex:86) | Actual q,V,K,aux finite rational matrix and exact Q/Real equivalence; zero-q lower-endpoint recovery; actual normalized compatible returned game with one eta. `interval_gap_epigraph_iff`, `rational_interval_system_point`, `rational_interval_system_real_point`, `rational_interval_algorithm_full_game`. | Physical finite-linear R extension/value search is proved beyond source residual-only R. No arbitrary nonlinear R solver or efficient LP claim. |
| `sp:cor:gridp` — Additive approximation for a fixed number of anchors (sections/algorithms.tex:111) | Actual global floor class with varying p,q; rounding/L1/grid count; actual enumeration and selection; accurate tau. Integrated general-floor wrapper now returns actual global rational interval(tau−epsilon,tau). `optimistic_allocation_grid_bounds`, `rational_grid_tuples_length`, `rational_floor_approximation_global`; integrated `rational_floor_certified_value`, `rational_floor_certified_none_iff`. | Source FPTAS polynomial cost is unproved. The new dense source-floor variant uses epsilon/(6Mk) for k>0 with an explicit k=0 branch and actual all-node count; the older sparse variant remains conservative. No slice L is asserted globally valid. |
| `ext:thm:cover` — Sparse witnesses from a cover of the observation graph (sections/graph_noise.tex:22) | Arbitrary original finite vertices, actual cover predicate including constrained zeros; same shares/incident entries/responses, canonical support caps, extra moments and r=0 branch. Integrated uniform-ceiling corollary removes residual r. `arbitrary_vertex_cover_sparse`, `arbitrary_vertex_cover_exact`; integrated `arbitrary_vertex_cover_uniform_exact`. | Uniform corollary applies any supplied cover and hence a supplied minimum one, without minimum-cover finding. Its current public signature has d=0; extra-d uniform wrapper is still optional packaging. |
| `ext:cor:algorithm` — An additive algorithm for a supplied small cover (sections/graph_noise.tex:81) | Block-labelled actual interval/floor solver, enumeration, genuine physical decision, both residual/nonresidual branches. Integrated general-floor wrapper returns requested-width rational value interval. `rational_floor_approximation_none_iff`, `rational_floor_approximation_global`; integrated `rational_floor_certified_complete`, `rational_floor_certified_value`. | Computable arbitrary original supplied-C encode/decode adapter remains absent. Exact source(1+floor(6Mk/epsilon))^k slice bound differs from current k+1 rule. Polynomial per-slice/bit and FPTAS cost unproved. |
| `ext:prop:weakcover` — Sparsification with uncovered interval restrictions (sections/graph_noise.tex:131) | Actual arbitrary-C clipping, beta_C source ordered maximum with empty max0, same cover data/support/moments and rho+eta+beta_C*r. `arbitrary_vertex_subset_weak_sparse`, `arbitrary_vertex_subset_weak_exact`, `residual_loss_bound_ordered`. | Final strong-edge-threshold-cover corollary is a direct missing wrapper from least-upper-bound contracts; no new sparsification principle needed. |
| `ext:prop:stability` — Stability under interval perturbations (sections/graph_noise.tex:159) | Actual attained optimistic interval minimum and support-restricted minimum; ordered endpoint proximity yields both-direction delta stability. `optimistic_value_ordered_interval_stability`, `optimistic_support_value_ordered_stability`. | Nonempty compact strategy class/nonempty finite action type hypotheses remain explicit. |
| `ext:thm:noise` — Sharp support law with uncertain observations (sections/graph_noise.tex:205) | Both actual attained commitment-class support minima, sharp constants and origin; actual bin/core witnesses. `uniformMinimumIntervalTotalSupport_sharp`, `uniformMinimumIntervalTotalSupport_origin`, `explicit_binned_core_witness`. | Family-specific deterministic information theorem. Literal source h-selection differs from valid implemented selection; stated constants are proved. |
| `ext:cor:corenoise` — Uncertainty in only the anchor-core entry (sections/graph_noise.tex:297) | One clipped actual core entry, exact cross observations, e=epsilon+3delta/8, actual attained minima with c and5. `uniformMinimumCoreTotalSupport_sharp`, `uniform_core_adjust`, `explicit_binned_core_witness`. | Concrete m243/h9 exact11-support instantiation is not yet a theorem/control. |
| `cv:lem:prefix` — Only score prefixes are needed (sections/conic.tex:4) | All cuts iff score prefixes; integrated quantitative strengthening dominates every subset numerical violation by a prefix, and certifies arbitrary delta bounds. `cuts_iff_score_prefixes`, `threshold_is_score_prefix`; integrated `score_prefix_violation_dominates`, `cut_violation_bound_iff_prefix_bound`. | The new RationalSortedCutCheck computes a labelled rational order and a cached prefix Boolean check, with exact all-cut equivalence. Its same-program comparison bound excludes arithmetic/bit/getter cost and does not return a violated cut. |
| `cv:thm:soc` — Exact conic completion characterization (sections/conic.tex:19) | Exact bounded normalized game iff linear guards/anchors and literal rotated-cone prefix system; fixed-tolerance convexity. `normalized_known_anchor_conic_iff`, `weighted_completion_rotated_cones_iff`, `known_anchor_conic_system_convex`. | Executed rational sorting/permutation and Boolean cut checking are now proved separately. Encoded rational SOC solving, explicit cut output and flow programs remain open. Source explicitly does not promise exact boundary-conic polynomial bit complexity. |
| `cv:thm:interval` — Convex interval-anchor completion (sections/conic.tex:54) | Joint q,V,K convex exact interval system and finite candidate-dependent positive-score threshold characterization; zero-q cases included. `variable_core_interval_completion_iff`, `interval_perspective_system_convex`, `interval_system_iff_threshold_system`. | Actual candidate-dependent sorted-prefix Boolean cut checking is proved for rational perspective variables; zero-mass moments follow from linear bounds. Explicit separating-cut output, full guard composition and O(m log m) arithmetic/bit proofs remain open. Literal interval all-subset rotated-cone rewrite is an easy missing wrapper of scalar identity, not a missing convexity/completion theorem. |

## What the integrated additions close

### No-grid large-tolerance bound: positive residual mass only

`large_tolerance_sparse_moments`, `large_tolerance_sparse_witness` and `normalized_large_tolerance_sparse_moments` formalize the optional final paragraph of `sparsification.tex`. For **r>0** and `M*r<=eta`, compress only the k anchor and d extra moments, obtaining at most k+d+1 original support labels. The actual original lower residual payoff bound implies every residual score is at most rho+Mr. The new explicit residual block is **zero**, so every original residual row, including zero-weight rows, is at most rho+eta. Anchor moments/responses are retained. The normalized theorem gives total support at most2k+d+1 and a bounded skew full matrix.

The statements strengthen the needed assumptions to M>=0 and require no original residual skewness because only its lower bound is used. **They do not quantify r=0.** The existing all-mass main theorems already handle r=0 separately; that does not make this new zero-block theorem an all-mass theorem. No executable compressor is claimed.

### Quantitative prefix domination

`score_prefix_violation_dominates` proves the stronger numerical statement in the proof of `cv:lem:prefix`: every subset violation is no larger than a score-prefix violation. `cut_violation_bound_iff_prefix_bound` handles every real bound delta, not just zero. The square-completion argument requires M>=0, q>=0 and Antitone scores, but no mass normalization or sign assumption on r. Empty/tied/zero-weight cases are included. The current rational follow-on executes a labelled sort and cached scan with the comparison bound stated below; its arithmetic and bit cost remain separate.

### Uniform supplied-cover ceiling bound

`cover_residual_mass_le_one` derives r<=1 from the actual nonnegative normalized strategy. `gridSize_uniform_mass_bound` proves canonical ceiling-root monotonicity. `arbitrary_vertex_cover_uniform_exact` returns an actual compatible witness on original labels with total support at most `min(card(nu),2*card(C)+ceil(sqrt(M/eta)))`, retaining cover shares, incident entries and cover responses. It works for any supplied cover, so it applies to a supplied minimum cover without computing one. The new public wrapper sets d=0; an extra-d wrapper can be added by the same argument.

### Returned global bracket for arbitrary nonnegative floors

`rationalFloorCertifiedApproximation` is an actual `Option.map` over the dense global floor program. It keeps p,q,D,K,B unchanged and returns `U=oldU+epsilon/3`, `L=U-epsilon`. Its four theorems prove actual output origin, completeness, physical-incompatibility iffNone for epsilon>0, original-floor class membership, every original row<=U, strictL<V<=U and width exactlyepsilon. It handles positive residual floors and carries **no sparse support claim**. It never treats the selected slice lower endpoint as a global lower endpoint. epsilon<=0None is not an incompatibility certificate. Value statements explicitly require a nonempty full action type.

### Direct compact-certificate arithmetic and storage

Write n=k+m, s for the supplied support-container length and N=n*k+s². The table program uses actual Vector/Array data, List.ofFn traversal, finite labels and an intrinsic `(value,ledger)` computation. Classical inverse/asCertificate definitions are proof-layer reconstruction only. The 51-proof tranche proves checker acceptance iff the existing full compact-certificate conditions and actual full-game soundness. It hoists mass/threshold work, checks omitted rows, adds k fixed-allocation or floor comparisons, and adds2nk chosen-K/D endpoint comparisons for interval observations.

| Instrumented checker | Every typed input | Accepted normalized input (Rate7) |
| --- | --- | --- |
| Base | ledger<=64(1+N) | ledger<=128N |
| Fixed shares or anchor floors | ledger<=128(1+N) | ledger<=256N |
| Interval observations plus fixed shares/floors | ledger<=256(1+N) | ledger<=512N |

Accepted normalization forces k+s>0, hence N>=1; it absorbs the additive constant. The accepted-input rates do not assert a zero-cost rejection bound for invalid N=0 inputs. Scalar storage is exactly k+s+s²<=k+2s², in addition to label indices; selected observations contain nk scalars.

The cost model counts **unit rational arithmetic/order/equality operations**. It excludes Nat indexing, Boolean/list/Vector administration, data loading, proof/label-injectivity validation, raw-input parsing, rational bit lengths, compiled machine operations and memory/wall-clock costs. Conjunction counts conservatively permit all generated tests despite short circuiting. Arbitrary repertoire constraints need their own verifier/cost. These are genuine limits of the stated arithmetic model; they neither prove polynomial LP cost nor invalidate the narrower arithmetic certificate claim.

## The 32 additional source-claim groups

This preserves the earlier audit’s claim-group enumeration. “Direct wrapper” denotes an absent named composition, not an absent central mathematical principle.

| # | Source claim group | Current status after integrated71 |
| --- | --- | --- |
| 1 | Every finite nonempty skew game has a symmetric equilibrium; unrestricted compatibility is automatic. (main.tex:99-101) | No project equilibrium-existence/minimax statement found. This standard background claim is separate from the completed conditional compatibility theorems. |
| 2 | General M sharp joint support law with sqrt(M/eta). (main.tex:119-125) | Integrated43: `joint_anchor_support_scaled_order_general` and `worstCaseSupport_sharp_general` prove general-M bounds for all k≥2,m>0,M>0,0<eta≤M; actual physical game lower family and attained worst-case operator. |
| 3 | x^T A x=0, nonnegative exploitability and symmetric epsilon-Nash interpretation. (main.tex:235-241) | Weighted skew cancellation, actual finite max exploitability and nonnegativity are formalized. No bimatrix Nash/deviation definition and equivalence theorem appears in the package. |
| 4 | Partial-mass integrated-score curve Lambda and its call variational identities. (completion.tex:45-67) | Cuts/call conclusion proved directly. No need to report the absent Lambda definition as failure of the envelope theorem. |
| 5 | Strictly increasing truncated quadratic nodes and terminal node. (sparsification.tex:8) | Grid interval coverage and terminal equality used in exact sparse endpoint proof; source r>0 assumptions matter. |
| 6 | Quadratic chord identity, truncation and shifted-call interpolation. (sparsification.tex:30-53) | quadratic_grid_identity, truncated_grid_error, call_secant and finite_grid_implication. |
| 7 | Polytope vertex rank bound; exact endpoint equality; d extra moments. (sparsification.tex:63-96) | Caratheodory compression gives matching statements; no LP extremal vertex program/rank theorem is claimed. |
| 8 | When eta>=Mr, mass and k moments alone suffice, giving k+1 original support points without call constraints. (sparsification.tex:98-106) | **Integrated closed for r>0** by LargeToleranceWitness3; r=0 remains existing separate main-theorem branch. |
| 9 | Sharper uniform observed-entry strict bounds 7/12 and core 1/6. (rigidity.tex:22-23) | Required bounded-payoff result [-1,1] is proved; these sharper margins not separately declared. |
| 10 | Anchor formulas, exact exposing expansion and finite odd-tail weight formula. (rigidity.tex:44-74) | two_anchor_responses, prefix_exposing_identity, uniform_exposing_weight and stability proofs. |
| 11 | Arbitrary target exposing weight <=2r, positive before final action and positive beta; margins5/6,1/3. (rigidity.tex:111-116) | exposing_moment_bounds, exposing_moment_positive and actual observation bounds prove the construction; literal finer margin contracts absent. |
| 12 | Quantitative prefix energy E<=z(r+1/p). (rigidity.tex:144-148) | Fixed-share and minimum-share stability; both derive from actual full-game responses. |
| 13 | Constant-run quantization and cubic Jensen. (rigidity.tex:163-169) | finite_subset_quantization_bound, sparse_cumulative_quantization; no assumed contiguous support. |
| 14 | Source explicit odd/even bin payoffs, original-label weights and parity error. (rigidity.tex:207-218;graph_noise.tex:244-269) | Computed rational matrix, same-bin +/-2/L, cross-bin orientation and omitted scores; all rows exactly zero, exact parity moment loss. Not an existential substitute anymore. |
| 15 | Simplex gap LP has a sparse vertex, general constraints/floors affect bound. (algorithms.tex:28) | GapSparse and RationalSparseGapSearch prove sparse completion at original rho+eta, with extra feature/row counts. Executed search enumerates2^m supports; no vertex selection or polynomial claim. |
| 16 | Rational grid coefficient polynomial bit length; rational flow. (algorithms.tex:66-69) | Actual grid is an alternative valid computable H. Rational arithmetic output exists, but no encoding-height/bit-cost/flow complexity theorem. |
| 17 | O(mH+mk+k^2) interval LP variables/rows. (algorithms.tex:103) | rational_interval_row_count plus explicit finite variable equivalence give stronger literal finite formulas. No matrix construction/runtime bit bound inferred. |
| 18 | Freeze recovered D,K; sparse final tolerance uses only one eta. (algorithms.tex:105-107) | IntervalGapSparse and actual RationalIntervalSparseReduction/Algorithm preserve physical linear R and original intervals. |
| 19 | Min slice upper and lower endpoints yield a global value bracket; zero-residual slice treatment. (algorithms.tex:137-144) | **Integrated closed**: actual arbitrary-floor returned global bracket from General4; no reuse of old slice L. Zero-residual slice treatment already functional. |
| 20 | Minimum-cover number tau gives min(n,2tau+ceil sqrt(M/eta)), extra d. (graph_noise.tex:68-76) | **Integrated closed for d=0 and any supplied C** by CoverUniformBound3. Minimum-cover finder/operator and explicit extra-d uniform wrapper remain separate. |
| 21 | Uniform two-anchor observation graph has minimum constraint cover number exactly2. (graph_noise.tex:77-78) | Two-anchor observation model and lower-bound family are proved; no explicit minimum-cover-number2 theorem found. |
| 22 | d_ij is maximal distance from interval, beta_C lies[0,2M], empty max0. (graph_noise.tex:125-129) | IntervalProjection and IntervalLossMaximum/Order provide actual bounds, least upper bound and ordered/unordered equality. |
| 23 | Cover strong-loss graph d_ij>beta implies extra loss<=beta*r. (graph_noise.tex:134-135) | Actual weak-cover theorem and loss-bound universal property suffice; graph-specific implication not yet bundled. |
| 24 | Concrete bin count choice and clipped one-core adjustment. (graph_noise.tex:273-288) | Source exact h selection is not required by theorem; available upper proof uses a valid alternative grid size achieving C5 and C5sqrt(8/3). |
| 25 | m243,h9,delta1/5000: d91/1417176, corechange91/531441, exact11-action/245-row witness. (graph_noise.tex:313-320;main.tex:387-396) | Generic explicit bin/core theorem can instantiate this exactly; no current project theorem or executable guard includes these constants. No minimality11 claim should be added. |
| 26 | Every prescribed subset violation is dominated by some score prefix. (conic.tex:9-16) | **Integrated closed** by PrefixViolation3 for M>=0 without normalization. |
| 27 | Rational SOC coefficients preserved and tolerance must be fixed for convexity. (conic.tex:37-44) | Fixed-tolerance convexity and known-anchor scalar rotated-cone identity proved. Rational encoded-SOC object/count remains a direct wrapper; no conic bit-cost claim. |
| 28 | Joint interval SOC and candidate-dependent separation with positive q sorted by H/q. (conic.tex:68-87) | Threshold tests are exact finite geometry. Actual rational sorting/permutation and early-exit prefix cut checking are proved, including H/q and derived zero-mass moments. An explicit violating subset, complete guard composition and arithmetic/bit complexity remain open. |
| 29 | Positive floors on every residual probability force full support. (main.tex:332-333;graph_noise.tex:137-143) | Sparse theorems correctly exclude floor-independent compression; value algorithms retain floors. A direct cardinality lemma is optional bookkeeping. |
| 30 | Figure m729 deterministic formula evaluations and support comparisons. (main.tex:280-291) | Generic theorems certify mathematical formulas. No figure data/plot byte audit performed from the nine TeX files. |
| 31 | Statistical coverage, causal identification, exact optimal constants, improved cover dependence and degenerate conic bit complexity. (main.tex:301-309,343-354,360-367;conic.tex:90-92) | Not missing proved paper results; do not manufacture proofs/criticism or add statistical/computational promises. |
| 32 | External exact/numerical artifact implementation history and solver behavior. (main.tex:376-410) | Existing Lean verifies independent mathematics/functions. Original prototype/code fidelity, floating solver statuses and external literature comparisons require separate artifact/literature audit; no claim of such inspection here. |

## Remaining gaps, by kind

### Mathematical strengthening and direct-corollary packaging

- General-M quantified joint bounds and actual worst-case support law are integrated in43 proofs; their exact-source mechanical verification must be bound to the new candidate.
- Actual per-instance attained minima and the attained worst-case maximum are constructed. Observation invariance and raw-input representation justify the feasibility-certificate packaging. Polynomial LP/flow/bit-cost assertions remain open.
- The uniform family’s **minimum** constrained-edge cover number exactly2 is not an explicit graph theorem. The threshold-strong-edge cover implication for weak constraints is also an unbundled direct corollary.
- An explicit interval all-subset rotated-cone/rational representation wrapper, sharper numerical observation margins, and the standard symmetric epsilon-Nash/deviation-definition bridge remain small separate formalization items. These are not missing central completion/rigidity proofs.
- The source concrete245-action example (m243,h9,delta1/5000, error91/1417176, core change91/531441, exact11-support witness) is not instantiated or executed in the current Lean project. Generic explicit-bin/core formulas make this tractable. No claim that11 is minimal should be added.

### Functional algorithms and exact source constants

- A specialized executed **supplied feasible input** compression routine should preserve its original support, anchor/extra moments and the literal canonical k+1+H/general or k+H/exact count. The current rational finite-mask gap algorithm correctly preserves its declared linear constraints but uses an alternative actualH and counts extra rows; its returned output contract is not the original-input theorem’s full preservation contract.
- The supplied arbitrary original vertex subset C still needs an executed finite relabel/encode/decode adapter to the block-labelled solver and returned game. Classical geometric coverEquiv proofs are not that runtime adapter.
- Source exact cover-grid slice count uses spacing epsilon/(6Mk) for k>=1; the existing automatic program uses epsilon/(6M(k+1)). Its accuracy is proved but its larger count must not be silently identified with the source constant.
- Rational positive-effective-score sorting, tie grouping and prefix scan are not executed/formally costed. The candidate-dependent finite threshold characterization and integrated quantitative prefix theorem are geometric correctness foundations.
- Returning rational Farkas multiplier data would enable an external checker for rejection. Current exact None iffReal-infeasible and true-game exclusion theorems are genuine and do not assume an LP oracle; the paper specifies no particular Farkas payload API. Treat such an output as a useful extension, not a missing feasibility theorem.

### Operation, bit and solver complexity

- No polynomial rational LP solver, coefficient-height/encoding-growth analysis, polynomial bit bound or end-to-end fixed-anchor/fixed-k additive-FPTAS running-time theorem. Fourier–Motzkin and exhaustive2^m support enumeration can be exponential.
- No actual efficient capacitated-flow reconstruction or proved flow operation/bit bound. The m²-variable rational payoff LP is a real construction, but it is not a max-flow implementation.
- No polynomial sparse LP-vertex selection algorithm. Geometric Caratheodory existence and exhaustive support search do not imply one.
- No O(m logm) executed sorted-separation cost proof. Finite exact constraints and an explicit logarithmic threshold-round count do not supply the missing per-call costs.
- The integrated connected unit-Rat compact checker closes that declared **arithmetic-model** claim once exact-source verification passes. It supplies no machine/bit-cost or arbitrary-R-checking theorem.

### Explicit nonclaims and original-paper open questions

Statistical coverage, time-uniform confidence guarantees, sample complexity, causal identification, sublinear discovery, relative-error approximation, optimal exact support constants, improved cover-size dependence and a general classification of exact degenerate rational conic feasibility are not proved paper claims. They must not be turned into formalization blockers or inferred from deterministic compatibility. External literature comparisons and the original numerical/prototype code need separate audits; reading the nine TeX files does not authenticate those artifacts.

## Readiness and attribution

Whole-paper completion and submission readiness remain **false**. Predecessor f3c300572e22fb88de71183aee09ccc66785c3da passed all12 native gates, with the historical retained Nat.find/WF/Classical source-completeness qualification. The later878941b source corrected that inventory and passed all12 native gates for its general-M and attained worst-case results. The current59 additions also correct later list and finite-equivalence recipe findings and require separately bound exact-source evidence for both entrypoints, builds, axiom audits, protected comparison/negative controls, exports and kernels. Failed receipts remain failed; predecessor receipts certify only their own source.

The authenticated manuscript retains its anonymous-draft authorship statement. The user separately supplied Arthur/David/Ruy paper attribution, which remains distinct from unconfirmed human Lean authors/maintainers. No coauthor approval, external peer review or publication authorization is inferred. No submission or external publication action was taken.


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

At the historical878 source, the package had246 mathematical modules,953 source theorem audits and843
protected selected contracts. Strict scratch compilation and independent
internal AI mathematical review cover the43 additions. Final integrated builds,
separate protected identities, altered-helper rejection, exports and kernel
checks require a new immutable exact-source receipt. Predecessor receipts
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
