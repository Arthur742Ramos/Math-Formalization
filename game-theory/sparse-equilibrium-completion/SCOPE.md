# Theorem-to-Lean scope map

The source is the verified sparse-equilibrium-completion paper revision
`1a424f297925294ae5818ff1ee7512304af1d460`, not the earlier variance-design work.
All labels below refer to `paper/sections/` at that revision. Source blobs are
bound in `verification/paper-source-manifest.json`. Proof status is confined to
the actual declarations; unfinished targets have no placeholder Lean theorem.

| Paper result | Lean correspondence | Scope and remaining work |
|---|---|---|
| `sp:lem:flow`, completion.tex | `skew_weighted_sum`, `response_guard`, `completion_cuts_necessary`, `cuts_dual_bound`, `cuts_weighted_completion`, `completion_of_cuts_and_guards`, `weighted_completion_iff` | Exact necessity and sufficiency for arbitrary finite index types, nonnegative weights and arbitrary total mass, including zero weights and M=0. Finite layer-cake duality and compact-convex separation replace the source flow argument; compactCompletion handles every zero-weight row. This proves existence, not an executable flow algorithm. |
| `sp:lem:call`, completion.tex | `quadratic_duality`, `cuts_imply_call_bound`, `call_bound_implies_cuts`, `cuts_iff_call_bound`, `supported_score_cap` | Exact cut/call equivalence for `M>0`, nonnegative weights of mass `r`; forward bound even holds for every real argument. Direct positive-score subset and square completion replace the source's sorted partial-mass proof. Singleton cuts also prove the supported-score cap. |
| `sp:lem:grid`, sparsification.tex | `quadratic_grid_identity`, `truncated_grid_error`, `call_convex`, `call_secant`, `grid_interval_cover`, `finite_grid_implication` | Full shifted-call implication for any natural `H` with `Mr ≤ η H²`, `M>0`, `r≥0`, `η>0`. Support cap applies only at nonzero coordinates. This generalizes the source grid parameter; `gridSize_bound` and `canonical_grid_implication` prove the explicit `H=ceil(sqrt(Mr/η))` bridge. No mass assumption is needed for this interpolation implication. |
| `sp:thm:sparse`, main_theorem.tex | `finite_moment_recombination`, `finite_feature_compression`, `sparse_cut_witness`, `exact_sparse_cut_witness`, `canonical_sparse_cut_witness`, `game_sparse_cut_certificate`, `exact_game_sparse_cut_certificate`, `game_sparse_completion`, `exact_game_sparse_completion` | Proved: nonnegative mass on original labels, original-support containment, exact anchor moments/responses, support `k+1+H` generally and `k+H` at exact equilibrium, all relaxed cuts and global guards, from actual original block-game data. Caratheodory preserves all selected hinge values exactly, replacing the source's inequality/vertex argument at the same support count. The exact case preserves only `H-1` hinge values; the full skew-game bridge supplies the missing endpoint equality. The completed-game theorems reconstruct an entry-bounded skew residual block and prove all original block-game response inequalities. `normalized_sparse_witness` and `normalized_exact_sparse_witness` specialize to fully bounded normalized skew games, preserve literal anchor shares and moments, and bound total support by `2k+1+H`/`2k+H`. The paper-facing `normalized_sparse_witness_all_mass` and `normalized_exact_sparse_witness_all_mass` handle every r≥0, including the zero-mass and empty-residual cases, and state the finite minima explicitly: residual min(m,k+1+H)/min(m,k+H), total min(k+m,2k+1+H)/min(k+m,2k+H). `sparse_cut_witness_extra_moments`, `exact_sparse_cut_witness_extra_moments`, their game-certificate/completion and normalized wrappers preserve d arbitrary extra linear quantities without adding game anchors. `normalized_sparse_witness_extra_moments_all_mass` and `normalized_exact_sparse_witness_extra_moments_all_mass` combine all r≥0 with residual min(m,k+d+1+H)/min(m,k+d+H) and total min(k+m,2k+d+1+H)/min(k+m,2k+d+H). Algorithmic clauses remain open. No residual floors are imposed. |
| `lb:thm:dense`, rigidity.tex | `prefix_exposing_identity`, `strict_prefix_rigidity`, `tight_prefix_completion_unique`, `two_anchor_fixed_share_uniqueness`, `bounded_two_anchor_fixed_share_rigidity`, `uniform_target_score`, `uniform_exposing_weight`, `uniform_two_anchor_dense`, `positive_target_full_support` | Proved: bounded normalized two-anchor construction, target feasibility, all residual strategy coordinates and all missing residual edges uniquely forced under fixed shares. Uniform t/w formulas match the paper with zero-based residual labels. The arbitrary positive-target fixed-share theorem strengthens the uniform case. Compatibility premise is explicit and essential. |
| `lb:thm:universalrigidity`, rigidity.tex | `exposing_moment_positive`, `cuts_exposing_moment_le`, `bounded_two_anchor_minimum_share_rigidity`, together with `bounded_two_anchor_fixed_share_rigidity` for canonical feasibility/bounds | Proved: every strictly positive target of mass `1/4`, `m≥2`; minimum shares `3/8` are forced tight. Candidate residual mass is initially variable; transfer of actual cuts to target mass precedes the exposing-moment comparison. Both residual distribution and completion are unique. The canonical witness is normalized, bounded and feasible. |
| `lb:thm:support`, rigidity.tex | `two_anchor_fixed_share_stability`, `two_anchor_minimum_share_stability`, `finite_subset_quantization_bound`, `sparse_cumulative_quantization`, `uniform_fixed_share_support_lower`, `uniform_minimum_share_support_lower`, `uniform_fixed_share_inverse_square`, `uniform_minimum_share_inverse_square` | Proved: exact finite subset variance bound, genuine H+1 cumulative-mass partition, cubic power-mean inequality and quantitative support lower bounds. Fixed shares use all m+1 prefix endpoints and require `m≥2H+1` for the simplified bound `3/(1216(H+1)²)≤ε`. Minimum shares use m endpoints before residual mass is forced and require `m≥2(H+1)` for the same simplified bound. Both apply to actual bounded completions and all original response inequalities. |
| `lb:thm:upperrate`, `lb:thm:allm`, rigidity.tex | `bin_call_compression`, `bin_quadratic_loss_identity`, `bin_compressed_mass`, `bin_compressed_support`, `bin_compressed_affine_moment`, `bin_compressed_calls`, `binned_support`, `binned_mass`, `binned_call_contraction`, `binned_uniform_residual_completion`, `binned_exposing_loss`, `balancedLength_mass`, `balancedLength_cube_sum`, `binned_game_witness`, `balanced_game_witness`, `uniform_binned_upper` | Proved: explicit original middle labels (one when odd, two when even), mass/mean preservation, call contraction for either affine orientation, exact local second-moment identity, canonical exhaustive consecutive partition, balanced lengths, support at most min(m,2h), anchors d,-d with 0≤d≤βstar and d≤r²/(3h²), all residual responses≤0. Here r=1/4 in the game theorem. The completion exists by the proved criterion; it is not the source's explicit across-/within-bin payoff algorithm. The exact global formula is `binned_exposing_loss_exact`: r²/(12m³) times the sum over bin lengths L of L(L²−4) for even L and L(L²−1) for odd L. `binned_odd_support_exact` proves exactly h active original labels for r>0. `uniform_odd_midpoint_witness` proves the equal odd-bin specialization m=h*s with exactly h residual actions and exact exploitability r²/12(1/h²−1/m²), r=1/4; anchor 0 attains the bound. `balanced_finite_game_witness` proves d≤r²/12(1/h+1/m)² with support≤min(m,2h) and actual bounded completion. The source-explicit payoff algorithm is proved in the later bin-construction section. |
| `lb:cor:rate`, `lb:thm:naturalapprox`, unlabeled total-support corollary | `uniform_total_support_lower`, `uniform_sparse_upper_rate`, `UniformWitness`, `uniform_witness_total_support_card`, `uniformMinimumTotalSupport_attained`, `uniformMinimumTotalSupport_le`, `uniformMinimumTotalSupport_zero`, `uniformMinimumTotalSupport_sharp` | Proved: witness-wise total lower bound for every positive tolerance and matching existential upper bound for `0<ε≤1`. Actual fixed/minimum-share total support minima are nonempty, attained and minimal, equal m+2 at zero tolerance for m≥2, and bounded by `sqrt(3/1216) min(m+2,1/sqrt ε)` below and `5 min(m+2,1/sqrt ε)` above. The alternate upper proof uses general exact sparsification and preserves fixed anchor shares. It also gives residual upper count `3 min(m,1/sqrt ε)`. `uniformMinimumResidualSupport_attained`, `uniformMinimumResidualSupport_le`, `uniformMinimumResidualSupport_zero`, `uniformMinimumResidualSupport_fixed_sharp` and `uniformMinimumResidualSupport_natural_sharp` additionally prove the actual residual-minimum laws: c=`sqrt(3/1216)/2`, C=3, zero value m, fixed-share range `0<ε≤1`, minimum-share range `0<ε≤1/1024`, all for m≥2. The positive residual count is proved rather than assumed. Balanced middle-label bin witnesses are now proved in the preceding row; its source-explicit payoff algorithm is proved below. |
| `sp:cor:sharpk`, joint_support.tex | `cloned_anchor_response`, `cloned_score`, `cloned_uniform_dense_full_game`, `cloned_uniform_total_support_lower`, `normalized_joint_support_upper`, `joint_anchor_support_order`, `joint_anchor_support_order_general` | Proved as quantified worst-case upper/lower statements for actual normalized bounded games: every exact-feasible instance has an η-witness with the source upper constant 2, preserving its literal anchor allocation and residual-support containment; the exactly feasible identical-clone family forces the lower constant sqrt(3/1216)/2 in both fixed-share and lower-commitment classes. Every anchor is strictly positive, aggregation preserves all base responses, and full support is the actual anchor cardinality plus residual support. The explicit all-k wrapper quantifies every k≥2 (n=k−2); m>0 and 0<η≤1 are explicit. No worst-case supremum/minimum operator is assumed or claimed to have been constructed. |
| `ext:prop:stability`, graph_noise.tex | `interval_clip_endpoint_distance`, `exploitability_perturbation`, `optimistic_value_attained`, `optimistic_value_interval_stability`, `optimistic_support_value_stability`, `optimistic_value_ordered_interval_stability`, `optimistic_support_value_ordered_stability` | Proved for every nonempty compact strategy class contained in the simplex and genuine finite nonempty action type. Compatible skew entry-bounded matrix sets are proved compact and nonempty for valid reverse-consistent intervals; exploitability is the attained finite supremum of all row responses, and the optimistic value is the actual infimum of its matrix/strategy image. The minimum is attained. Projection preserves the same strategy and changes the value by at most δ in either direction. The support-budget set is proved closed as a finite union of coordinate subspaces, giving actual attained restricted minima and the same stability whenever the restricted class is nonempty. Ordered wrappers derive the source i<j endpoint condition using reverse symmetry. |
| `ext:thm:noise`, graph_noise.tex | `ClippedObservation`, `clipped_observation_interval`, `UniformIntervalWitness`, `uniform_interval_restore`, `uniform_interval_total_support_card`, `uniform_interval_total_support_lower`, `uniformMinimumIntervalTotalSupport_attained`, `uniformMinimumIntervalTotalSupport_le`, `uniformMinimumIntervalTotalSupport_lower`, `uniformMinimumIntervalTotalSupport_radius_zero`, `uniformMinimumIntervalTotalSupport_origin`, `uniformMinimumIntervalTotalSupport_sharp` | Proved: actual bounded normalized interval games, exact clipped-Icc interpretation, unchanged strategy/support under central restoration at ε+δ, and lower constant sqrt(3/1216) for every positive ε+δ. Both commitment classes have genuine attained minima; radius zero agrees with the exact-observation minimum; origin value is m+2 for m≥2. Dense central observations prove nonemptiness for ε,δ≥0. `uniform_core_uncertainty_upper` constructs actual compatible witnesses by balanced original-label bins and a clipped core adjustment. `uniformMinimumIntervalTotalSupport_sharp` proves the full existential sharp law for m≥2, ε,δ≥0 and 0<ε+δ≤1 with constants sqrt(3/1216) and 5 sqrt(8/3), for both commitment classes. This is a family-specific theorem, not a universal noise-sparsity theorem. The source's explicit residual-payoff algorithm remains separate. |
| `ext:cor:corenoise`, graph_noise.tex | `two_core_response_perturbation`, `UniformCoreWitness`, `uniform_core_restore`, `uniform_core_total_support_card`, `uniform_core_total_support_lower`, `uniformMinimumCoreTotalSupport_attained`, `uniformMinimumCoreTotalSupport_le`, `uniformMinimumCoreTotalSupport_lower`, `uniformMinimumCoreTotalSupport_radius_zero`, `uniformMinimumCoreTotalSupport_origin`, `uniform_core_adjust`, `uniform_core_uncertainty_upper`, `uniformMinimumCoreTotalSupport_sharp` | Proved: exact cross observations, fixed anchor shares, one bounded uncertain core payoff, sharper restoration/lower scale ε+3δ/8, genuine attained support minima, radius-zero equality and origin m+2 for m≥2. Perturbation vanishes on every residual row and is at most 3δ/8 on each anchor row. The matching sharp law is proved at every 0<ε+3δ/8≤1, with lower constant sqrt(3/1216) and upper constant5, for actual attained minima. Its positive-tolerance theorem even holds for m>0; origin density still requires m≥2. The new core payoff stays inside its clipped bounded interval, residual responses remain≤0, and the anchor error is max(d−3δ/8,0). |
| `sp:cor:certificate`, algorithms.tex | `compact_block_certificate_iff`, `RationalCertificate.check_iff`, `RationalCertificate.rows_iff`, `RationalCertificate.check_iff_full_rows`, `RationalCertificate.accepted_full_game`, `RationalCertificate.support_card_le`, `RationalCertificate.reject_omitted_violation` | Proved actual rational finite certificate checker and full-game soundness, including normalization, bounds, skewness and all original omitted rows. Actual reduced Rat data, lawful rational decidability and exact rational-to-Real injection contracts are retained. The support container may contain zero weights. The checker uses ambient finite quantification with support-membership guards and has no proved support-only operation bound. Finite rational linear repertoire and exact anchor checks are implemented below; arbitrary nonlinear repertoire checks and O(nk+S²) arithmetic/bit cost remain open. |
| `sp:thm:gap`, `sp:cor:fixedapprox`, algorithms.tex | `exact_completion_gap_point`, `gap_point_completed_witness`, `gap_infeasible_excludes_completion`, `gap_feasibility_monotone`, `fixed_game_value_bounds`, `gap_threshold_attained`, `gap_original_infimum_eq`, `fixed_anchor_additive_value_enclosure`, `RationalBisection.search_spec`, `RationalBisection.value_certificate` | Proved true→gap→relaxed feasibility for arbitrary R, monotonicity, actual compact-class fixed optimum V∈[0,M], attained nonnegative gap optimum W, equality with the original unrestricted nonnegative-threshold infimum, W≤V≤W+η and an actual completed witness. Rational bisection is an executable conditional procedure with genuine DecidablePred input, exact halving, nested bracket, finite-width existence and upper-witness enclosure of width η+ζ from explicit feasibility/exclusion/reconstruction contracts. The rational elimination tranche below now supplies an actual rational LP decider, payoff constructor and composed fixed-anchor bisection; explicit log2/ceil round choice is proved below; bit-cost and polynomial complexity theorems remain open. |
| `sp:prop:interval`, `sp:cor:gridp`, algorithms.tex | `perspective_call_epigraph_iff`, `exact_interval_completion_gap_point`, `interval_gap_recovered_exact_point`, `normalized_interval_gap_completed_witness`, `rounded_anchor_bounds`, `allocation_rounding_mass`, `allocation_rounding_distance`, `rounded_allocation_finite_grid`, `allocation_grid_card`, `allocation_rounding_in_grid`, `optimistic_allocation_grid_bounds` | Proved finite-grid perspective call/epigraph equivalence, necessary compatible-game lift and sufficient actual normalized bounded compatible completion at ρ+η, including zero-mass rows and unchanged q/K. Repertoire membership and core constraints are preserved by that literal identity. For nonnegative floors, nonempty feasible strategies, δ>0 and a specified residual action, round-down transfers removed mass to that action, preserves all floors/mass, has L1 distance≤2kδ, and lies in a finite grid with (1+floor(1/δ))^k index vectors. Compactness/attainment for actual floor classes and grid subclasses prove V≤Vgrid≤V+2Mkδ over actual compatible interval games. The rational implementation below handles the zero-residual case and returns an epsilon value approximation for the literal floor-only repertoire. Later sections prove actual sparse output for the zero-residual-floor class; polynomial execution/bit cost remains open, and no complete FPTAS implementation theorem is claimed. The literal interval LP and actual rational compatible-game output are proved below. |
| `ext:thm:cover`, graph_noise.tex | `free_residual_iff_anchor_cover`, `arbitrary_vertex_cover_sparse`, `arbitrary_vertex_cover_exact` (see ArbitraryCover.lean) | Proved on arbitrary original finite vertex sets: a constraint edge is an off-diagonal interval differing from the full interval, including an observed zero. A vertex cover frees the entire residual block. Nonnegative normalized actual witnesses are compressed with cover probabilities, all cover-incident entries and responses unchanged, original residual-support containment, all interval constraints and d specified linear moments preserved. General/exact residual and total finite-cardinality caps hold, including r=0, empty/full covers. The theorem uses H=gridSize M r η=ceil(sqrt(Mr/η)) directly, including the zero-mass branch. Decidable cover membership is genuine; the coordinate equivalence uses classical enumeration and asserts no efficient cover-finding algorithm. |
| `ext:prop:weakcover`, graph_noise.tex | `arbitrary_vertex_subset_weak_sparse`, `arbitrary_vertex_subset_weak_exact`, `residual_loss_bound_ordered` | Proved on arbitrary original subsets: project the residual block into nonempty bounded intervals with reverse consistency. All original constraints, cover data, residual-support containment and d extra moments are preserved, with final tolerance ρ+η+β_C r (η+β_C r for exact input). β_C is the least nonnegative bound on residual-pair losses, lies in [0,2M], and equals the source i<j maximum under a linear order and reverse interval symmetry. Empty/singleton residual types give zero. |
| `ext:cor:algorithm`, graph_noise.tex | Cover/weak-cover witness reductions and allocation-rounding mathematics in preceding rows | Supplied-cover mathematical reductions are proved; general allocation-floor grid/value bounds are proved for an explicitly nonempty residual action. Still open: end-to-end executable supplied-cover enumeration/selection and zero-residual branch, interval/cover-specific solver and grid integration, arithmetic and polynomial bit-complexity guarantees. Fixed-anchor finite rational linear repertoires now have an actual solver and bisection composition below. |
| `cv:lem:prefix`, `cv:thm:soc`, conic.tex | `threshold_is_score_prefix`, `cuts_iff_score_prefixes`, `prefix_cut_quadratic`, `quadratic_rotated_cone`, `weighted_completion_prefix_quadratic_iff`, `weighted_completion_rotated_cones_iff`, `known_anchor_prefix_characterization`, `normalized_known_anchor_conic_iff`, `known_anchor_conic_system_iff`, `prefix_system_convex`, `known_anchor_conic_system_convex`, `linear_repertoire_convex` | Proved: every strict threshold set is a genuine nonincreasing-score prefix, including ties, zero masses and empty types; all cuts iff the prefixes. The empty prefix is included as a tautology. Exact bounded skew residual completion and every original row are equivalent to the linear guards/anchor constraints and explicit rotated-cone constraints (2uv≥w², v=1/2). The full displayed q-system is convex at fixed tolerance for M≥0 and arbitrary convex repertoire; completion equivalence uses M>0 and fixed sorted scores. Literal linear-inequality repertoires are proved convex rather than assumed. `normalized_known_anchor_conic_iff` additionally proves the literal nonnegative mass-one, bounded skew full-game equivalence under explicit fixed K/D/p premodel premises. Quantified prefixes are l≤m (m+1 including empty), so this is a finite linear-size mathematical representation; no solver implementation, operation count, bit-complexity or exact-decision theorem is claimed. |
| `cv:thm:interval`, conic.tex | `interval_perspective_completion_iff`, `normalized_interval_perspective_iff`, `interval_perspective_system_convex`, `repertoire_interval_completion_iff`, `interval_system_repertoire_convex`, `residual_linear_repertoire_convex`, `perspective_cuts_iff_candidate_thresholds`, `interval_system_iff_threshold_system` | Proved exact normalized full-game characterization with jointly variable q,V,K and arbitrary declared residual repertoire R. The displayed perspective/core/anchor/cut system is jointly convex for M≥0; exact completion equivalence uses M>0, nonnegative fixed p and explicit normalization/interval premises. Convex repertoires preserve convexity; literal linear repertoires are proved convex. Zero-mass rows force V and H to zero, recovering D at the lower endpoint while retaining the explicit guard. All subset quadratics are equivalent to candidate-dependent upper-score threshold tests indexed only by positive-mass rows, with ties grouped. No globally fixed interval-score ordering is asserted. Mathematical finite separation, actual original-label quadratic violation output and affine separation, and exact finite-linear candidate-guard composition are proved. Full interval repertoire separation beyond the finite-linear class, O(m log m) arithmetic/bit costs, rational conic solving and polynomial guarantees remain open. |

The central result concerns existence of a compatible completion and strategy.
Compression may change the residual payoff block, retains original action labels,
and preserves anchor moments. It does not certify a strategy in the actual hidden
game or improve fixed-game support bounds. Positive residual probability floors
can force dense support. Residual and total support counts must remain distinct.

Classical prerequisites include weighted tournament-score/circulation geometry
and finite-moment recombination. The source credits Moon, Aldous–Kolesnik,
Tchakaloff-type work and related convex-order geometry. Research significance
resides in the combined sharp completion theorem, two-anchor realization and
family-specific uncertainty law. Completion existence, the sparse upper count,
the two-anchor exact realization and the total-support sharp order are now proved. The family-specific
uncertainty sharp laws are now proved. Later sections prove actual rational
algorithms, Boolean cut checking and the source-explicit residual-payoff
construction. Whole-paper coverage remains unfinished: full interval repertoire separation beyond the finite-linear guards,
arithmetic and bit complexity, polynomial LP/flow and the other explicit gaps
remain open.
Pinned Mathlib filename and term searches found no existing development of this
specific completion problem. This is not an exhaustive external overlap audit or
editorial novelty clearance. General finite sums, real algebra and convexity
infrastructure are reused, not claimed as new mathematics.

Proved extensions in the theorem presentation include arbitrary finite-feature
recombination and a finite-grid certificate independent of the square-root choice
of grid size (`finite_feature_compression`, `finite_grid_implication`). Rational
executable full-game certificate checking with repertoire constraints is proved
below; row-specific perturbation bounds remain an extension to prove.

Generic certificate checking and conditional bisection are strengthened by the total rational elimination and reconstruction tranche below. Its computed q,B are distinct from the prior existential Real completion. The algorithm does not supply polynomial encoding bounds. Later sections prove the source-explicit within/across-bin residual-payoff construction and executable sorted Boolean cut checking. Actual original-label violating cuts, affine separation and exact finite-linear candidate guards are supplied by the later tranches. Full arithmetic and bit cost and polynomial LP/flow guarantees remain tracked gaps.

The finite-gap sparsification results `gap_sparse_point`,
`normalized_gap_sparse_completed_witness` and
`normalized_interval_gap_sparse_completed_witness` compress an already feasible
gap point while preserving its original H call coefficients and anchor moments.
They give residual support at most min(m,k+1+H) and total support at most
min(k+m,2k+1+H), with an actual normalized bounded completed game at the original
ρ+η. The zero-mass case is proved separately. For interval input, the recovered
D and original K are frozen before compression. This proves the claimed support
existence without a second slack; no vertex-selection algorithm is inferred.
General repertoire/floor constraints need not survive compression and are not
claimed to do so. `interval_gap_epigraph_iff` packages all H call constraints in
one actual finite auxiliary family, including H=0 and empty residual types.


`RationalGrid` and `RationalGridSizeBounds` provide a genuine computable integer
count H=Nat.sqrt(Nat.ceil(Mr/η))+1, admissibility Mr≤ηH², and
H≤sqrt(Mr/η)+2 for M,r≥0,η>0. This is not literally the canonical count (r=0
uses H=1). Exact rational nodes/calls/envelope cast to the real coefficients,
and `rational_finite_grid_implication` proves interpolation on this explicit
grid. `rational_gap_check_iff`, `rational_gap_completed_witness` and
`rational_gap_normalized_full_game` validate a supplied rational q with actual
finite decidability and reconstruct an actual existential real completed game
at ρ+η. They retain all zero-mass row guards. Skew/bounded observations,
nonnegative p and normalization are explicit premodel premises. These results
supply rational coefficients and point-checking soundness. The new solver decides
∃q feasibility, returns rational B and handles finite rational linear repertoire
constraints. Arbitrary non-linear repertoires, bit bounds and integration of sparse
compression for this alternate H remain open.
The canonical-H real sparse-gap theorem above remains separate.


## Total rational fixed-anchor algorithm

| Component | Exact declarations | Scope |
| --- | --- | --- |
| Literal LP encoding | `rational_gap_conditions_iff_linear`, `rational_gap_encoding_rows` | Exactly 2m+2+k+H gap rows, including all m zero-mass guards, plus the declared finite rational linear repertoire. k+H counts anchor/call families; it is not a claim every row is nonzero or nonredundant. |
| Rational elimination | `rational_lp_solve_sound`, `rational_lp_solve_complete`, `rational_lp_solve_none_iff`, `rational_lp_real_complete`, `rational_linear_real_feasible_iff` | Actual recursive rational Fourier–Motzkin program, finite sign partitions, exact candidate selection and genuine computed existential decidability. Empty, one-sided, inconsistent and zero-dimensional systems are covered. Failure iff no real solution for rational coefficients; no general Real comparison decider is introduced. |
| Gap decision and real exclusion | `rational_gap_solve_sound`, `rational_gap_solve_none_iff`, `exact_game_rational_gap_solve`, `rational_gap_solve_none_excludes_real_completion` | Actual rational q computation. A true real completed game at ρ forces success. Failure excludes every such real completed game in the repertoire. Positive M is explicit; η>0 is needed for relaxed reconstruction. |
| Rational payoff reconstruction | `residual_completion_real_iff`, `rational_residual_completion_complete`, `rational_residual_completion_none_iff`, `rational_gap_reconstruction_normalized_full_game`, `rational_gap_algorithm_complete`, `rational_gap_algorithm_sound` | A literal 4m²+m-row matrix LP, m² variables, exact row-major indexing, rational skew/bounds/response constraints, and actual Option-returning matrix construction. An accepted gap point yields a normalized full game at the original ρ+η, with all original rows and the same p,q,K,D. No second slack. |
| Fixed-anchor value certificate | `rational_real_repertoire_compact`, `rational_gap_model_upper_feasible`, `rational_gap_approximation_complete`, `rational_gap_approximation_value_enclosure` | Actual rational linear repertoire has compact normalized nonnegative section. A nonempty section remains an explicit consistency premise. For M,η>0 and a nonempty full action type, automatic feasibility at M and a total returned rational q,B are proved. The actual compact-class value obeys L≤V≤U+η and U−L≤M/2^n. Therefore the shifted enclosure has width≤η+M/2^n. No assumed LP oracle or target optimality is used. |

This closes functional rational LP feasibility/reconstruction and fixed-anchor
solver/bisection composition. It does not close polynomial complexity:
Fourier–Motzkin elimination can grow exponentially. The paper's efficient
flow-based reconstruction, encoded bit bounds, executable sorted separation remain explicit work. The zero-floor global
sparse-output composition is proved below.
The source-explicit within/across-bin payoff construction is implemented in the later section below.
Whole-paper submission readiness remains false.


## Rational interval program and automatic accuracy

| Component | Exact declarations | Scope |
| --- | --- | --- |
| Interval recovery and encoding | `rational_interval_gap_recovered`, `rational_interval_row_count`, `rational_interval_system_point`, `rational_interval_lp_feasible_iff` | Explicit computable q,V,K,aux indexing, dimension m+mk+k²+Hm, exactly 3m+2+2mk+4k²+k+2Hm+H rows. Actual rational LP satisfaction is equivalent to all decoded constraints, including unweighted lower-score guards at q=0. K is a variable constrained by its original core intervals. Empty types and zero weights are retained. |
| Real feasibility and actual rational outputs | `rational_interval_system_real_point`, `real_interval_completion_rational_lp`, `rational_interval_algorithm_real_lp_complete`, `real_interval_completion_algorithm_success`, `rational_interval_algorithm_full_game` | Same rational matrix over Real; for M>0 and p≥0, every compatible real completion at ρ supplies a feasible point at the actual rational H. With η>0 and consistent cross intervals, genuine finite rational elimination returns actual coordinates and residual B. With p≥0, p-mass+r=1, η>0, consistent cross intervals and endpoints inside ±M, returned K,D lie in original intervals and the actual full game is normalized, skew, bounded and satisfies every response≤ρ+η. M>0 is needed for completeness. The base program has no repertoire parameter; the augmented program below handles finite physical linear constraints and interval value search. |
| Automatic fixed-anchor accuracy and returned certificate | `rational_log_rounds_width`, `rational_gap_accurate_value_enclosure`, `rational_gap_algorithm_checked_output`, `rational_certified_approximation_complete`, `rational_certified_approximation_sound` | Actual natural log2/ceil round choice n=log2(ceil(M/ζ))+1; M/2^n<ζ for ζ>0. Total returned program carries a rational full-container certificate and actual compact-class value bracket L≤V≤U+η with shifted width<η+ζ. Checker explicitly verifies same anchors and declared finite rational repertoire. The support container is all residual labels, may contain zero weights, and carries no claimed sparse cardinality bound. |

These are functional rational algorithms. The source's polynomial sparse vertex-selection
program, efficient sorted separation/flow construction, polynomial operation and
bit bounds remain unformalized. The explicit within/across-bin residual payoff
construction is proved in the source-explicit bin section below. Fourier–Motzkin may be exponential. The canonical-grid sparse
existence theorem remains distinct from this computable alternate-H program.
Whole-paper submission readiness remains false.


## Physical-repertoire interval value algorithm

| Component | Exact declarations | Scope |
| --- | --- | --- |
| Physical constraints | `interval_physical_pack`, `rational_interval_repertoire_system_iff`, `rational_interval_repertoire_real_system_iff`, `real_interval_repertoire_algorithm_success`, `rational_interval_repertoire_algorithm_full_game` | Declared finite rational linear R acts only on q,V,K. Explicit projection removes auxiliary variables. Exact Q/Real augmented-matrix equivalences, true-real success and returned normalized bounded original-interval game preserve R(q,qD,K), also at zero q. DirectD and arbitrary nonlinear constraints are not encoded. |
| Actual tolerance search | `rational_interval_repertoire_feasibility_monotone`, `rational_interval_search_bracket`, `rational_interval_model_upper_feasible`, `rational_interval_model_approximation_complete` | Actual finite rational elimination decides feasibility; increasing ρ preserves q,V,K/R and rebuilds auxiliary A while H stays fixed. The model has M,η>0, p≥0, normalized p-mass+r, endpoint containment, consistent cross intervals and actual compatible-class nonemptiness. Consistency contains no objective threshold or solver result. Bounded probability responses give automatic feasibility at M and total actual program output. |
| Actual optimum | `interval_game_class_compact`, `interval_game_class_nonempty`, `interval_game_value_attained`, `interval_game_class_game_facts`, `interval_game_value_bounds` | The full original q,D,K,B class with physical R(q,qD,K) is compact by finite boxes and closed polynomial constraints. The q≤r box is derived from nonnegative mass. Actual exploitability attains its infimum V∈[0,M]. Class/value proofs allow arbitrary I intersections; algorithms require finite I. Nonempty full action type is explicit for finite row supremum/value. |
| Output and value | `rational_interval_output_physical`, `rational_interval_algorithm_output_class`, `rational_interval_approximation_value_enclosure`, `rational_interval_accurate_complete`, `rational_interval_accurate_value_enclosure` | Every returned rational game belongs to the original physical class; qD=V includes zero q. True attained optimal witnesses contradict computed infeasible lower endpoints; returned all-row games certify the upper endpoint. Thus L≤V≤U+η, U−L≤M/2^n and automatic log2/ceil rounds give shifted width<η+ζ for ζ>0. One η slack; no optimum oracle or sparse-output bound. |

Polynomial sparse vertex selection, efficient sorted separation
and flow, and operation/bit
bounds remain open. For M=1, the source fixedapprox result claims time polynomial in input bit
length, inverse η and log(1/ζ). Fourier–Motzkin may be exponential; a bounded pinned-library audit found
no reusable object-level polynomial rational-LP proof. This is a formal
foundation gap, not evidence against the paper's mathematical result. Whole-paper
readiness remains false.


The initializer now computes physical consistency for admissible rational
parameters: M,η>0, nonnegative anchors, normalization, bounded endpoints and
ordered cross intervals are explicit proof fields; physical nonemptiness is not.
Its actual rational solver determines the Boolean branch of a genuine Decidable
instance for compatible real games. Initialization and the combined approximation
return None exactly for incompatibility. Returned fixed-dimension rational
q,K,D,B belong to the original class and have all responses at most U+η. With
nonempty full action type and ζ>0, L≤V≤U+η and shifted width<η+ζ. This is not
a parser validating arbitrary untrusted rational inputs. The original dense initializer supplies no polynomial-time bound. The sparse follow-on below reuses its actual compatibility decision.

Exact new contracts are `rational_interval_success_compatible`,
`rational_interval_compatible_success`,
`rational_interval_initialize_complete`, `rational_interval_initialize_sound`,
`rational_interval_initialize_none_iff`,
`rational_interval_initialized_complete`, `rational_interval_initialized_none_iff`,
`rational_interval_initialized_game` and `rational_interval_initialized_value`.
The proofs cover all dimensions; executable controls include zero residual
actions and the fully empty incompatible case. The later zero-floor global sparse-output composition is now proved. Efficient
sorted separation/flow and polynomial cost bounds remain outside this tranche. Whole-paper readiness is false.


## Executed floor-grid global approximation

| Component | Exact declarations | Scope |
| --- | --- | --- |
| Empty-safe rounding | `reservoir_rounded_floors`, `reservoir_rounded_mass`, `reservoir_rounded_distance`, `reservoir_grid_approximation`, `rational_reservoir_rounding_enumerated`, `rational_anchor_rounding_enumerated` | Actual same-label floor/mass preservation and L1≤2kδ. Removed anchor mass goes to a residual coordinate when available, otherwise an existing anchor. Exact Q/Real floor and index bridges identify the rational candidate with the real rounded strategy. The Real index bridge is noncomputable mathematics; actual rational enumeration and search do not call it. |
| Executable enumeration and selection | `rational_grid_tuples_complete`, `rational_grid_tuples_length`, `rational_finite_select_origin`, `rational_finite_select_minimal`, `rational_finite_select_none_iff`, `rational_allocation_run_success_iff` | Literal finite lists constructed by finRange/map/flatMap/Fin.cons contain all grid indices and have length (1+floor(1/δ))^k. Actual runs check anchor floors, compute physical feasibility and interval value outputs, skip infeasible candidates, and use rational argmin of computed U. No classical enumeration, fake real comparison, or optimality oracle supplies the runtime result. |
| Actual global class | `floor_interval_game_class_compact`, `floor_interval_game_value_attained`, `floor_interval_game_class_of_fixed`, `rational_floor_approximation_output_class` | Both p and q vary, with original K,D,B intervals, nonnegative floors and total mass1. Coordinate upper bounds1 are derived from nonnegative mass, not added constraints on genuine feasible games. Actual original-label games form a compact class and attain the literal exploitability infimum. The caller supplies physical nonemptiness only when stating a value; it is subsequently decided by the actual program. |
| Program/value composition | `rational_floor_grid_value_certificate`, `rational_no_residual_global_certificate`, `rational_floor_search_value_certificate`, `rational_floor_approximation_global` | For the literal residual-floor R, any physically nonempty admissible class gives actual rational output. True rounded witnesses bound slice values; computed min-U selection and actual returned game membership prove V≤U+η<V+2Mkδ+ζ+η. The automatic program uses ε/3 slacks and δ=ε/(6M(k+1)), proving V≤τ<V+ε. The returned fixed-anchor L is not claimed to be a global lower bound. |
| Physical decision and edge cases | `floor_interval_class_nonempty_actions`, `rational_floor_approximation_none_iff`, `rational_floor_approximation_empty`, `rationalFloorClassDecision` | For ε>0, actual None iff the global real physical class is empty. The genuine Decidable Bool comes from public Option.rec over the actual rational program and proved success/failure branches. No physical-nonemptiness or target-value proof is supplied to the decision. The fully empty action type returns None; m=0 and k=0 branches are explicit. ε≤0 returns None without implying incompatibility. |

The global program requires R to be exactly the residual floor matrix. Its
rounding proof does not assert preservation of arbitrary additional physical
linear constraints; the independently proved fixed-anchor solver still permits
those constraints. Admissibility proofs for M>0, endpoint bounds/order,
nonnegative template anchors and normalization are input fields, not an
untrusted-data parser. The returned game may have dense residual support.
The finite node-count theorem is not a machine/bit-cost bound. The source's
polynomial-time guarantee, efficient sorted separation and max-flow
reconstruction and canonical release verification remain open. No
whole-paper or submission readiness is claimed.


## Executable sparse interval output

| Scope | Lean contracts | Exact result and limits |
| --- | --- | --- |
| Compression at the executed grid | `rational_gap_real_compression` | Nonnegative real finite-gap points compress to min(m,k+actualH+card(I)+1), preserving every actual H call, anchor-response coefficient and additional linear row. Mass zero is handled directly. This real intermediate also preserves original zeros. |
| Actual support search | `rational_sparse_gap_search_sound`, `rational_sparse_gap_search_complete`, `rational_sparse_gap_algorithm_sound`, `rational_sparse_gap_algorithm_complete` | All 2^m masks are enumerated by the existing actual tuple program; zero-outside-mask rows are imposed on the actual rational LP. Real compression and proved real-to-rational feasibility transfer force actual success. The returned rational q preserves gap feasibility and R, with min(m,k+actualH+card(I)+1) support. No sparse input witness, choice oracle or fake real decision supplies the algorithm. |
| Returned full games | `rational_sparse_gap_algorithm_full_game`, `rational_sparse_gap_algorithm_full_support` | With explicit normalized, bounded skew anchor data and eta>0, actual q,B form a normalized bounded skew full game with every response<=rho+eta, and total support<=min(k+m,2k+actualH+card(I)+1). |
| Interval recovery and physical rows | `rational_frozen_physical_system_iff`, `rational_interval_sparse_reduction`, `rational_interval_sparse_algorithm_real_complete`, `rational_interval_sparse_algorithm_conditions`, `rational_interval_sparse_algorithm_game` | Rational K,D are recovered at original rho before compression. Original arbitrary R(q,qD,K) becomes affine in q, with the constant K contribution subtracted exactly. Actual sparse q,K,D,B retain original interval membership and all physical rows, with only one eta. Final q is not asserted to preserve an arbitrary original real witness's individual moments. |
| Actual automatic value program | `rational_interval_sparse_accurate_complete`, `rational_interval_sparse_accurate_value_enclosure`, `rational_interval_sparse_initialized_none_iff`, `rational_interval_sparse_initialized_game`, `rational_interval_sparse_initialized_value` | Compatible admissible parameters give actual sparse rational output; None iff physical incompatibility. The original compact class's true value satisfies L<=V<=U+eta with shifted width<eta+zeta for zeta>0. Full action nonemptiness remains explicit for values. Runtime does not take a physical-nonemptiness proof. Completeness/computed incompatibility theorems use row type I:Type, matching the existing finite-compression theorem; soundness permits Type*. |

This is an exhaustive functional algorithm. It does not prove polynomial
operation or bit complexity, sorted separation or efficient flow reconstruction.
The zero-floor global wrapper below sparsifies its chosen fixed observations. Arbitrary extra
physical rows contribute card(I) to the support bound; no sparsity independent
of positive residual floors is claimed. The zero-floor global sparse-output composition is proved below; canonical release checks remain open.


## Source-explicit original-label bin payoff construction

| Scope | Lean contracts | Exact result and limits |
| --- | --- | --- |
| Executed payoffs and index semantics | `rational_central_pair_response`, `rational_explicit_bin_payoff_skew`, `rational_explicit_bin_payoff_bounds`, `rational_binned_label_decode`, `rational_supported_bin_payoff_local` | Rational payoff program uses actual original labels through finSigmaFinEquiv. Earlier supported bins lose to later bins by1; distinct same-bin centers exchange2/L; omitted rows use -(m-2j-1)/m and the reverse entry is skew. Odd duplicated slots are coalesced. Distinct same-bin labels force L>=2; the proof does not infer2/L<=1 from positivity alone. |
| Actual strategy and all exact rows | `rational_binned_weights_real`, `rational_binned_weights_mass`, `rational_binned_omitted_response`, `rational_bin_cross_response`, `rational_bin_pair_response`, `rational_binned_residual_response`, `rational_binned_explicit_completion` | Computed rational weights coincide exactly with the existing real binned weights. Direct finite sums prove every supported and omitted original residual row has response0. Cross-bin contribution2start+L-m and local2offset+1-L cancel the literal uniform score; no existential cut/flow witness substitutes for this matrix. Nonnegative probabilities require r>=0; exact algebra covers r=0. |
| Same matrix over the reals | `rational_uniform_score_real`, `rational_binned_response_real`, `explicit_binned_residual_response` | Unit-mass rational correctness and proved homogeneity extend the cast of the same actual matrix to every real r. Division by r is not used at r=0. Total m>0 is explicit when asserting mass/probability/completion. |
| Error and uncertainty composition | `explicit_binned_game_witness`, `explicit_binned_core_witness` | With r=1/4 and arbitrary positive lengths, the same actual matrix has min(m,2h) residual support, exactly zero residual rows, two anchor responses+/-d and exact parity error r^2/(12m^3)*sum L(L^2-c), c=4 even/1 odd. Existing proved loss/support laws provide the cubic upper bound. The clipped core observation adjustment retains the same q,B under d<=epsilon+3delta/8. This is not an assumed new coauthor proof or a generic polynomial LP algorithm. |

This closes the previously missing explicit within/across-bin payoff route for
the source mathematics. The zero-floor global sparse-output composition is proved below. Efficient sorted separation and generic flow reconstruction, polynomial
operation/bit-cost foundations, untrusted raw-input validation and canonical
release requirements remain distinct. No whole-paper submission readiness is
claimed.


## Global sparse output and computed epsilon-width certificate

| Scope | Lean contracts | Exact result and limits |
| --- | --- | --- |
| Actual two-stage sparse program | `rational_floor_sparsify_complete`, `rational_floor_sparsify_class`, `rational_floor_sparse_output_game`, `rational_floor_sparse_global` | Actual dense allocation search at epsilon/2 chooses p,K,D; exact-game necessity supplies the finite-gap input, then actual finite-mask sparse LP/completion changes q,B only. Original zero-floor interval class is retained and every response<=tau with V<=tau<V+epsilon. Anchor floors remain arbitrary nonnegative; R must be literally the zero residual-floor matrix. No arbitrary-R rounding or positive-floor-independent sparsity is claimed. |
| Support and computed incompatibility | `rational_floor_sparse_total_support`, `rational_floor_sparse_sqrt_support`, `rational_floor_sparse_none_iff`, `rationalSparseFloorClassDecision`, `rational_floor_sparse_empty` | Full support<=min(k+m,2k+H+1)<=2k+sqrt(2M/epsilon)+3, with the actual H at eta=epsilon/2 and r=1-sum p. None iff physical incompatibility for epsilon>0; the decision is derived from the actual Option program. Fully empty actions return None; m=0 and k=0 controls execute. |
| Actual value-bracket wrapper | `rational_floor_sparse_certified_origin`, `rational_floor_sparse_certified_none_iff`, `rational_floor_sparse_certified_complete`, `rational_floor_sparse_certified_value` | Actual map replaces only the bracket with (tau-epsilon,tau), proves strict L<V<=U and exact width epsilon for every Some output, with the same class membership, rows and support. No prior refined lower grid bound is retained or assumed. Value statements have the explicit nonempty action instance; program execution takes no class-nonemptiness or target-value proof. |

This closes the functional zero-floor global sparse-output and actual global
additive certificate packaging. Efficient sorted separation/flow, a polynomial
rational LP implementation and polynomial operation/bit-cost guarantees remain
unformalized. The exact source cost of checking compact certificates is a
separate follow-on; no whole-paper readiness is claimed.

## Complete original-source statement inventory and instrumented checker

WHOLE-PAPER-COVERAGE.md enumerates all27 formal source environments and32
additional substantive claim groups. The new no-grid positive-mass bound,
quantitative prefix domination, general nonnegative-floor returned value bracket
and uniform supplied-cover ceiling corollary are proved in the added modules.
The connected finite-table certificate checker has proved unit-rational
arithmetic/order/equality and rational-slot bounds, including fixed/floor and
chosen interval checks. This closes that explicitly declared source arithmetic
model, not polynomial LP/flow or input-bit/machine complexity. All old cost-open
statements referring to this checker are superseded only to this precise extent.
Full candidate separation, arbitrary-cover program transport and polynomial
LP/flow/bit guarantees remain explicit gaps. The historical59 additions prove
sorted Boolean cut checks and source-exact dense allocation node constants. General-M joint bounds and the actual worst-case support operator are
proved in the43 additions described below. See the full table for edge cases.

## General payoff bounds and actual worst-case support

The historical43-proof follow-on added payoff rescaling, general-M upper and hard-instance
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

This section records predecessor836ab90. Later additions and resolved gaps are described below.

The prior verified follow-on added59 proofs in17 mathematical modules:45 cover actual
balanced sorting, original action labels, running-sum prefix scanning and raw
or interval perspective cut checks;14 cover the allocation step proportional to
`epsilon/(M*k)` and its actual dense floor-search output. That historical package
had263 mathematical modules,1012 source theorem axiom audits and902 selected
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

Whole-paper readiness remains false. Remaining work includes general repertoire separation, full arithmetic and bit complexity, polynomial rational
LP/flow guarantees, efficient sparse vertex selection and executable arbitrary
cover transport. Native macOS checks do not establish canonical Linux sandbox,
rendering, release-role or editorial readiness. No submission is authorized.

## Violating-cut payloads and exact candidate reconstruction

The next local tranche adds43 genuine proofs in8 modules, giving271 mathematical
modules,1055 source theorem audits and945 selected protected contracts. The
actual rational prefix scan returns an original-label subset whose cut is
strictly violated. Its None result agrees with the existing Boolean cut checker;
all-cut completeness requires nonnegative M and weights. A second payload
constructor uses the proved Nodup label list directly. Its executable data path
uses take/map and the Finset constructor without dedup; its equality proof with
the earlier List.toFinset program still imports the literal dedup semantics.
This tranche does not yet wrap the payload in interval perspective coordinates
or return affine separating coefficients.

The same-program supplied-score arithmetic ledger counts additions,
subtractions and multiplications as unit rational operations. It proves at most
7*m+4 written arithmetic operations and m*(Nat.log2 m+2)+1 comparisons, with
combined bound m*(Nat.log2 m+9)+5. It excludes score/getter formation, rational
normalization, equality tests, allocation, traversal and machine/bit costs.
Denominator products bound the reduced denominator of a rational list sum and
its binary length. Numerator growth, primitive arithmetic bit cost and complete
algorithm runtime remain unproved.

rationalIntervalExactCheck computes all finite linear perspective, anchor,
core-skew/core-interval and global lower-score guards, including every zero-mass
row, and the sorted quadratic cut check. For M>=0 it is equivalent to the exact
cast intervalPerspectiveSystem. An optional arbitrary physical repertoire R is
not wired into this base checker. The full-game existence wrapper retains M>0 and
explicit normalization, anchor nonnegativity and physical interval bounds.
rationalIntervalExactReconstruction returns actual rational cross and residual
payoff tables using the existing genuine rational residual LP at epsilon.
Its completeness holds for M>=0, including M=0; soundness gives the original
bounded normalized skew game under the stated physical premises and all rows
at epsilon without hidden eta slack. None rejects this particular candidate
(q,V,K), not the entire physical class. The residual LP is Fourier--Motzkin:
its correctness is proved, but no polynomial running-time bound is claimed.

The43-source narrow check passed strict compilation,43 axiom reports (including
two axiom-free proofs) and36 executable controls. Internal independent AI review
covers the mathematics, proof repairs and receipt authentication. These narrow
checks are not a clean exact-commit whole-package verification. All completed
mechanical gates for the integrated candidate are bound by immutable evidence
outside the frozen source; predecessor836ab90 passed all12 native gates for its
own bytes. Whole-paper and submission readiness remain false. At predecessor273fb8c, perspective violating-cut output and affine separation were open; the later52 tranche below supplies them. Complete arithmetic/bit costs, polynomial rational LP/flow guarantees, efficient sparse vertex selection and executed supplied-cover encode/decode transport remain open. Native macOS checks do not establish
canonical Linux, rendering or editorial readiness. No submission is authorized.

## Computed violating cuts, separation and flow foundations

This follow-on adds52 proofs in10 modules to predecessor273fb8c. The resulting
source at predecessor dd34 had281 mathematical modules,1107 source theorem audits and997 selected
protected contracts. These counts describe scope, not whole-paper completion.
Its exact-source verification and independent receipts are recorded outside the
frozen package; predecessor receipts certify only their own source bytes.

RationalPerspectiveViolation and RationalIntervalViolation connect actual
rational prefix search to an original-label violating quadratic cut. None is
equivalent to the corresponding cut checker, under the stated M≥0 and q≥0 premises, with H=0 at zero q
or the interval perspective bounds that imply it. RationalPerspectiveSeparator computes an
affine functional from the returned cut and the candidate mass. The exact gap
is M times a squared mass difference. For M≥0 the functional separates the
violating candidate from every real point satisfying the perspective cuts.
This is a separation certificate, not a polynomial LP implementation.

RationalFlowDemandCuts proves the signed-demand network cut identity.
RationalSaturatedFlow decodes a supplied nonnegative source-saturated arc-flow
certificate to a bounded skew payoff table when the unknown masses are positive.
RationalFlowZeroRows handles zero masses by an explicit piecewise table; the
original global row guard is essential. RationalFlowCertificateCheck checks the
physical premises and supplied certificate and returns the actual decoded table.
Some is sound. None means that supplied certificate failed; it does not establish
infeasibility. Zero total mass, zero capacity and empty unknown index sets are
covered where the theorem premises allow them.

RationalResidualReach executes finite flood layers on a Boolean adjacency
function. After n layers the reachable set is closed and equals finite
reflexive/transitive reachability. This input is a function, with no array-cache
or access-cost theorem. RationalNetFlow converts nonnegative arc flow F to skew
net flow F(u,v)−F(v,u), proving capacity, divergence and residual identities.
Residual capacity includes cancellable reverse flow. Applying C−F directly to
raw nonnegative arc data would use the wrong convention.

FiniteSkewEquilibrium proves that every finite nonempty real skew game has a
normalized nonnegative mixture with all row responses nonpositive. Its proof
uses compact convex separation, normalization of a nonnegative separating
functional and the zero self-payoff identity. The simplex is defined locally;
this is a classical existence foundation, not a computable optimizer or a
novelty claim.

Source retention adds the literal Relation.ReflTransGen declaration and exact
compiler routes for Nat's generated recursor and finite existential decision.
Nat.rec is compiler-generated from the retained Nat inductive; there is no
literal def Nat.rec. This also repairs62 precisely identified historical
WellFounded.Nat.fix source contexts. Predecessor273fb8c's native checks remain
valid, while its retained-source completeness was qualified by that omission.
The new finite-existential route is retained separately from finite universal
decision. Exact declaration usage follows actual compiled local dependency
closures, with no assignment merely from module membership. Both import
contexts retain executable controls and semantic bridges.

The following remain open: residual path recovery and augmentation, a maximum
flow finder and its correctness, polynomial flow and rational LP guarantees,
primitive arithmetic/bit costs and full runtime, efficient canonical sparse
selection and executed supplied-cover encode/decode transport. Existing comparison counts,
supplied-score unit arithmetic ledgers and denominator bounds do not prove
those runtime claims. Canonical Linux/rendering and release-role confirmation
also remain separate. Formalization authors and maintainers are unconfirmed;
internal AI reviews are distinguished from human or external review.
No registry or journal submission is authorized or performed.

## Cached paths, net-flow cuts, numerator bounds and Nash interpretation — source-only candidate

The current proposed source has287 mathematical modules,1155 source theorem
audits and1045 selected protected contracts. The six modules add48 proved
statements, including the finite-vector getter coherence helper. All48 have
strict pinned-toolchain development axiom reports,18 executable controls passed,
and the prospective protected comparison, altered-helper rejection and export
kernel checks passed. This source integration is a new candidate: the14 newly
inserted semantic bridges and both canonical entrypoints have NOT been compiled
for these bytes. The generated-definition validator source passed independent code review and
14 portable Python regression methods; that establishes no Lean compilation.
Its exact two reviewed root files are installed separately. Exact assembled
source/dependency checks, final independent source review and full exact-commit
native verification remain required. Earlier stage counts and open-item paragraphs are
historical; the following account states this candidate's scope.

`RationalPositiveNetFlow` reconstructs nonnegative arc flows from skew net flow.
`RationalReachCut` and `RationalNetCut` prove saturation of the actual residual
reachable cut, cut/divergence identities, weak duality and a maximum certificate
when the target is unreachable. They do not find a feasible flow or implement an
augmentation loop.

`CachedResidualBFS` stores a finite Boolean adjacency table and, per layer, a
vector of discovered complete walks. Its actual Option result is None exactly
when the target is unreachable. A Some result is a genuine walk with the stated
endpoints, at most n edges and shortest length among genuine walks. Predecessor
extraction uses that returned path. This is not a predecessor-forest/linear-space
implementation, and no table-access, allocation, traversal-operation or machine
cost theorem is claimed. For zero vertices there are no source/target Fin labels;
the zero-size cache construction is executable. The rational residual graph uses
C−F for NET flow. Raw positive arc flows require the proved antisymmetrization
bridge; reverse residual capacity can arise from a negative net-flow entry.

`RationalNumeratorGrowth` adds actual magnitude, numerator-product, binary-power
and numerator bit-length bounds for rational LIST SUMS. These supplement the
existing denominator bounds. They do not bound intermediate sizes of arbitrary
LP elimination, normalization/gcd primitives or end-to-end rational bit time.

`FiniteSkewNash` gives an actual both-player mixed-deviation predicate for the
zero-sum game and proves its equivalence to the symmetric row-response criterion
for skew games. Finite nonempty skew games therefore have an actual symmetric
zero-tolerance mixed equilibrium. This is an existence/interpretation result,
not a computable optimization algorithm or a generic non-zero-sum Nash theorem.

Source retention records the genuine to_additive generators mabs→abs and
Pi.mulSingle→Pi.single separately from their actual generated declarations.
Their inferred names are not accepted as fake literal source heads. The narrowly
reviewed validator distinguishes the exact two generated source/target pairs. A retained
dual-export attestation binds actual target presence, while separately named
semantic bridges must still compile in BOTH entrypoints. Exact historical
marker audits cover240 abs and184 Pi.single contexts. Cached-table construction
retains Vector.ofFn→Array.ofFn and its coordinate contract; integer magnitude
retains Int's signed constructors and natAbs's logical/extern boundary.

The finite-complement source correction is operation-specific:223 contexts use
element search/difference,226 use shared erasure/runtime support, and183 older
contexts use the explicit Finset.erase→Multiset.erase wrappers. Three historical
erasure users do not require List.elem. These audits stop at the established
project-local/external-definition boundary; they do not claim exhaustive
expansion of every upstream theorem body. Frozen predecessor receipts remain
unchanged and mechanically valid, with the discovered retention qualification
preserved in this new candidate.

Whole-paper completion and submission readiness remain false. Open work includes
a genuine complete capacitated-flow finder/augmentation algorithm, its operation
and bit bounds, polynomial rational LP guarantees, complete arithmetic/encoding
costs beyond the proved components, efficient sparse selection and the remaining
source-specific algorithm compositions. No publication or submission is made.
