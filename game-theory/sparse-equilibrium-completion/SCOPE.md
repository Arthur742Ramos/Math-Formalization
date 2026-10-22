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
| `sp:thm:sparse`, main_theorem.tex | `finite_moment_recombination`, `finite_feature_compression`, `sparse_cut_witness`, `exact_sparse_cut_witness`, `canonical_sparse_cut_witness`, `game_sparse_cut_certificate`, `exact_game_sparse_cut_certificate`, `game_sparse_completion`, `exact_game_sparse_completion` | Proved: nonnegative mass on original labels, original-support containment, exact anchor moments/responses, support `k+1+H` generally and `k+H` at exact equilibrium, all relaxed cuts and global guards, from actual original block-game data. Caratheodory preserves all selected hinge values exactly, replacing the source's inequality/vertex argument at the same support count. The exact case preserves only `H-1` hinge values; the full skew-game bridge supplies the missing endpoint equality. The completed-game theorems reconstruct an entry-bounded skew residual block and prove all original block-game response inequalities. Open: paper-facing normalized bounded-game specialization, explicit extra-moment wrapper and algorithmic clauses. No residual floors are imposed. |
| `lb:thm:dense`, rigidity.tex | Unformalized | Open: bounded two-row construction with `p=3/4`, `r=1/4`, uniform target; anchor formulas; prefix exposing identity; all strategy coordinates and all residual edges uniquely forced. Compatibility premise is essential. |
| `lb:thm:universalrigidity`, rigidity.tex | Unformalized | Open: arbitrary strictly positive target of mass `1/4`, `m≥2`; minimum shares `3/8`; variable-mass prefix argument; unique strategy and completion. |
| `lb:thm:support`, rigidity.tex | Unformalized | Open: constant-run approximation to cumulative mass; cubic run inequality; full quantitative bound and simplified `3/(1216(h+1)²)` for `m≥2h+1`. |
| `lb:thm:upperrate`, `lb:thm:allm`, rigidity.tex | Unformalized | Open: midpoint construction under divisibility/oddness; parity-free one/two-center bins; omitted-action guards; exact second moments; at most `min(m,2h)` residual support and upper bounds. |
| `lb:cor:rate`, `lb:thm:naturalapprox`, unlabeled total-support corollary | Unformalized | Open: attained support minima; exact density; fixed-share and minimum-share inverse-square laws with separate tolerance ranges and constants. |
| `sp:cor:sharpk`, joint_support.tex | Unformalized | Open: mandatory clones and aggregation; worst-case total support `Theta(min(n,k+sqrt(M/η)))` for `k≥2`, `m≥2`, `0<η≤M`. |
| `ext:prop:stability`, graph_noise.tex | `response_perturbation` is the response-level ingredient | Open: independent interval projection preserving skew bounds, compact strategy-class minima and support-budget bridge. Response bound is `δ*r`; simplex mass one gives `δ`. |
| `ext:thm:noise`, graph_noise.tex | Unformalized | Open: uniform-family interval construction, lower transfer at `ε+δ`, matching upper law and origin; both exact shares and minimum shares. This is not a universal noise-sparsity theorem. |
| `ext:cor:corenoise`, graph_noise.tex | Unformalized | Open: altering only anchor-anchor entry, feasible clipped interval, all supported/omitted responses, matching law; fixed-share sharper scale `ε+3δ/8`. |
| `sp:cor:certificate`, algorithms.tex | `compactCompletion`, `compactCompletion_skew`, `compactCompletion_bounds`, `compactCompletion_response_on`, `compactCompletion_response_off`, `compact_certificate_responses_iff`, `compact_block_certificate_iff`, `blockMatrix_bounds` | Residual reconstruction and exact full-game anchor/supported/omitted response equivalence are proved, with skewness and bounds provided by the construction lemmas. The supplied support may contain zero-mass entries; only weights outside it must vanish. Normalization and nonnegativity have literal block-weight bridges. Additional repertoire predicates and arithmetic-operation cost remain open. |
| `sp:thm:gap`, `sp:cor:fixedapprox`, algorithms.tex | Unformalized | Open: rational LP exclusion/gap guarantees, monotone bisection and arithmetic cost. |
| `sp:prop:interval`, `sp:cor:gridp`, algorithms.tex | Unformalized | Open: independent interval perspective lift, zero-mass recovery, variable core, fixed-`k` anchor grid and additive error/bit-complexity guarantees. |
| `ext:thm:cover`, `ext:cor:algorithm`, `ext:prop:weakcover`, graph_noise.tex | Unformalized | Open: constrained-edge cover reduction, `r=0` case, additional linear moments and imperfect-cover response loss. |
| `cv:lem:prefix`, `cv:thm:soc`, `cv:thm:interval`, conic.tex | Unformalized | Open: score-prefix sufficiency and exact convex/SOC formulations; no polynomial exact-decision claim is licensed by convex representability. |

The central result concerns existence of a compatible completion and strategy.
Compression may change the residual payoff block, retains original action labels,
and preserves anchor moments. It does not certify a strategy in the actual hidden
game or improve fixed-game support bounds. Positive residual probability floors
can force dense support. Residual and total support counts must remain distinct.

Classical prerequisites include weighted tournament-score/circulation geometry
and finite-moment recombination. The source credits Moon, Aldous–Kolesnik,
Tchakaloff-type work and related convex-order geometry. Research significance
resides in the combined sharp completion theorem, two-anchor realization and
family-specific uncertainty law, the latter two remain unformalized. Completion existence and the sparse upper count are now proved; whole-paper sharpness is not claimed.
Pinned Mathlib filename and term searches found no existing development of this
specific completion problem. This is not an exhaustive external overlap audit or
editorial novelty clearance. General finite sums, real algebra and convexity
infrastructure are reused, not claimed as new mathematics.

Proved extensions in the theorem presentation include arbitrary finite-feature
recombination and a finite-grid certificate independent of the square-root choice
of grid size (`finite_feature_compression`, `finite_grid_implication`). Rational
executable full-game certificate checking with repertoire constraints and
row-specific perturbation bounds remain useful extensions to prove.
