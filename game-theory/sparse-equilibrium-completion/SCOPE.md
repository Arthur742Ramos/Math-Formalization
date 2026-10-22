# Theorem-to-Lean scope map

The source is the verified sparse-equilibrium-completion paper revision
`1a424f297925294ae5818ff1ee7512304af1d460`, not the earlier variance-design work.
All labels below refer to `paper/sections/` at that revision. Source blobs are
bound in `verification/paper-source-manifest.json`. Proof status is confined to
the actual declarations; unfinished targets have no placeholder Lean theorem.

| Paper result | Lean correspondence | Scope and remaining work |
|---|---|---|
| `sp:lem:flow`, completion.tex | `skew_weighted_sum`, `response_guard`, `completion_cuts_necessary` | Necessity for arbitrary finite index types, nonnegative weights and arbitrary total mass. Lower bounds on skew entries imply both payoff bounds. Flow/cut sufficiency, positive-support division and zero-mass completion remain open. |
| `sp:lem:call`, completion.tex | `quadratic_duality`, `cuts_imply_call_bound`, `call_bound_implies_cuts`, `cuts_iff_call_bound` | Exact cut/call equivalence for `M>0`, nonnegative weights of mass `r`; forward bound even holds for every real argument. Direct positive-score subset and square completion replace the source's sorted partial-mass proof. Endpoint supported-score consequence remains to package. |
| `sp:lem:grid`, sparsification.tex | `quadratic_grid_identity`, `truncated_grid_error`, `call_convex`, `call_secant`, `grid_interval_cover`, `finite_grid_implication` | Full shifted-call implication for any natural `H` with `Mr ≤ η H²`, `M>0`, `r≥0`, `η>0`. Support cap applies only at nonzero coordinates. This generalizes the source grid parameter; `gridSize_bound` and `canonical_grid_implication` prove the explicit `H=ceil(sqrt(Mr/η))` bridge. No mass assumption is needed for this interpolation implication. |
| `sp:thm:sparse`, main_theorem.tex | Foundational ingredients above | Open: bounded completion sufficiency; finite-polytope extreme point existence; rank/support bound `k+1+H`; original-support containment; exact anchor moments; fixed-anchor block bridge; exact-equilibrium saving to `k+H`; extra `d` moment extension. No residual floors permitted. |
| `lb:thm:dense`, rigidity.tex | Unformalized | Open: bounded two-row construction with `p=3/4`, `r=1/4`, uniform target; anchor formulas; prefix exposing identity; all strategy coordinates and all residual edges uniquely forced. Compatibility premise is essential. |
| `lb:thm:universalrigidity`, rigidity.tex | Unformalized | Open: arbitrary strictly positive target of mass `1/4`, `m≥2`; minimum shares `3/8`; variable-mass prefix argument; unique strategy and completion. |
| `lb:thm:support`, rigidity.tex | Unformalized | Open: constant-run approximation to cumulative mass; cubic run inequality; full quantitative bound and simplified `3/(1216(h+1)²)` for `m≥2h+1`. |
| `lb:thm:upperrate`, `lb:thm:allm`, rigidity.tex | Unformalized | Open: midpoint construction under divisibility/oddness; parity-free one/two-center bins; omitted-action guards; exact second moments; at most `min(m,2h)` residual support and upper bounds. |
| `lb:cor:rate`, `lb:thm:naturalapprox`, unlabeled total-support corollary | Unformalized | Open: attained support minima; exact density; fixed-share and minimum-share inverse-square laws with separate tolerance ranges and constants. |
| `sp:cor:sharpk`, joint_support.tex | Unformalized | Open: mandatory clones and aggregation; worst-case total support `Theta(min(n,k+sqrt(M/η)))` for `k≥2`, `m≥2`, `0<η≤M`. |
| `ext:prop:stability`, graph_noise.tex | `response_perturbation` is the response-level ingredient | Open: independent interval projection preserving skew bounds, compact strategy-class minima and support-budget bridge. Response bound is `δ*r`; simplex mass one gives `δ`. |
| `ext:thm:noise`, graph_noise.tex | Unformalized | Open: uniform-family interval construction, lower transfer at `ε+δ`, matching upper law and origin; both exact shares and minimum shares. This is not a universal noise-sparsity theorem. |
| `ext:cor:corenoise`, graph_noise.tex | Unformalized | Open: altering only anchor-anchor entry, feasible clipped interval, all supported/omitted responses, matching law; fixed-share sharper scale `ε+3δ/8`. |
| `sp:cor:certificate`, algorithms.tex | `compactCompletion`, `compactCompletion_skew`, `compactCompletion_bounds`, `compactCompletion_response_on`, `compactCompletion_response_off`, `compact_certificate_responses_iff` | Residual block reconstruction and exact supported/omitted response equivalence are proved. The supplied support may contain zero-mass entries; only weights outside it must vanish. Open: full anchor-block bridge, additional repertoire constraints and arithmetic-operation cost. |
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
family-specific uncertainty law, none of which is claimed completed by this tranche.
Pinned Mathlib filename and term searches found no existing development of this
specific completion problem. This is not an exhaustive external overlap audit or
editorial novelty clearance. General finite sums, real algebra and convexity
infrastructure are reused, not claimed as new mathematics.

Future useful extensions: extend the proved residual compact-certificate reconstruction to rational full-game checking with
explicit anchor and repertoire constraints; generalize preserved moments to arbitrary finite
features; separate finite-grid certificates from square-root choices of grid size;
and derive row-specific perturbation bounds when only an observation cover moves.
These must be proved before receiving completed status.
