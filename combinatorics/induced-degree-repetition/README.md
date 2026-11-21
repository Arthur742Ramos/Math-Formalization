# Induced degree repetition — Lean formalization

The source is *A subexponential bound for induced degree repetition* by Arthur F. Ramos, David Barros Hulak and Ruy J. G. B. de Queiroz, in the 13-page PDF supplied with this project. Its SHA-256 is `66a9d8c4c5973a860c22d7d40c0407fdc8bc48b05e000559c02d977d8406ec5e`. MSC 2020 classes are 05C35 and 05C55.

Theorem 1 gives an induced subgraph on at least $r$ and fewer than $2r$ vertices, where $r=\lceil K\log N\rceil$. One degree must occur at least $(1-\eta)|S|$ times, counting degrees in the whole induced subgraph on $S$. The Lean proof establishes this for every positive K and every η between zero and one. It follows that the least Caro–Yuster threshold satisfies log g(k) = o(k).

[RemainingStatements.lean](RemainingStatements.lean) specifies Lemmas 3–5, 7–8 and 11, including the cut and operator-norm hypotheses, exponential error rates, order of quantifiers, and quantification over adaptive edit targets. The proposition names are shared by the source map and the proofs.

## Proof coverage

| Paper result | Lean declaration and file | Proof status |
| --- | --- | --- |
| Theorem 1 | `logScale_repetition` in [MainTheorem.lean](MainTheorem.lean) | Proved for every positive logarithmic scale, uniformly over all sufficiently large hosts. [Witness.lean](Witness.lean) also proves the exact Ramsey-range witness. |
| Corollary 2 | `subexponential_threshold` in [MainTheorem.lean](MainTheorem.lean), [Bounds.lean](Bounds.lean) and [Ramsey.lean](Ramsey.lean) | Proved unconditionally for the least threshold with the strict host-size convention. |
| Lemma 3 | `OpenProblems.density_reduction` in [DensityReduction.lean](DensityReduction.lean) | Proved for every positive logarithmic scale. Dependent random choice either produces a regular union of blocks or a set with two-sided cuts. A self-pair theorem derived from Mathlib’s Szemerédi regularity lemma then gives the uniform degree and Euclidean operator estimates. |
| Lemma 4 | `OpenProblems.biased_rectangle` in [BiasedRectangle.lean](BiasedRectangle.lean) | Proved the quantitative label bound for all dimensions and all moduli $q\ge3$. The direct proof uses weighted differences, the coset concentration theorem and character orthogonality. |
| Lemma 5 | `OpenProblems.adjacency_approximation` in [AdjacencyApproximation.lean](AdjacencyApproximation.lean) | Proved the disagreement bound over composite moduli. A maximum-score subrectangle controls the error on every strip. Iterating the strip complexity reduction gives a constant rectangle above the cut threshold. |
| Lemma 6 | `coset_concentration` in [Concentration.lean](Concentration.lean) | Proved for every probability weight on a finite abelian group annihilated by $q\ge2$. The constant is uniform in the group and weight. The proof uses counting convolution and the equivalent squared-norm inequality. |
| Lemma 7 | `OpenProblems.random_restrictions` in [RandomRestrictions.lean](RandomRestrictions.lean) | Proved for ordered samples with replacement. Selected rows and columns determine a model whose agreement probability is bounded by a counting argument. The row-mass exponent is $u/128$ for every subgroup budget. |
| Lemma 8 | `OpenProblems.conditional_residues` in [ConditionalResidues.lean](ConditionalResidues.lean) | Proved for all dyadic lengths in the statement. Iterated differences give decay on quotients, repeated Cauchy–Schwarz bounds the mixed sum, and a double count transfers the estimate to conditioned families. |
| Lemma 9 | `conditional_range` in [CountRange.lean](CountRange.lean) | Proved both integer atoms under the inherited cut bounds, uniformly over the conditioning family. The finite product allows repeated coordinates and uses ordered tuples. [GraphRange.lean](GraphRange.lean) specializes the result to graph adjacency and the exact disjoint-cut hypotheses of the paper. |
| Lemma 10 | `integer_totals` in [IntegerTotals.lean](IntegerTotals.lean) | Proved the uniform interior representation with modulus four, the odd-prime tests and one allowed exceptional position retaining its initial value. |
| Lemma 11 | `OpenProblems.simultaneous_adjustment` in [SimultaneousAdjustment.lean](SimultaneousAdjustment.lean) | Proved the joint probability estimate before the choice of rows and targets. The proof combines the two tuple lengths, the registered exterior profiles, and estimates for every profile on the other fresh rows. |
| Section 6 | [CoreWitness.lean](CoreWitness.lean), [EventualPlan.lean](EventualPlan.lean), [SampleSelection.lean](SampleSelection.lean) | The proof chooses disjoint equal-sized pools, then obtains one draw satisfying all four error bounds. A fourth-moment estimate applies to the adaptively chosen parity set. The edit preserves exterior profiles, and the discarded rows and auxiliary vertices fit the allowed error for each fixed η. |

The graph interface uses simple graphs on `Fin N`, with the chosen vertices represented by a finite set. `degreeOn_eq_induced_degree` identifies the neighbor count with Mathlib's induced graph degree. The threshold $g(k)$ is the infimum over integers $n\ge0$ for which every host of order strictly greater than $n$ contains an induced subgraph in which at least $k$ vertices have equal degree.

## Building and checking

Run the following commands in this package with the Lean toolchain in [lean-toolchain](lean-toolchain). Lake resolves exact dependency commits from [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake comparator --config comparator.json
```

[Challenge.lean](Challenge.lean) gives the independent statements using Mathlib imports and the deliberate statement-side placeholders of the Palomar template. [Solution.lean](Solution.lean) imports the proof modules. [comparator.json](comparator.json) selects all eleven numbered results, the Ramsey range, and the conditional corollary. The namespace name `OpenProblems` identifies the original statement interface. Every selected declaration has a proof. The Section 7 deletion identity is proved as `degreeOn_delete_exceptional`. The polynomial upper bound discussed there remains a research question. This local package has not been submitted to Palomar.

The proof of Lemma 6 reduces weighted concentration to ordinary additive energy in [WeightedEnergy.lean](WeightedEnergy.lean). It uses the ordinary Balog–Szemerédi–Gowers theorem in AddCombi and the bounded-torsion Freiman–Ruzsa theorem in PFR. The intended audience is researchers in extremal graph theory, Ramsey theory and additive combinatorics. The imported regularity, energy and bounded-torsion results support the paper-specific cut, sampling and exact degree-edit arguments. See [material imported definitions](MATERIAL-DEFINITIONS.md) for the pinned conventions.

## Attribution

The project authors are Arthur Freitas Ramos, David Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. Arthur Freitas Ramos is the responsible maintainer. OpenAI Codex wrote the Lean proofs. An independent internal AI reviewer examined all eleven numbered results, the parameter choices and the final induced witness against the manuscript. No human review of the Lean formalization is recorded.

- [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55)
- [Pinned AddCombi BSG proof](https://github.com/leanprover-community/add-combi/blob/b57ee30f6461e49a8ef212b463b20edd1f5de31d/AddCombi/BSG.lean)
- [Pinned bounded-torsion PFR proof](https://github.com/teorth/pfr/blob/ddd44f6ce82ef48624e468662e0fbeb5e37e4026/PFR/TorsionEndgame.lean)
- [Conlon–Fox, cited for Lemma 3](https://arxiv.org/abs/1107.4829)
- [Bhowmick–Dvir–Lovett, cited for Lemma 4](https://arxiv.org/abs/1204.1367)
- [Palomar template used for the package layout](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406)
