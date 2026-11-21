# Induced degree repetition — partial Lean formalization

The source is *A subexponential bound for induced degree repetition* by Arthur F. Ramos, David Barros Hulak and Ruy J. G. B. de Queiroz, in the 13-page PDF supplied with this project. Its SHA-256 is `66a9d8c4c5973a860c22d7d40c0407fdc8bc48b05e000559c02d977d8406ec5e`. MSC 2020 classes are 05C35 and 05C55.

Theorem 1 asks for an induced subgraph on at least $r$ and fewer than $2r$ vertices, where $r=\lceil K\log N\rceil$. One degree must occur at least $(1-\eta)|S|$ times, counting degrees in the whole induced subgraph on $S$. The unrestricted theorem and its unconditional subexponential consequence remain open in this project.

## Proof coverage

| Paper result | Lean declaration and file | Proof status |
| --- | --- | --- |
| Theorem 1 | `LogScaleRepetition` in [Statement.lean](Statement.lean), `logScale_ramsey_range` in [Witness.lean](Witness.lean) | The full proposition is stated. For every $K>0$ with $K\log 4\le 1$ and every $N\ge2$, the proof gives an exactly regular induced subgraph with exactly $r$ vertices. The larger scales remain open. |
| Corollary 2 | `subexponential_of_logScale` in [Bounds.lean](Bounds.lean), `threshold_spec` and `threshold_le` in [Ramsey.lean](Ramsey.lean) | The threshold exists and is least under the paper's strict host-size convention. The paper's little-o conclusion follows from Theorem 1. |
| Lemma 3 | `ramsey_regular_witness` in [Ramsey.lean](Ramsey.lean) | Finite Ramsey bound proved. The density iteration, the Conlon–Fox regular self-pair input and the spectral conclusion remain open. |
| Lemma 4 | Bhowmick–Dvir–Lovett submatrix lemma, cited as [2, Lemma 6.3] | Open, including the passage from distinct vector sets to weighted labels and its quantitative loss. |
| Lemma 5 | `strip_card_bound` in [ModularMatrices.lean](ModularMatrices.lean) | Proved the kernel–image inequality for the two strips. The constant-rectangle recursion and its error and size bounds remain open. |
| Lemma 6 | `coset_concentration` in [Concentration.lean](Concentration.lean) | Proved for every probability weight on a finite abelian group annihilated by $q\ge2$. The constant is uniform in the group and weight. The proof uses counting convolution and the equivalent squared-norm inequality. |
| Lemma 7 | `row_column_image_card` in [ModularMatrices.lean](ModularMatrices.lean) | Row and column image sizes agree over composite moduli as well as primes. The random-restriction estimate with exponent independent of the subgroup bound remains open. |
| Lemma 8 | Conditional counts modulo $q$ | Open. The required estimate amplifies convolution decay on quotients and passes from restrictions to conditioned tuple families. |
| Lemma 9 | `conditional_range` in [CountRange.lean](CountRange.lean) | Proved both integer atoms under the inherited cut bounds, uniformly over the conditioning family. The finite product allows repeated coordinates and uses ordered tuples. |
| Lemma 10 | `integer_totals` in [IntegerTotals.lean](IntegerTotals.lean) | Proved the uniform interior representation with modulus four, the odd-prime tests and one allowed exceptional position retaining its initial value. |
| Lemma 11 | `simultaneous_edits` in [Adjustment.lean](Adjustment.lean), `small_profile_cells` and `exceptional_profile_lists` in [ProfileSampling.lean](ProfileSampling.lean) | Proved the deterministic edit construction, the small-profile bound and the union bound over other-row profiles in the product sample. The choice of lengths and the full probability estimate from Lemmas 8 and 9 remain open. |
| Section 6 | `gallai_even_partition` in [Gallai.lean](Gallai.lean), `parity_core` and `equalized_witness` in [Witness.lean](Witness.lean) | Proved the even partition, the retained size interval, common starting parity, and the final degree-count implication. The partition/sampling estimates, spectral control of the adaptive set and complete assembly remain open. |

The graph interface uses simple graphs on `Fin N`, with the chosen vertices represented by a finite set. `degreeOn_eq_induced_degree` identifies the neighbor count with Mathlib's induced graph degree. The threshold $g$k$$ is the infimum over integers $n\ge0$ for which every host of order strictly greater than $n$ has a degree class of size at least $k$.

## Building and checking

Run the following commands in this package with the Lean toolchain in [lean-toolchain](lean-toolchain). Lake resolves exact dependency commits from [lake-manifest.json](lake-manifest.json).

```sh
lake exe cache get
lake build Challenge Solution
lake env lean AxiomAudit.lean
```

[Challenge.lean](Challenge.lean) gives the independent statements using Mathlib imports and the deliberate statement-side placeholders of the Palomar template. [Solution.lean](Solution.lean) imports the proof modules. [comparator.json](comparator.json) selects both headline results, the three completed numbered lemmas, the Ramsey range, and the conditional corollary. The solution lacks the two unconditional headline declarations. A successful Lake build therefore does not certify the full comparator target. This is an unpublished development checkpoint, with no claim of Palomar verification or acceptance.

The proof of Lemma 6 reduces weighted concentration to ordinary additive energy in [WeightedEnergy.lean](WeightedEnergy.lean). It uses the ordinary Balog–Szemerédi–Gowers theorem in AddCombi and the bounded-torsion Freiman–Ruzsa theorem in PFR. The mathematical source authors are listed above. Codex wrote the Lean proofs. An AI source-fidelity review examined the main statement, the conditional corollary, Lemmas 6, 9 and 10, the deterministic edit construction and parity selection. No human review of the Lean project is recorded.

- [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55)
- [Pinned AddCombi BSG proof](https://github.com/leanprover-community/add-combi/blob/b57ee30f6461e49a8ef212b463b20edd1f5de31d/AddCombi/BSG.lean)
- [Pinned bounded-torsion PFR proof](https://github.com/teorth/pfr/blob/ddd44f6ce82ef48624e468662e0fbeb5e37e4026/PFR/TorsionEndgame.lean)
- [Conlon–Fox, cited for Lemma 3](https://arxiv.org/abs/1107.4829)
- [Bhowmick–Dvir–Lovett, cited for Lemma 4](https://arxiv.org/abs/1204.1367)
- [Palomar template used for the package layout](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406)
