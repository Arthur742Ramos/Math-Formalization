# Coverage of the manuscript

The source is the supplied *Regular induced subgraphs in bounded independent-edge arrays*
manuscript identified in the [README](README.md). A checked ingredient in the table is
a theorem about the paper's model. A row marked partial still requires the rest of
the named source result. Statements of conclusions alone are marked as such.

| Source | Lean coverage | Proofs still required |
| --- | --- | --- |
| Theorem 1.1, pp. 1–2 | All four statements in `Theorem11.lean`. | The two uniform logarithmic bounds and the three exact-order lower bounds. |
| Lemma 2.1, pp. 3–4 | `TiltedDegreeAtom.lean` proves the centring tilt, uniform probability interval, both norm estimates, exact likelihood, likelihood cost and atom lower bound. The likelihood identity on individual graphs is in `Tilt.lean`. | |
| Lemma 2.2, p. 4 | The elementary symmetric mean, variance bound, and two-sided tail bound are proved in `SymmetricMean.lean` and `SamplingMoments.lean`. The expectations and probabilities use equal weights over the finite family of samples. | |
| Proposition 2.3, pp. 4–5 | `CandidateRounding.lean` proves admissible parity rounding. `SampleDriftTail.lean` proves that at least half the samples satisfy both drift bounds, and `CandidateDriftRates.lean` proves the uniform scalar estimates. `InducedDegreeTargets.lean` gives the fixed-degree event on induced arrays and its law under reindexing. `CandidateSets.lean` proves the full candidate-family theorem, including the tilt and success bounds. | |
| Lemma 3.1, p. 5 | `InducedIndependence.lean` proves independence for small overlaps. `SharedTiltConditioning.lean` proves the change of measure on the overlap and the sum-of-squares bound for the logit shifts. `SharedTiltMoment.lean` bounds the expected product of the two likelihoods. `LocalEdgeEvents.lean` and `OverlapAssignmentPartition.lean` prove conditional factorization for disjoint residual supports and the finite averaging identities. `InducedFreshBound.lean` proves the fresh-edge inequality (3.1), its bound after normalization, and the exact independent case. `InducedOverlap.lean`, `InducedConditionalRatio.lean`, and `SharedRatioAveraging.lean` prove the shared-assignment factorization, reindexing, and conditional-ratio averaging. `CandidateSharedLikelihood.lean` proves the moderate-overlap bound with coefficient `j/4` on the sum of the restricted energies, the coefficient obtained in the proof and used in §4. | |
| §3, p. 5, estimate (3.2) | Both bounds on the intersection probabilities of two uniform fixed-size sets are proved in counting form in `IntersectionProbability.lean`. | |
| Theorem 3.2, p. 6 | `WeightedSecondMoment.lean` proves the failure bound in terms of the inverse-probability weighted second moment. `OverlapSecondMoment.lean` groups it by intersection size, cancelling overlaps of size zero and one. `MeanSquareOverlapRates.lean` proves the geometric overlap sums at the prescribed rates. `MeanSquareInducedRegularity.lean` proves the uniform failure bound and its improvement at zero imbalance. | |
| Theorem 4.1, pp. 6–7 | `IntersectionSampling.lean` proves uniformity of intersections of fixed size. `SupportedSecondMoment.lean` proves the Cauchy–Schwarz lower bound for a count supported on the success event. `OverlapTiltAverage.lean` and `BalancedOverlapAverage.lean` prove the small-overlap tilt average. `BalancedLargeOverlap.lean` proves the exponential estimate for each large-overlap term. | The bounded weighted second moment and the positive success probability. |
| Theorem 4.2, p. 7 | `RowSampleApproximation.lean` proves the row-mean approximation on retained vertices. `IndependentEdgeFamilies.lean` proves the joint product law on disjoint blocks. `BlockRegularAmplification.lean` proves the failure bound from local block success. `BlockSizeRates.lean` verifies the block-size estimates. | Existence of a partition with sufficiently many good blocks and the application of Theorem 4.1. |
| Lemma 5.1, p. 8 | `DensitySurplus.lean`, `BernoulliLowerTail.lean`, and `DensityIncrement.lean` prove the density increment by biased independent sampling. | |
| Lemma 5.2, p. 8 | `DensityIteration.lean` proves density iteration and the final induced-domain theorem. `TrimDegrees.lean` and `DegreeDeletion.lean` prove the trimming and degree-loss estimates. | |
| Theorem 5.3, p. 8 | Pending. | The logarithmic lower bound and its uniform failure probability. |
| Theorem 6.1, p. 9 | `NearBalancedBlockPacking.lean` proves the deterministic extraction of disjoint near-balanced blocks from the finite large-cell property and the sampling tolerance. `LargeCellScale.lean` verifies the available block size at the stated exponent. `LargeCellAmplification.lean` gives the full transfer from the local block-success bound. | The probability conclusion through Theorem 4.1. |
| Corollary 6.2, p. 9 | `CubeCells.lean` proves the cube covering and bounds the range of the kernel entries. `CellRowBalance.lean` proves (6.1) with the stated size and row discrepancy. `StructuralLargeCells.lean` packages the large-cell property and the headline statement appears in `Theorem11.lean`. | The probability conclusion through Theorem 6.1. |
| Lemma 6.3, pp. 9–10 | `BoundedRowCoordinates.lean` proves bounded coordinates using a maximum determinant in the row span. `RankCells.lean` proves the cell-size constant and range bound using diagonal subdivision and polarization. | |
| Corollary 6.4, p. 10 | `RankCellRowBalance.lean` proves the finite near-balance hypothesis with exponent `(r + 1) / 2`. `StructuralLargeCells.lean` packages the large-cell property and the headline statement appears in `Theorem11.lean`. | The exact-order probability bound through Theorem 6.1. |
| Remark 6.5, p. 10 | Pending. | The improved rate under the diagonal second-difference hypothesis and its smooth-kernel criterion. |
| Corollaries 7.1–7.3, pp. 10–11 | `AlmostSure.lean` proves the almost-sure conclusion given the stated marginal failure bound. `NoisyAndRandomEnvironment.lean` proves the noise model's floor and degree means, and the random-environment transfer for a measurable graph-law kernel. `ConsecutiveBlocks.lean` constructs disjoint blocks of uniform size. | The uniform noise conclusion and quantitative amplification through the main lower bounds. |
| Proposition 8.1, p. 11 | Both bounds are proved in `RegularAtomUpper.lean` and `RegularUpper.lean`. `OrderUpper.lean` transfers the regularity bound to arbitrary finite ordered vertex sets and proves the two order-tail estimates following the proposition. | |
| Theorem 8.2, p. 12 | The finite first-moment estimate and the asymptotic square-root upper bound are proved in `LinearProductUpper.lean`. `LinearProductStructure.lean` proves rank-one completion and a one-dimensional Lipschitz representation at each prescribed edge floor. | The square-root lower bound through Corollary 6.2. |
| Proposition 9.1, p. 12 | Proved in `MeanDrift.lean` and transferred to induced vertex sets in `UnionBounds.lean`. | |
| §9, p. 13, consequences | Both union bounds, the sufficient large-variation criterion and both necessary small-variation bounds are proved in `UnionBounds.lean`. | |
| Appendix A, Lemma A.1, pp. 13–14 | `Covariance.lean`, `OverlapCovariance.lean`, and `OverlapInverse.lean` prove the quadratic and inverse bounds. `WeightedCovariance.lean` proves the positive-weight extension and gives constants at every fixed overlap fraction. `CovarianceDetBound.lean` gives the determinant upper bound. | |
| Appendix A, (A.1), p. 14 | `GaussianMvPolynomial.lean` proves Gaussian Poincaré for multivariate polynomials via `GaussianPolynomial.lean`, `ProductVariance.lean` and `GaussianTensorization.lean`. `GaussianConcentration.lean` proves the exponential moment bound for Lipschitz functions. | |
| Appendix A, Lemmas A.2–A.3 and (A.3), pp. 14–15 | `GaussianCubicUniform.lean` proves the bounded cubic second moment and the characteristic error of order `k⁻¹ᐟ²`. `GaussianQuarticUniform.lean` proves the bounded quartic mean and uniform convergence of the truncated quartic weight in L¹. `FourierCenteredPeak.lean` and `FourierModulusApproximation.lean` prove the two uniform small-box expansions with normalized Haar measure. The modulus estimate also works after deletion under the covariance lower bound. | |
| Appendix B, Lemma B.1, pp. 15–16 | `eventually_integral_degreeFourier_outside_small_boxes_le_uniform` in `ResidualLocalLimit.lean` proves the uniform normalized tail estimate over the complement of both peaks, including permitted deletions. | |
| Appendix B, Theorem B.2, p. 17 | `centered_degreeAtom_uniform_asymptotic_of_variance_floor` in `CenteredDegreeAtom.lean` proves the asymptotic with uniform relative error, a positive constant times the Gaussian normalization, and the stated exponential lower bound. | |
| Appendix C, Proposition C.1, p. 17 | `probability_residual_degreeAtom_le_uniform` in `ResidualLocalLimit.lean` proves the bound with a constant and threshold uniform over the permitted deletions, probabilities and integer target vectors. | |
| Appendix C, Corollary C.2, p. 17 | `ConditionalDegreeRatio.lean` proves the uniform bound on the conditional-to-unconditional probability ratio using Theorem B.2, Proposition C.1 and the determinant comparison. | |

The unrestricted questions in §§1 and 9 are recorded as open questions in the manuscript.
The source distinguishes exact order from a lower bound on the largest order. Both
events use the same underlying product law, with a union across larger cardinalities
in the latter case.

The fixed-floor example after Theorem 8.2 uses vertex weights in the
interval from `√ξ` to `√(1−ξ)`. The endpoints follow from requiring all
products of two weights to lie in `[ξ, 1−ξ]`.

Before Palomar selection, the headline conclusions require unconditional Lean proofs,
an independent source-fidelity review, and the repository's verification procedure.
