# Coverage of the manuscript

The source is the supplied *Regular induced subgraphs in bounded independent-edge arrays*
manuscript identified in the [README](README.md). A checked ingredient in the table is
a theorem about the paper's model. A row marked partial still requires the rest of
the named source result. Statements of conclusions alone are marked as such.

| Source | Lean coverage | Proofs still required |
| --- | --- | --- |
| Theorem 1.1, pp. 1–2 | All four statements in `Theorem11.lean`. | The two uniform logarithmic bounds and the three exact-order lower bounds. |
| Lemma 2.1, pp. 3–4 | The centring tilt, uniform floor, and both norm estimates are proved in `CentringTilt.lean` and `TiltQuantitative.lean`. `Tilt.lean` proves the exact likelihood, and `TiltEntropy.lean` bounds its logarithm on the centred atom. `AtomLowerDeduction.lean` proves the lower-bound transfer from the tilted atom. | The centred lower bound from Theorem B.2. |
| Lemma 2.2, p. 4 | The elementary symmetric mean, variance bound, and two-sided tail bound are proved in `SymmetricMean.lean` and `SamplingMoments.lean`. The expectations and probabilities use equal weights over the finite family of samples. | |
| Proposition 2.3, pp. 4–5 | `CandidateRounding.lean` proves admissible parity rounding for an interior target. | Uniform candidate selection and the stated tilt, cardinality and success bounds. |
| Lemma 3.1, p. 5 | Independence for overlaps of at most one vertex is proved in `InducedIndependence.lean`. `FreshEdgeAtoms.lean` proves the product of the scalar atom bounds for the residual constraints after any overlap assignment of positive probability. | The joint-probability ratio, the averaged likelihood estimate and the use of the fresh-edge estimate in (3.1). |
| §3, p. 5, estimate (3.2) | Both bounds on the intersection probabilities of two uniform fixed-size sets are proved in counting form in `IntersectionProbability.lean`. | |
| Theorem 3.2, p. 6 | `WeightedSecondMoment.lean` proves the failure bound in terms of the inverse-probability weighted second moment. `OverlapSecondMoment.lean` groups it by intersection size, cancelling overlaps of size zero and one. | The ratio estimates for both overlap ranges and the resulting uniform failure rate. |
| Theorem 4.1, pp. 6–7 | Pending. | Averaging restricted tilts and the large-overlap estimate at the balanced scale. |
| Theorem 4.2, p. 7 | Pending. | Near-balance of sampled blocks and amplification over disjoint blocks. |
| Lemma 5.1, p. 8 | `DensitySurplus.lean`, `BernoulliLowerTail.lean`, and `DensityIncrement.lean` prove the density increment by biased independent sampling. | |
| Lemma 5.2, p. 8 | `DensityIteration.lean` proves density iteration and the final induced-domain theorem. `TrimDegrees.lean` and `DegreeDeletion.lean` prove the trimming and degree-loss estimates. | |
| Theorem 5.3, p. 8 | Pending. | The logarithmic lower bound and its uniform failure probability. |
| Theorem 6.1, p. 9 | Pending. | Extraction of disjoint near-balanced domains from the large-cell hypothesis. |
| Corollary 6.2, p. 9 | `CubeCells.lean` proves the cube covering and bounds the range of the kernel entries. `CellRowBalance.lean` proves (6.1) with the stated size and row discrepancy. The headline statement appears in `Theorem11.lean`. | The probability conclusion through Theorem 6.1. |
| Lemma 6.3, pp. 9–10 | Pending. | Bounded coefficients from a maximal minor, diagonal subdivision and the polarization bound. |
| Corollary 6.4, p. 10 | The corresponding headline statement appears in `Theorem11.lean`. | Transfer of the rank-cell estimate to the exact-order probability bound. |
| Remark 6.5, p. 10 | Pending. | The improved rate under the diagonal second-difference hypothesis and its smooth-kernel criterion. |
| Corollaries 7.1–7.3, pp. 10–11 | `AlmostSure.lean` proves the almost-sure conclusion given the stated marginal failure bound. | Independent noise, the quantitative amplification and the random-environment transfer. |
| Proposition 8.1, p. 11 | Both bounds are proved in `RegularAtomUpper.lean` and `RegularUpper.lean`. `OrderUpper.lean` transfers the regularity bound to arbitrary finite ordered vertex sets and proves the two order-tail estimates following the proposition. | |
| Theorem 8.2, p. 12 | The finite first-moment estimate and the asymptotic square-root upper bound are proved in `LinearProductUpper.lean`. `LinearProductStructure.lean` proves rank-one completion and a one-dimensional Lipschitz representation at each prescribed edge floor. | The square-root lower bound through Corollary 6.2. |
| Proposition 9.1, p. 12 | Proved in `MeanDrift.lean` and transferred to induced vertex sets in `UnionBounds.lean`. | |
| §9, p. 13, consequences | Both union bounds, the sufficient large-variation criterion and both necessary small-variation bounds are proved in `UnionBounds.lean`. | |
| Appendix A, Lemma A.1, pp. 13–14 | `Covariance.lean`, `OverlapCovariance.lean`, and `OverlapInverse.lean` prove the quadratic and inverse bounds. `WeightedCovariance.lean` proves the positive-weight extension and gives constants at every fixed overlap fraction. `CovarianceDetBound.lean` gives the determinant upper bound. | |
| Appendix A, (A.1), p. 14 | `GaussianMvPolynomial.lean` proves Gaussian Poincaré for multivariate polynomials via `GaussianPolynomial.lean`, `ProductVariance.lean` and `GaussianTensorization.lean`. `GaussianConcentration.lean` proves the exponential moment bound for Lipschitz functions. | |
| Appendix A, Lemmas A.2–A.3 and (A.3), pp. 14–15 | `GaussianEdgeCovariance.lean` and `GaussianFrame.lean` prove the edge covariance bounds and (A.2). `GaussianCubicMoment.lean` bounds the cubic second moment. `GaussianCubicStein.lean` proves the generator identity and the equality of the cubic second moment and the expected gradient product. `GaussianQuarticMoment.lean` bounds the quartic second moment, and `GaussianLinearTail.lean` controls the Gaussian mass outside the box. `GaussianQuarticConcentration.lean` applies the exponential estimate to the clipped quartic. `GaussianWeightApproximation.lean` bounds the errors from clipping and truncating. `GaussianChangeOfVariables.lean` proves the Gaussian change of variables. `FourierLocalExpansion.lean` and `FourierBoxRemainder.lean` prove the expansion and the uniform shrinking-box remainder. `FourierGaussianAssembly.lean` gives the error bound for combining the expansions. | The cubic differential error estimate and the uniform asymptotic deductions from the finite Gaussian estimates. |
| Appendix B, Lemma B.1, pp. 15–16 | `FourierOuterTail.lean` proves the finite exterior estimate with the many-bad-edge term and an explicit factor times the total integral. `FourierPhaseAnnulus.lean` proves the finite annulus estimate on the torus and its extension to the π mode by translation. `FourierTailAssembly.lean` combines these estimates given a bound on the mass in the two small boxes. `FourierTailRates.lean` proves the scalar limits for the two estimates. | The uniform bound on the small-box mass and the choices of parameters in the finite estimates. |
| Appendix B, Theorem B.2, p. 17 | The degree-vector parity constraint, exact inversion and π-shift identity are in `Incidence.lean`, `Fourier.lean` and `FourierSymmetry.lean`. `FourierPeaks.lean` proves the exact two-peak and tail decomposition. `AtomLowerDeduction.lean` converts a positive constant multiple of the Gaussian normalization into the stated exponential scale. | The uniform centred asymptotic and positivity of the leading coefficient. |
| Appendix C, Proposition C.1, p. 17 | Exact Fourier inversion accepts the edge set with overlap edges removed. | The uniform estimate for every residual degree atom. |
| Appendix C, Corollary C.2, p. 17 | The determinant comparison is proved in `OverlapDeterminant.lean`. `OverlapConditioning.lean` proves the exact conditional residual atom and positivity of each assignment under interior probabilities. `OverlapProbabilityRatio.lean` combines these results with atom bounds. | The uniform probability ratio using Theorem B.2 and Proposition C.1. |

The unrestricted questions in §§1 and 9 are recorded as open questions in the manuscript.
The source distinguishes exact order from a lower bound on the largest order. Both
events use the same underlying product law, with a union across larger cardinalities
in the latter case.

The fixed-floor example after Theorem 8.2 uses vertex weights in the
interval from `√ξ` to `√(1−ξ)`. The endpoints follow from requiring all
products of two weights to lie in `[ξ, 1−ξ]`.

Before Palomar selection, the headline conclusions require unconditional Lean proofs,
an independent source-fidelity review, and the repository's verification procedure.
