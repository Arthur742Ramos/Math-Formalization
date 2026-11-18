# Coverage of the manuscript

The source is the supplied *Regular induced subgraphs in bounded independent-edge arrays*
manuscript identified in the [README](README.md). A checked ingredient in the table is
a theorem about the paper's model. A row marked partial still requires the rest of
the named source result. Statements of conclusions alone are marked as such.

| Source | Lean coverage | Proofs still required |
| --- | --- | --- |
| Theorem 1.1, pp. 1–2 | All four statements in `Theorem11.lean`. | The two uniform logarithmic bounds and the three exact-order lower bounds. |
| Lemma 2.1, pp. 3–4 | Exact likelihood on individual graphs and constancy on a degree atom in `Tilt.lean`. The complete-graph quadratic identity is in `MeanDrift.lean`. | The centring tilt, its norm and entropy bounds, and the lower bound on the original atom. |
| Lemma 2.2, p. 4 | Pending. | The elementary symmetric mean, variance bound and two tails for sampling without replacement. |
| Proposition 2.3, pp. 4–5 | Pending. | Uniform candidate selection with parity rounding and the stated tilt, cardinality and success bounds. |
| Lemma 3.1, p. 5 | Independence for overlaps of at most one vertex is proved in `InducedIndependence.lean`. The scalar modulus estimate is in `BernoulliFourier.lean`. | The overlap conditional ratio, the averaged likelihood estimate and the fresh-edge bound (3.1). |
| §3, p. 5, estimate (3.2) | Pending. | The intersection probabilities of two uniform fixed-size sets. |
| Theorem 3.2, p. 6 | Pending. | The inverse-probability weighted second moment and estimates for both overlap ranges. |
| Theorem 4.1, pp. 6–7 | Pending. | Averaging restricted tilts and the large-overlap estimate at the balanced scale. |
| Theorem 4.2, p. 7 | Pending. | Near-balance of sampled blocks and amplification over disjoint blocks. |
| Lemmas 5.1–5.2, p. 8 | Pending. | Density increment and iterative extraction followed by trimming. |
| Theorem 5.3, p. 8 | Pending. | The logarithmic lower bound and its uniform failure probability. |
| Theorem 6.1, p. 9 | Pending. | Extraction of disjoint near-balanced domains from the large-cell hypothesis. |
| Corollary 6.2, p. 9 | The corresponding headline statement appears in `Theorem11.lean`. | Cube covering, the row-discrepancy bound and the conclusion. |
| Lemma 6.3, pp. 9–10 | Pending. | Bounded coefficients from a maximal minor, diagonal subdivision and the polarization bound. |
| Corollary 6.4, p. 10 | The corresponding headline statement appears in `Theorem11.lean`. | Transfer of the rank-cell estimate to the exact-order probability bound. |
| Remark 6.5, p. 10 | Pending. | The improved rate under the diagonal second-difference hypothesis and its smooth-kernel criterion. |
| Corollaries 7.1–7.3, pp. 10–11 | The amplified logarithmic bound is stated in `Theorem11.lean`. | Independent noise, almost-sure amplification and the random-environment transfer. |
| Proposition 8.1, p. 11 | The likelihood formula, its quadratic cost bound and the one-edge Fourier modulus are proved. | Scalar atom bounds, sequential exposure, tilted variance cost and the upper bound after summing degrees. |
| Theorem 8.2, p. 12 | Pending. | Both sides of the square-root estimate in the rank-one example. |
| Proposition 9.1, p. 12 | Proved in `MeanDrift.lean` and transferred to induced vertex sets in `UnionBounds.lean`. | |
| §9, p. 13, consequences | Both union bounds, the sufficient large-variation criterion and both necessary small-variation bounds are proved in `UnionBounds.lean`. | |
| Appendix A, Lemma A.1, pp. 13–14 | Covariance quadratic form and full-array spectral inequalities in `Covariance.lean`. | The spectral lower bound with an overlap removed and all inverse entry and row-sum bounds. |
| Appendix A, Lemmas A.2–A.3 and (A.3), pp. 14–15 | Pending. | Gaussian integration by parts, cubic characteristic function, quartic truncation and the joint expansion. |
| Appendix B, Lemma B.1, pp. 15–16 | Exact scalar modulus identity and exponential bound in `BernoulliFourier.lean`. | The good-coordinate localization, fiber comparison and small-box tail bound. |
| Appendix B, Theorem B.2, p. 17 | The degree-vector parity constraint, exact inversion and π-shift identity are in `Incidence.lean`, `Fourier.lean` and `FourierSymmetry.lean`. | The uniform centred asymptotic and its explicit exponential lower bound. |
| Appendix C, Proposition C.1, p. 17 | Exact Fourier inversion accepts the edge set with overlap edges removed. | The uniform estimate for every residual degree atom. |
| Appendix C, Corollary C.2, p. 17 | Pending. | Conditioning on the shared edges and the covariance-determinant ratio. |

The unrestricted questions in §§1 and 9 are recorded as open questions in the manuscript.
The source distinguishes exact order from a lower bound on the largest order. Both
events use the same underlying product law, with a union across larger cardinalities
in the latter case.

Before Palomar selection, the headline conclusions require unconditional Lean proofs,
an independent source-fidelity review, and the repository's verification procedure.
