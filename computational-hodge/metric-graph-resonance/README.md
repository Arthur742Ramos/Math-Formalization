# Equilateral graph resonance and computational traces

Development draft for verification. Release and registry intake require
source-bound evidence for all applicable checks and independent review.

For verification-stage commit `96cc2fd1d3cfa63740ec433378015f58ced9c515`,
the pinned local full canonical report records Comparator acceptance by NanoDa
and Lean and acceptance by the con-ron kernel. Its SHA-256 is
`1588c423dbeb3cbef7f091391aee84331c8d0172fed3b2ab350381b5af605858`.
That evidence applies to the tested commit and does not certify later changes.
The local canonical Challenge render also passed for that tested commit;
its report SHA-256 is
`cdf3b1e41c44be2a90f7337be5282dbe229b5daf857974e596d90a7be605d7c3`.
The material inventory and bridge package remain a development draft. Check
applicable evidence against its exact tested source; inventory completeness,
visual inspection, semantic-provenance assessment and final release review
require separate assessment.

For finite connected oriented unit-edge multigraphs, continuous edge forcing,
and nonzero real `k` with `sin k = 0` and `cos k = 1`, the source characterizes
solvability of the edgewise first-order system `u' = q`, `q' = -(k^2 u + f)`,
with common vertex values and Kirchhoff balance. The conditions are zero total
cosine moment and an exact sine-moment edge cochain. An equivalent statement
uses zero sine-density integrals on every generated finite closed computational
trace. A separate theorem relates that density almost everywhere to a local
affine edge coordinate and its derivative, together with a local representation
of the realized quotient path.

The three-indexed-edge forcing example has zero total cosine moment and proves
that the first two edges cannot both match the same pair of endpoint values.
Its statement does not instantiate the full Kirchhoff theta graph or explicitly
exhibit a closed-trace period. The underlying graph and ODE mathematics are
classical; research significance and external acceptance are not established.

The package does not claim a general Hodge theorem, an intrinsic metric-graph
line integral, arbitrary continuous-path integrals, the usual metric topology
on the quotient, a kernel-dimension formula, or the omitted polynomial examples.
The stronger finite-switching theorem is outside this package.

The attributed upstream computational-trace excerpt and its pinned revision
are recorded in `source-provenance.json` and `SOURCE-LICENSE.txt`. Challenge
and Solution have common selected declaration headers but are different source
files; Challenge also contains additional public proof helpers. Definition-value
and material dependency-provenance checks, together with final independent
evidence review, require source-bound release evidence.
OpenAI Codex supplied substantive proofs and packaging. Arthur Freitas Ramos
confirmed the listed authors and designated himself as the sole responsible
maintainer. These roles do not imply individual human proof contributions or
human mathematical review.
