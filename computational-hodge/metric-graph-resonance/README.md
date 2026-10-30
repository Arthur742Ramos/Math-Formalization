# Equilateral graph resonance and computational traces

Development draft for verification. This packet is not verified for release or
registry intake. It has not passed the complete canonical, Comparator, kernel,
rendering, semantic-provenance or independent review gates.

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
files; Challenge also contains additional public proof helpers. Their semantic
Comparator, dependency-provenance and independent-kernel checks remain pending.
OpenAI Codex supplied substantive proofs and packaging. The proposed author and
maintainer names are carried from a prior Hodge project; their roles for this
project remain to be confirmed. They do not imply individual human proof
contributions or human mathematical review.
