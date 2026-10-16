# Mathematical sources and overlap

The directly consulted primary research manuscript is Gary Gruenhage,
*Spaces having a small diagonal*, arXiv:math/9910153v1 (27 October 1999),
https://arxiv.org/pdf/math/9910153v1. Printed p.1 recalls metrizability iff
Gδ diagonal for compact spaces. Printed pp.1–3 explain the surrounding
research in diagonal conditions, compact spaces and countable networks. PDF
SHA256: `28af90fe4bcce66fb34d812679baa968842ec423da6cc5cbef4057a4bfd4426c`.
The source's regular T1 convention is compatible with the explicit compact
Hausdorff hypotheses used here. We formalize its recalled classical criterion,
not the paper's new small-diagonal theorems.

Historical attribution to V. E. Sneider is retained in the project title. The
1945 original was not consulted, so this package claims no original theorem
number, verified page-level original proof mapping, or reproduction of that
proof. The proof supplied here is the compact-normal shrinking argument
followed by canonical uniform metrization.

The audience is general/set-theoretic topology: the Gδ-diagonal criterion is
used as a metrizability foundation in studying weaker diagonal properties and
countable-network conditions. This documents relevance of the actual theorem
proved. No weaker-diagonal, countably compact, new research, or priority claim
is made.

## Dated duplicate audit: 2026-10-16

The twelve existing Math-Formalization packages, remote branches, open PRs
(none at the check), and repository catalog contained no equivalent criterion.
Official registry-wide searches for `Sneider` returned no result; `diagonal`
returned 23 unrelated entries, with no next page; `compact metrizable`
returned the prior perfect-image and Dowker entries. The repository index had
eight public registrations and no matching new project. This is a dated
coverage audit, not a claim that no other formalization exists anywhere.

At Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, searches included
`IsGδ`, diagonal, countable neighborhood bases, compact uniformity and
metrization, with alternative name spellings. Existing coverage includes:

- `MetricSpace/PiNat.lean`: `MetrizableSpace.of_countable_separating` already
  metrizes compact spaces from a countable separating continuous family.
- `UniformSpace/OfCompactT2.lean`: `uniformSpaceOfCompactR1` builds the compact
  compatible uniformity directly from neighborhoods of the diagonal.
- `UniformSpace/Compact.lean`: `nhdsSet_diagonal_eq_uniformity`.
- `Metrizable/Uniformity.lean`: countably generated uniform metrization and
  compatible metric choice.
- `UrysohnsLemma.lean`: realizes compact Gδ sets as continuous level sets.

No equivalent Gδ-diagonal criterion or the used closed-Gδ cofinal-neighborhood
bridge was found. The new proof supplies that bridge explicitly and credits
all imported tools. Existing AU, Nagata–Smirnov, Smirnov and perfect-image
packages are different criteria and are neither imported nor modified.
