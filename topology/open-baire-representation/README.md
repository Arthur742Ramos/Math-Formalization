# Open Baire-space representation of Polish spaces

Every nonempty Polish space, with its given topology, is the image of Baire
space `ℕ → ℕ` under a continuous, open, surjective map. The domain has the
product topology of the discrete natural numbers. The empty Polish space is
excluded necessarily: the domain is inhabited.

This is a classical representation theorem, following David Marker,
*Descriptive Set Theory*, Fall 2002, Theorem 1.17 (printed page 6), with
supporting Lemmas 1.5–1.6. The nonempty hypothesis, omitted from the informal
theorem statement, is made explicit. Marker concludes openness as well as
continuity and surjectivity. Chen's *Notes on quasi-Polish spaces*, Section 10,
recalls this classical result and attributes it to Kechris Exercise 7.14.
No novelty or priority is claimed, and no quasi-Polish generalization is proved.

## Mathematical content

The construction covers each nonempty open set by countably many nonempty
open sets of a prescribed small diameter, with each closure contained in its
parent. These covers define a countably branching open scheme. Each infinite
branch has a unique limit inside all its open sets. Crucially, for every
finite prefix the image of its whole cylinder equals the corresponding open
set, rather than merely being contained or dense in it. This gives openness
and surjectivity of the limit map.

The exact cylinder-image theorem supplies reusable infrastructure for
descriptive set theory, open quotient representations and open-map transfer.
Our prior open-image package proves preservation along maps assumed to be
open. This package constructs those maps. Pinned Mathlib's existing Polish
representation theorem provides continuous surjectivity via a closed-subset
map and retraction; it does not supply openness. No claim is made about all
external formalizations or current private registry attempts.

| Selected declaration in `OpenBaire` | Exact scope |
| --- | --- |
| `exists_open_refinement` | Nonempty open subset of a second-countable metric space; any positive real diameter bound; countable open cover with nested closures. |
| `exists_open_scheme` | Nonempty second-countable metric space; a genuine open scheme with covering, closure and diameter contracts. Completeness is not needed here. |
| `OpenScheme.image_cylinder` | Any constructed-contract open scheme on a complete metric space; exact image of each basic Baire cylinder. |
| `exists_continuous_open_surjective_of_completeSpace` | Nonempty second-countable complete metric space. |
| `exists_continuous_open_surjective` | Nonempty Polish space with its supplied topology; a compatible complete metric is introduced only inside the proof. |
| `exists_continuous_open_surjective_iff_nonempty` | For any Polish space, existence of such a map is equivalent to nonemptiness. |

The list convention is inherited from `PiNat.res`: the newest coordinate is
prepended, `res x (n+1) = x n :: res x n`. The branch extension proof preserves
all prescribed initial coordinates and one prescribed point.

## Attribution and review

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de
Queiroz. Responsible maintainers, a separate role: Arthur Freitas Ramos;
David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz. These established
campaign roles do not assert human authorship of the generated Lean proof.

OpenAI Codex authored the new Lean proof, tests and packaging. Independent
internal AI reviewers assessed the primary-source scope and implementation.
No human mathematical review or external peer review is claimed. Upstream
generic scheme limits, continuity and completeness machinery are due to Felix
Weilacher's Apache-2.0 Mathlib `CantorScheme` development; Polish and metric
infrastructure are used with their original attribution. The new work is the
open covering scheme and exact cylinder-image proof.

## Reproduction and evidence

Lean is pinned to `leanprover/lean4:v4.35.0-rc2`; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, with the transitive lockfile retained.
Run `lake build` in this directory. `OBChallenge` contains the self-contained
proof and definitions using only pinned Mathlib imports; `OBSolution` imports
the separately compiled `OpenBaire`. No local project import is required by
the protected Challenge.

`comparator.json` selects six theorem targets, no definition holes, and only
the standard axioms `propext`, `Quot.sound` and `Classical.choice`. Verification
stages are certified by their own source-bound receipts outside the frozen
package. Native checks, protected canonical verification, Challenge rendering,
browser visual inspection, editorial review and registration are distinct
claims. A passing earlier source does not certify edited bytes. This package
does not claim public registration or an editorial decision.

Sources: [Marker](https://homepages.math.uic.edu/~marker/math512/dst.pdf),
[Chen](https://arxiv.org/pdf/1809.07440),
[pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55).
