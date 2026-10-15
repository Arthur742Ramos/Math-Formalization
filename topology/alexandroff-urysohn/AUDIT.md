# Scope, provenance and duplicate audit

Selected target: Alexandroff–Urysohn's intersecting-pair cover characterization,
Sakai Theorem 2.4.1(a)↔(b). The pointwise Frink condition (c) and the
star-refinement corollaries are not selected claims.

Primary source: Katsuro Sakai, *Geometric Aspects of General Topology*,
second-edition author manuscript, November 2, 2023; author-uploaded PDF SHA256
`d9a05e311296b68f59f761862eccba3d317ad8ce5555f11d18dad82b24657cfd`.
An independent internal AI reviewer downloaded the manuscript and visually
checked printed p.47 (PDF page 23), as well as the surrounding text. The source
statement spans printed pp.46–49. Cover openness, pair absorption and
neighborhood-basis stars match the Lean definition. Source Hausdorffness is
weakened to explicit T₀ for the metric formulation; the separation-free
formulation concludes pseudometrizability.

The result is a classical characterization with uses in metrizable quotients,
compact decompositions and metric adjustment to open covers. The source uses the equivalent Frink neighborhood criterion in
Proposition 2.4.5 and the barycentric/star-refining corollaries with quantitative
metric bounds in §2.6. These belong to the same classical equivalence family;
the applications and those additional formulations are context, not claims of
this package. The proposed
contribution is a formalized characterization and its explicit cover-to-uniformity
bridge, rather than a claim of new mathematics.

Before selection on 2026-10-15:

- Live remote heads and all 12 repository PRs were inspected. All existing PRs
  were merged; no competing new project branch or open PR was found.
- All 11 existing project scopes and their relevant source text were inspected.
  Only explanatory references to this criterion occurred in the perfect-image
  package. Its registered theorem is distinct and remains unchanged.
- An independent reviewer paginated all 561 public registry results at revision
  290, release `5deeddb2d24d8f78bbc18068eadb7befcc238b17662fcfc7135da4c65da0d7dc`.
  Complete snapshot SHA256:
  `cf6e3ef95a79c9f697ff685efee2795cb3996660ab34d88cbb9b8d296e771c11`.
  Titles, abstracts and declaration names revealed no equivalent AU,
  star-refinement or barycentric criterion. Related Smirnov and Nagata–Smirnov
  entries were checked as distinct.
- The pinned Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55` was
  searched across topology for the named and equivalent cover criteria. Existing
  second-countable Urysohn metrization and countably generated uniformity
  metrization are supporting results, not the selected cover characterization.
  The later upstream revision `cfc55fc58714a59dc06e6e79edc6d1d95140d3c2`
  was observed, but no complete audit of that later revision is claimed.

The uniformity/filter and metric machinery is credited to Mathlib, including
the authors of `Topology/Metrizable/Uniformity.lean` (Yury Kudryashov) and
`Topology/UniformSpace/Defs.lean` (Johannes Hölzl, Mario Carneiro, Patrick Massot).
Their source text is imported, not copied or attributed to this project.
The actual new proof is in `AlexandroffUrysohn.lean`, with a synchronized
canonical Challenge. No prior registered support theorem is relabeled as new.

These searches support a scoped nonduplication assessment, not a worldwide
priority claim or a promise of Palomar acceptance. Policy snapshot SHA256:
`32cfaa48ef8d51a6959df46f73ccff1482d8bbf89b4bb3f878498b518b11edcd`.
Both the minimum toolchain and the selected Mathlib pin match Lean 4.35.0-rc2.
Challenge size and repository-wide module/line constraints are checked by the
package checker. Every existing package tree is separately preserved by the
root catalog checker.
