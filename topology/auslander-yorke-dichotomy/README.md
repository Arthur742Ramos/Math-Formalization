# Auslander–Yorke dichotomy for minimal metric maps

Let f be continuous on a metric space and suppose every forward natural
orbit is dense. Then f is sensitive or its actual forward iterate family
is equicontinuous at every point. On a nonempty space, nonsensitivity is
equivalent to this equicontinuity, so the two alternatives are exclusive.

Sensitivity means one delta>0 such that each nonempty open U contains
a pair whose images at some natural time have distance strictly greater
than delta. Times include zero. Pairs and times depend on U. No anchored,
strictly positive-time, thick/multi/syndetic or cofinite variant is claimed.
On empty X this literal sensitivity convention is vacuously true, as is
equicontinuity. The unrestricted OR therefore is not exclusive there;
the exclusivity equivalence explicitly assumes Nonempty X.

The substantive propagation proof takes a stable open U at epsilon/2,
uses density of the orbit of x to find its hitting time k, and pulls U
back to a neighborhood of x. All later times are controlled by U, while
continuity controls the finitely many times before k. This proves actual
Mathlib Equicontinuous of the natural iterate family, pointwise in x.
No compactness, surjectivity, invertibility, nontriviality or separate
no-isolated-points assumption is used. No global uniform-equicontinuity
modulus or minimal-implies-surjective assertion is made.

Good, Leek and Mitchell, Equicontinuity, transitivity and sensitivity:
The Auslander–Yorke dichotomy revisited, DCDS40(2020)2441–2474,
doi:10.3934/dcds.2020121, authors PDF pp1–2, supplies the classical compact
metric scope and definitions. The direct pointwise statement here explicitly
drops compactness; uniform equicontinuity without compactness is not claimed.
The definition Minimal is credited to campaign source2fae123025f57f2f74220c01ffea7148fc6e3a11;
no prior proof is imported. The registered regional-proximal/equicontinuous-factor
TheoremsA–F PALOMAR-2026-10-20-000017 were examined and distinguished.
Sources and immutable links are in formalization.yaml. Bounded overlap
checks do not establish novelty or editorial acceptance.

Three selected declarations are in comparator.json. DichotomyChallenge
contains the complete proof with only Mathlib imports; DichotomySolution
imports the separate implementation. Fixed definitions, no holes or new axioms.
Exact readiness is recorded by immutable external local native, canonical,
render, visual and independent review receipts; a build alone is not full
certification. No intake or registration claimed. No author-hosted CI.

Authors and responsible maintainers: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz. Codex proof/internal AI reviews disclosed;
no human proof contribution or external review inferred. Exact Mathlib/Lean
provenance retained. Run lake build, python3 scripts/check_package.py and
all local root AGENTS.md gates.
