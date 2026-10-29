# Weak mixing and local Cantor scrambled families — development notes

Status: proof development only. No claim of package, canonical, kernel,
rendering, publication, or registry verification.

Proposed result: let X be a nonempty perfect Polish metric space and f a
continuous self-map on a space with at least two points such that the induced map on X × X is open-set transitive,
with time zero permitted. There is a positive δ such that every nonempty open
U contains a closed embedded Cantor set C for which every distinct pair x, y in C
returns arbitrarily late to distance less than ε for every ε > 0 and also
returns arbitrarily late to distance greater than δ. The witness times
may depend on the fixed pair, threshold and lower bound; the family is fixed for U and δ is global.

A stronger intermediate result asks each ordered distinct pair in C to have
dense forward orbit in X × X. A countable basis and square transitivity produce
the dense-open relations needed by the repository's binary Mycielski fusion.
Perfectness makes every nonempty open subset of X × X infinite; a dense orbit
therefore meets it beyond every finite time. This explicitly handles time zero.

Independent mathematical and source-scope review, 2026-10-29: this formulation
is sound; no compactness, surjectivity, or invariance claim is intended. The
reviewer checked the relation to:
Blanchard, Glasner, Kolyada and Maass, “On Li–Yorke pairs”,
https://www.imath.kiev.ua/~skolyada/LY.pdf. The classical literature also has
stronger dense Mycielski or all-arity statements; the local Cantor result here
does not claim these, and does not claim research priority.

The binary fusion result already exists in the repository at
topology/mycielski-cantor-independent/Mycielski/Independent.lean, base commit
a6fd933f00c83a82c4d7ab510d17ae62e87dc75f, Git blob
c0c0615effc8abd76b78470a6e61261d0aad8b94. The generic orbit and late-return
ideas use topology/ip-transitive-points/IPTransitive.lean at that commit, Git
blob 40afb48ddf57a1f7a35e2706d346ae6baaed9a54, with authorship and upstream
credit recorded in those source files. Both are Apache-2.0.

The independent bounded catalog and pinned Mathlib search found no matching
packaged Li–Yorke or scrambled-set theorem. Existing Cantor fusion,
strongly transitive sequences, and thick multisensitivity do not state the
fixed Cantor-family conclusion. A differently named equivalent result cannot
be ruled out by a text search.

The initial draft used retained Mycielski build artifacts. Later development checks compiled copied fusion sources into fresh Q: outputs while reusing pinned Mathlib artifacts. These checks do not establish a clean package build, canonical verification, or full source-bound validation.
