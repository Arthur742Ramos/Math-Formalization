# Weak mixing and equicontinuous metric factors

Weak mixing transfers through continuous surjective semiconjugacies. One
equicontinuity point of the actual natural iterate family forces a weakly
mixing metric space to have at most one point. Every equicontinuous metric
factor of a weakly mixing topological map is therefore subsingleton.

The metric proof chooses separated target balls, sends two points from one
small source ball to them at a common weak-mixing time, and contradicts
equicontinuity by the triangle inequality. Factor transfer uses actual open
preimages and the semiconjugacy iterate identity. No compactness, minimality,
invertibility, continuity or surjectivity of f/g is assumed. Only the factor
map is assumed continuous and surjective. The one-point helper has an explicit
point x; the main theorem needs no global nonemptiness. Subsingleton means at
most one point, so empty cases assert no nonexistent point.

OrbitEquicontinuousAt is literal Mathlib EquicontinuousAt of all f^[n], with a
separately proved epsilon-delta bridge. Global Equicontinuous means this at
every point. Natural time0 is included. No converse, uniform sensitivity,
maximal-factor construction or regional-proximality claim is made.

Michael Hochman, Notes on Topological Dynamics, June15 2022, Proposition6.12
and Corollary6.13 were directly inspected:
https://math.huji.ac.il/~mhochman/courses/TD2022/notes-v3.pdf
The compact metric scope is strengthened using direct separation, without
importing the source's isometry reduction. Credited WeakMixingCore comes from
source9e5b57dba2ba9423cc8f12ff934bd07d86394c47; inherited finite-family proofs
are not newly claimed. Related registered regional-proximal theory
PALOMAR-2026-10-20-000017v1 proves different A–F claims for minimal compact
semigroup actions. Bounded equivalent-statement checks do not establish novelty.

Three selected declarations are in comparator.json. EquicontChallenge merges
the credited core and new proof with Mathlib-only imports; EquicontSolution
imports implementation. All definitions fixed, no holes or added axioms.
Exact-source readiness is recorded in immutable external local native,
canonical, rendering, visual and independent review receipts; a build alone
is not full certification. No intake or registration is claimed.

Authors and responsible maintainers: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex proof development and separate
internal AI review disclosed; no human proof contribution or external review
inferred. Exact Mathlib/Lean source provenance retained. Run lake build,
python3 scripts/check_package.py and complete root local AGENTS.md gates.
No author-hosted CI is added.
