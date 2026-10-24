# Weak mixing and thick common multi-sensitivity

A continuous surjective weakly mixing map on a nontrivial metric space has
one positive separation constant for which every finite family of nonempty
open sets admits arbitrarily long, arbitrarily late blocks of common positive
separation times. At each time and in each source set there are two points
whose images are strictly farther apart than this constant.

The same constant precedes every family size k and U : Fin k -> Set X.
Pairs may depend on the source set and time, including the block offset.
No fixed pair or tuple across the entire block is asserted. The empty family
k=0 is included: its set of common times is exactly the positive naturals.
Thick uses inclusive offsets0..L and arbitrary lower boundN; main uses start
N+1 to exclude time0. Underlying iteration includes0.

The proof selects separated open metric targets, refines all finite hitting
constraints to one open pair, and uses its thick hitting set. It does not
intersect arbitrary thick sets, whose intersection need not be thick. A
Bool-doubled family supplies two separated image witnesses per source set.
No compactness, minimality or separate no-isolated-points hypothesis is used.
Continuity and surjectivity of f are explicit; surjectivity is not derived.
The finite common-hit helper works on nonempty topological spaces; separated
targets need only a nontrivial metric space. No bounded-diameter API is used.

Liu, Liao and Wang, Thickly Syndetical Sensitivity of Topological Dynamical
System (2014), Theorem6, and Huang, Kolyada and Zhang, Multi-sensitivity,
Lyapunov numbers and almost automorphic maps, MPIM2014(52), definitions and
Proposition4.1 were directly inspected. This proof explicitly strengthens
the ordinary single-open thick-sensitivity and finite-intersection-nonempty
claims to common thick blocks, with the hypotheses above. It does not formalize
the hyperspace proof, transitive converse, M-system equivalences or entropy.
No tuplewise/IP, thickly syndetic or cofinite sensitivity theorem is claimed.

Credited WeakMixingCore comes from source9e5b57dba2ba9423cc8f12ff934bd07d86394c47.
HittingThicknessCore retains the literal Thick definition and hitting_thick
proof from source2fae123025f57f2f74220c01ffea7148fc6e3a11. Inherited proofs
are not new work. Sources and immutable links are in formalization.yaml.

Three compared declarations are in comparator.json. SensitivityChallenge
merges all proof sources with Mathlib-only imports; SensitivitySolution
imports implementation. All definitions fixed, no holes or new axioms.
Exact readiness is recorded by immutable external local native, canonical,
render, visual and independent review receipts; a build alone is not full
certification. No intake or registration claimed. Bounded overlap searches
do not establish novelty or editorial acceptance.

Authors and responsible maintainers: Arthur Freitas Ramos; David Barros Hulak;
Ruy Jose Guerra Barretto de Queiroz. Codex proof/internal AI reviews disclosed;
no human proof contribution or external review inferred. Exact Mathlib/Lean
provenance retained. Run lake build, python3 scripts/check_package.py and
complete root local AGENTS.md gates. No author-hosted CI added.
