# Generic strongly transitive sequences

For a continuous weakly mixing self-map f of a nonempty Polish space X,
a comeagre family of sequences x : Nat → X has every finite prefix dense
under its synchronized diagonal forward orbit. An actual nonempty dense
G-delta subfamily is obtained. Time0 and prefix0 are included.

The proof constructs transitivity of the countable product from finite
cylinders, proves residual dense orbits using a countable basis, then
projects a single coherent countable orbit to every finite prefix.
Residual membership alone needs no Baire assumption; density/nonemptiness
use the Baire property of the actual countable Polish product. No converse,
preselected-prefix extension, distinct-coordinate, compactness, perfection,
surjectivity or measure-mixing conclusion is claimed.

Nagar arXiv:1906.00712v4 Proposition2.30 and Remark2.31 provide the
strongly-transitive sequence scope. Hochman's June15 2022 Topological
Dynamics notes Proposition6.2 provide the countable-basis construction.
Both primary statements/proofs were directly inspected. The finite-family
Furstenberg infrastructure is copied with attribution from immutable source
9e5b57dba2ba9423cc8f12ff934bd07d86394c47, not claimed as new here.

StrongChallenge contains all proof code from Mathlib imports, including
the credited core; StrongSolution imports the separate StrongTransitive
and WeakMixingCore source. The five selected names in StrongTransitive are
residual_dense_orbits, countable_power_transitive, dense_prefix_orbit,
residual_strong_sequences and exists_dense_Gdelta_strong_sequences.
The construction proofs remain visible rather than hidden in an imported
statement equivalent to the target. Fixed DenseOrbit, initialSegment,
StrongSequence and inherited weak-mixing definitions have zero holes.

Only propext, Quot.sound and Classical.choice are allowed; no holes or added
axioms. Exact-source release readiness is established by immutable external
local native, canonical, rendering, visual and independent review receipts;
a build alone is not full certification. No intake or registration is claimed.

Campaign authors and responsible maintainers: Arthur Freitas Ramos;
David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz. Codex formalization
and separate internal AI reviews disclosed; no human proof contribution or
external peer review inferred. Mathlib and Lean core provenance is retained.

Run `lake build`, `python3 scripts/check_package.py`, and the pinned local
material/core-definition checkers. Repository AGENTS.md local validation
and independent release gates apply. No author-hosted CI workflow is added.
