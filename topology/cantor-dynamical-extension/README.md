# Cantor dynamical extension — local development

The sole target is the invariant-subset dense-forward-orbit extension theorem:
for a closed nowhere-dense subset A of the usual Cantor space N → Bool and any
homeomorphism f : A ≃ₜ A, construct an ambient homeomorphism H extending f and
a point whose forward H-orbit is dense. Empty A is included.

The full theorem `CantorDynamics.exists_extension_dense_forward_orbit` is proved
in `CantorDynamics/Extension.lean`. Exact-source release readiness is established
by immutable external verification/render/review receipts, not by this source
file. A successful Lean build alone is not full release certification.

The proof follows the orbit-embedding and shift-conjugation construction in
Andrzej Gutek, *Homeomorphisms on a Cantor set with subsequentially dense orbits*,
2012, Theorem 2.6, https://www.tntech.edu/cas/pdf/math/techreports/TR-2012-4.pdf.
Our target is only the invariant P=Q case and a dense forward orbit; it does not
claim the paper's stronger simultaneous positive/negative subsequence property
or arbitrary P,Q reduction. No novelty or acceptance claim is made.

The vendored KnasterReichbach files are byte-identical campaign infrastructure
from verified source caf9b142e9b7061c364499b5994dae4ab5bf4071, under the same
license. Their previous verification is historical evidence, not fresh checks
of this package. The new proof must establish the orbit embedding's topology,
closed nowhere-dense image, dense forward orbit for the full two-sided shift,
and the exact conjugation/extension identity. No such obligations are assumed
as hypotheses of the intended theorem.

Bounded overlap review found no corresponding result in the current campaign,
its three open topology PRs, pinned Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55,
or the public registry search. This is not a global formalization priority claim.
Independent internal AI scope review approved development with these limits.

Campaign authors and responsible maintainers: Arthur Freitas Ramos, David
Barros Hulak and Ruy Jose Guerra Barretto de Queiroz. OpenAI Codex performs the
formalization; no human proof contribution or human/external review is inferred.
All necessary validation is local under root AGENTS.md and the pinned Lean
4.35.0-rc2 toolchain. No intake, registration, or hosted CI is created here.

## Statement and proof interface

`DynamicsChallenge` contains the complete independent proof from Mathlib
imports; `DynamicsSolution` imports the separate project modules. Comparator
selects the final theorem with zero definition holes, protecting the statement
dependency closure. Separate semantic bridges establish that H^n means the nth
forward composition, its range is the set of all forward iterates, and Dense
means every point lies in its closure. Cantor space has the existing product
topology, and subsets retain the induced topology.

`OrbitEmbedding` proves the closed nowhere-dense image and the extended ambient
conjugating map. `DenseOrbit` constructs finite-coordinate patches, proves dense
open visiting sets, then applies Baire to all nonempty countable basic opens.
`Extension` proves the conjugation direction, powers and pointwise extension.
The only allowed axioms are propext, Quot.sound and Classical.choice.
