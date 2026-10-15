# Alexandroff–Urysohn cover metrization

A T₀ space is metrizable if and only if it has a sequence of open covers such
that any two intersecting members of cover `n+1` have their union contained in
one member of cover `n`, and the stars at each point form a neighborhood basis.
Without separation, the same cover condition characterizes pseudometrizability.
The space and each cover may have arbitrary cardinality. Empty spaces and
empty covers on them are included. No second countability, separability or
paracompactness hypothesis is imposed.

This is Theorem 2.4.1(a)↔(b) in Katsuro Sakai, *Geometric Aspects of General
Topology*, second-edition author manuscript dated November 2, 2023, printed
pp.46–49, statement on p.47. The author-uploaded manuscript is linked in
`formalization.yaml`. The source treats Hausdorff spaces; our metric statement
uses the weaker explicit T₀ hypothesis, and we also prove the separation-free
pseudometric formulation. The pointwise Frink condition in part (c), the
barycentric/star-refining corollaries, and quantitative bounds for a particular
chain metric are outside the selected scope.

The cover criterion is useful when a topology is given by covers rather than
coordinates. Sakai uses equivalent neighborhood and cover criteria from the same theorem
family for perfect images and closed gluing in Proposition 2.4.5, and for
metric adjustment in §2.6. Those applications are mathematical context, not
additional formalized results here. The audience is general topologists studying metrization, quotients and
compact decompositions. This formalizes classical mathematics; no new
mathematics, first-formalization priority or registry acceptance is claimed.

The proof constructs the co-membership relations `R n`: two points are related
exactly when they lie in one member of cover `n`. Pair absorption proves
`R (n+1) ○ R (n+1) ⊆ R n`. Covering and symmetry give the other uniformity
axioms. The resulting countably generated uniformity has exactly the supplied
topology, proved by comparing neighborhood bases. Mathlib's existing uniform
metrization theorem then supplies a compatible pseudometric; T₀ makes it a
metric. Conversely, balls of radius `(1/8)^n` satisfy the criterion. This is a
uniformity proof rather than the source's chain-metric proof.

All substantive proofs are new in this package. No project support modules are
copied from previous registered packages. Mathlib supplies uniform-space/filter
constructions, metrization of countably generated uniformities, compatible
metric choice, and elementary metric estimates. The previous perfect-image
project mentions this criterion in prose but proves its own theorem by a
different route; that mention is not an existing implementation of this result.
See `AUDIT.md` for the duplicate search and source mapping.

`AUChallenge.lean` is a canonical-Mathlib-only, proof-complete copy of
`AlexandroffUrysohn.lean`. `AUSolution.lean` publicly imports the reusable module.
The four selected theorems and four literal definitions are in `comparator.json`.
`DEFINITIONS.md` explains each definition. Build in this directory:

```sh
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py --axiom-log verification/local-axioms.txt
```

Lean is pinned to `leanprover/lean4:v4.35.0-rc2`, Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The manifest is independently
owned by this package. Use a normal Elan/Lake installation with these same pins. Existing package
pins and registered sources are preserved.

Authors and responsible maintainers: Arthur Freitas Ramos, David Barros Hulak,
and Ruy Jose Guerra Barretto de Queiroz, following the authorized campaign
attribution. OpenAI Codex authored the substantive formalization and packaging
under Arthur's authorization. Independent internal AI review and machine
verification are recorded separately in `REVIEW.md`; no human review is claimed.
Apache-2.0 license.

Local Lean checks are distinct
from Palomar's full protected Comparator/multi-kernel preflight. That full
preflight and Challenge rendering remain outstanding: this cloud host cannot
write its user-namespace UID map, and the pinned hosted installer can load an
AppArmor policy requiring specific approval. No such host change has been run.
No registry submission has been performed.
