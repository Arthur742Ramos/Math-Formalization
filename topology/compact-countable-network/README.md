# Compact Hausdorff countable-network metrization

A compact Hausdorff space is metrizable if and only if it has a countable network of arbitrary subsets. Equivalently, it is second countable. The space and network may be empty, and the underlying type has an arbitrary universe. A metric witness induces exactly the original supplied topology.

A network member need not be open, closed or a neighborhood. The proof derives an actual countable open base in the compact Hausdorff case. The substantive bridge chooses Urysohn functions from pairs of network sets with disjoint closures. Regular shrinking guarantees that one such function takes values zero and one at any two distinct points. Countability then supplies a countable continuous separating family, to which existing canonical Mathlib compact metrization applies.

The package also proves preservation of networks under continuous surjections, heredity to every subspace, and metrizability of compact subspaces of Hausdorff countable-network spaces. The general closed embedding has codomain `(N × N) → ℝ` with coordinates in `[0,1]`; it is not stated as a literal interval-subtype or Nat-indexed Hilbert cube. See [DEFINITIONS.md](DEFINITIONS.md) for all exact contracts and hypotheses.

This classical criterion is used in contemporary function-space and generalized metric research: Tall, *Countable Tightness and the Grothendieck Property in Cp-Theory*, printed p.8; Gruenhage, *Spaces having a small diagonal*, printed p.5. Banakh's *P₀-spaces* supplies the standard arbitrary-subset network definition. [SOURCES.md](SOURCES.md) maps the consulted author manuscripts, scope and overlap. No novelty, priority or acceptance is claimed, and the original historical proof was not consulted.

## Attribution and review

Authors: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.

Responsible maintainers: Arthur Freitas Ramos; David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz.

These are separately confirmed roles under the standing campaign instruction. OpenAI Codex authored substantive proofs, tests and packaging under Arthur's authorization. Reviews are independent internal AI reviews; no human review is claimed, and no human proof contribution is inferred from the role lists. See [REVIEW.md](REVIEW.md).

## Build and verification

From this package directory use its own `lean-toolchain` and `lake-manifest.json`:

```sh
lake build
lake env lean AxiomAudit.lean > /tmp/countable-network-axioms.txt
python3 scripts/check_package.py --axiom-log /tmp/countable-network-axioms.txt
```

Lean is pinned to `leanprover/lean4:v4.35.0-rc2`, Mathlib to `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Six modules separately exercise Challenge and Solution contracts, exact definitions and semantic edge cases. All thirteen selected declarations have audited transitive dependencies within `propext`, `Classical.choice`, `Quot.sound`; both definitions and the network image theorem use no axioms. There are no proof holes or custom axioms. The proof and Challenge files are byte-identical; Solution publicly imports the proof module.

Ordinary Lean checking and internal review do not certify canonical Comparator/multi-kernel preflight, canonical Challenge rendering, current registry duplicate clearance, editorial acceptance or registration. Those remain separate gates. This package is a development draft and has not been submitted. Current limitations are recorded in [AUDIT.md](AUDIT.md); snapshot status is historical and must be read with later exact-source reports if any.

License: repository Apache-2.0. Classification: math.GN; MSC2020 54E35, 54D30.
