# Dowker's characterization

This package formalizes C. H. Dowker's Theorem 4 in *On countably paracompact
spaces*, Canadian Journal of Mathematics 3 (1951), 219–224,
[DOI 10.4153/CJM-1951-026-2](https://doi.org/10.4153/CJM-1951-026-2).

For any topological space `X`, the following three conditions are equivalent:

- `X` is normal and countably paracompact.
- `X × [0,1]` is normal.
- For arbitrary real upper semicontinuous `h` and lower semicontinuous `g`
  with `h x < g x` everywhere, there is a continuous real `f` with
  `h x < f x < g x` everywhere.

Countable paracompactness means every countable open cover has a locally finite
open refinement. That refinement can have any cardinality. The equivalence to
precise natural-number refinements is proved, including empty and finite covers.
Normality means separation of disjoint closed sets by disjoint open sets.
No T1 or Hausdorff condition on `X`, boundedness of `h` or `g`, or uniform gap
is assumed. Empty spaces are included.

The companion theorem proves that normal countably paracompact `X` has normal
product with every compact metrizable space. The proof actually establishes
the compact regular second-countable version. The decreasing-closed-sequence
characterization is also proved from the ordinary open-cover definition.

These are classical results. Their research audience includes general topologists
studying normal products and Dowker spaces, and researchers using real-function
insertion or homotopy extension. Dowker's characterization identifies the precise
additional covering property needed for the interval product. Hart's
[course notes, Chapter 4](https://fa.ewi.tudelft.nl/~hart/onderwijs/old-courses/settop/dowker.pdf)
explain the product and homotopy-extension context. No novelty, first-ever
formalization, or guaranteed Palomar acceptance is claimed.

Lean is pinned to `4.35.0-rc2` and canonical Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. From this directory:

```sh
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py
```

`Challenge.lean` is a transparent assembled copy of all proof modules, with only
canonical Mathlib imports. `scripts/assemble_challenge.py` reproduces it exactly.
It includes complete definitions and proofs, stays below the renderer's
1,000-line and 100-KiB limits, and can receive a readability warning for exceeding
300 lines. `Solution.lean` publicly imports the modular implementation.
`comparator.json` selects the exact declarations and definition values.

Project authors:

- Arthur Freitas Ramos
- David Barros Hulak
- Ruy Jose Guerra Barretto de Queiroz

Responsible maintainers:

- Arthur Freitas Ramos
- David Barros Hulak
- Ruy Jose Guerra Barretto de Queiroz

Codex agents authored the Lean implementation, package and metadata under
Arthur's authorization. Independent review is internal AI review. No human
mathematical review or external refereeing is claimed. See `formalization.yaml`
and `REVIEW.md` for provenance. The root Apache-2.0 license applies.

Local proof elaboration, Challenge and axiom checks passed. Hosted mechanical
preflight must pass on the exact published commit. This package has not been submitted to Palomar;
the parent task owns browser submission once the exact verified packet is ready.

