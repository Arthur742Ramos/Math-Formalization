# Perfect surjections and paracompactness

A continuous closed surjection from a Hausdorff space with compact fibres
preserves and reflects paracompactness. If the domain is paracompact, the image
is also Hausdorff; no separation assumption on the target is needed.

This package formalizes the perfect-map invariant theorem in James R.
Munkres, *Topology*, second edition (2000), section 41, exercise 8(a),(b),
printed page 260. Section 31, exercise 7 supplies the perfect-map convention.
It also proves the regular-space criterion that every open cover admits a
locally finite refinement consisting of arbitrary sets, following Katsuro
Sakai's author-uploaded second-edition manuscript dated November 2, 2023,
chapter 2, Theorem 2.6.3(a),(e):
https://www.researchgate.net/publication/299698540_Metrization_and_Paracompact_Spaces
The webpage's 2013 publication metadata describes an older edition.

The six Comparator statements are:

- `PerfectParacompact.paracompact_iff`: the full equivalence, assuming only
  Hausdorffness of the domain, continuity, closedness, compact fibres and
  surjectivity.
- `PerfectParacompact.paracompact_t2_image`: the image is paracompact Hausdorff
  when the domain is paracompact Hausdorff.
- `PerfectParacompact.paracompact_preimage`: inverse transfer for arbitrary
  spaces, including empty fibres and nonsurjective maps.
- `PerfectParacompact.paracompact_image`: forward transfer with regular target
  and arbitrary paracompact domain.
- `PerfectParacompact.locallyFinite_image`: compact fibres and closedness
  transfer local finiteness of arbitrary indexed families.
- `PerfectParacompact.paracompact_iff_refinements`: the regular-space
  arbitrary-refinement criterion in both directions.

There are no metric, countability, local compactness, or uniform fibre-size
assumptions. Domain, target and family index universes are independent where
those objects occur. The cover criterion uses the same universe as Mathlib's
`ParacompactSpace`; passing through the range of a family permits larger
intermediate index types. Every statement uses ordinary Mathlib notions;
there are no new definitions whose values could change the claim.

The inverse proof chooses finite subcovers on fibres, uses closedness to get
target neighbourhoods, refines there, and pulls the refinement back. For the
image proof, compact fibres transfer local finiteness. The resulting image
sets can fail to be open. Two successive locally finite refinements and closed
unions produce an open refinement in the regular target. A closed continuous
surjection transfers normality and the T1 property, supplying target
regularity and Hausdorffness when the domain is paracompact Hausdorff.

This is classical general-topology infrastructure. Perfect maps occur in
decomposition and quotient constructions; the invariance theorem transports
the covering condition used for partitions of unity. For contemporary
specialist context, Vlad Smolin's *Perfect maps between submetrizable spaces*
(2026), https://arxiv.org/abs/2605.01509, studies perfect maps between
paracompact spaces. Its additional submetrizability results are not claimed
here. New contribution means the development and reusable Lean API added to
this collection, not mathematical novelty, formalization priority, or
guaranteed Palomar acceptance.

Lean is `v4.35.0-rc2`; canonical Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Run from this folder:

```sh
lake build
python3 scripts/check_package.py --axiom-log verification/local-axioms.txt
```

`Challenge.lean` is a complete proof-bearing copy of `Transfer.lean`, with only
Mathlib imports; `Solution.lean` imports the substantive proof module. This
keeps all source free of proof holes and added axioms while giving Comparator
distinct independently compiled modules. Challenge stays below the preferred
300-line review surface. `SemanticTests.lean` checks empty-domain and
nonsurjective inverse transfer, compact products without separation, and
proper-map image transfer in independent universes.

Project authors:
- Arthur Freitas Ramos
- David Barros Hulak
- Ruy Jose Guerra Barretto de Queiroz

Responsible maintainers:
- Arthur Freitas Ramos
- David Barros Hulak
- Ruy Jose Guerra Barretto de Queiroz

Codex authored the implementation and packaging under Arthur's authorization.
A separate Codex agent performed the independent source and implementation
review. See `AUDIT.md`, `REVIEW.md` and `verification/source-hashes.json`.
Machine checks and internal AI review are distinct; no human review is claimed.
