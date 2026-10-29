# Draft Comparator decomposition for attainable regions

The manuscript's Corollary 3 is an exact criterion at an arbitrary fixed legal
root context. The package proves it directly as
`exact_relevant_region_realization` and `exact_region_realization`, and proves
`attainable_regions_context_independent` with possibly different witnesses.

The current proof-filled, self-contained Challenge for all those statements
measured 1,038 lines, above the observed 1,000-line single-file limit. The
present draft instead gives two distinct Challenge/Solution configurations:

- `comparator-region-nec.json` selects `determined_region_conditions`: every
  admissible mechanism's determinate region satisfies the criterion, with no
  relevance premise.
- `comparator-region-suff.json` selects `region_conditions_sufficient`: every
  region satisfying the criterion is realized by an admissible fully
  edge-relevant mechanism at the given legal context.

Together, these statements imply both relevant and unrestricted exact-region
characterizations and the context-independence corollary, because the criterion
does not mention the context and its witnesses can differ. The named
biconditional and context-independence theorems themselves are not selected in
either Comparator. The configurations would be separate entries if accepted;
neither alone represents the whole corollary or paper.

Both Challenges contain complete proofs and import `Init` only; they do not
import candidate-local helper files. Their line counts are 522 and 698 lines
respectively and remain above the 300-line readability warning. Their
wording, source closure, Comparator behavior, independent-kernel replays and
release eligibility still require final exact-source review and verification.
No Palomar submission or registration is claimed.
