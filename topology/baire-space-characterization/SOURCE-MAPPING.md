# Source mapping and provenance

Primary theorem: Anush Tserunyan, Introduction to descriptive set theory,
Theorem5.4, printedp19, PDFpage18 (zero based), dated October21,2026.
https://www.math.mcgill.ca/atserunyan/Teaching_notes/dst_lectures.pdf
Retained PDF SHA256:523e7872328aa6136054effbcc194dbe4ff2da7f177257f5d317475540acab61.

Construction: Anush Tserunyan, Descriptive set theory problem set, Problem26(a,b),
printedp5, PDFpage4 (zero based), retained18page download.
https://homepages.math.uic.edu/~cdean8/docs/dst_problems.pdf
Retained PDF SHA256:b9cf370dee86d3a1fa6f33bf32411f996eb3f7e3e80cac64bd8fb776f601dcd5.
Another web-parser snapshot returned22pages and numbered it33. The citation
here is bound to the actual downloaded bytes. Both versions give the same
classical characterization and infinite clopen scheme strategy. The source
PDFs are retained outside this source package, not relicensed as local code.

Local exists_clopen_partition implements the hint by a genuinely infinite
survivor-index argument. exists_clopen_scheme and the complete/Polish
homeomorphism theorems implement the sufficient direction of Theorem5.4.
baire_hasClopenBasis, baire_compactInteriorEmpty and nonempty_homeomorph_iff
supply necessity and the exact full equivalence. No new mathematics attributed
to this formalization. The related Kechris book theorem is cited by sources;
its full proof was not independently consulted here.

Prior OpenBaire code reuse is acknowledged in module and README. Mathlib
CantorScheme, clopen operations, countable refinements, complete/total bounded
compactness and denumerable indexing are ingredients, not local novelty.
