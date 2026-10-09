# Source and mathematical provenance

The proof module and axiom audit are retained from
[sorgenfrey-covering-lean, commit b60f28592f22a142949e48e50597bcacb05aebfe](https://github.com/Arthur742Ramos/sorgenfrey-covering-lean/tree/b60f28592f22a142949e48e50597bcacb05aebfe).
`reuse.json` records the original Git blob, source hash, retained byte hash, and
any newline transformation. The proof declarations have no changes. The
standalone repository remains available. This nested package retains Lean
4.28.0 and the exact Mathlib pin.

The topology, clopen basis, separation properties and antidiagonal facts come
from Yury Kudryashov's attributed Mathlib file. The covering arguments are
classical. [Mizar TOPGEN_6 (2013)](https://mizar.uwb.edu.pl/fm/2013-21/pdf21-2/topgen_6.pdf)
already formalizes line Lindelöfness and plane non-Lindelöfness and non-normality.
No first-ever formalization claim is made.

The Mathlib Sorgenfrey file has its paracompactness TODO and no line Lindelöf
theorem at the pinned release, research commit
`a37dcbd570ffe4283df24efc20b144a09cc3661e`, and checked 2026-10-09 head
`a02a63c2100af866343c74550041885f8f39f099`. Scoped GitHub searches under
Arthur742Ramos and PalomarArchive returned no Sorgenfrey results before the
standalone publication. These are bounded overlap checks, not novelty claims.

The integration adds independent specifications, local contract checks,
metadata, definition evidence, verification scripts and path-specific CI.
It makes no registry submission. Source attribution and licensing are retained.
