# Source and mathematical provenance

The proof module and axiom audit are ported from
[sorgenfrey-covering-lean, commit b60f28592f22a142949e48e50597bcacb05aebfe](https://github.com/Arthur742Ramos/sorgenfrey-covering-lean/tree/b60f28592f22a142949e48e50597bcacb05aebfe).
`reuse.json` records the original Git blob and source hash, plus the ported
file hash. The port adds module headers, public imports/declarations and three
explicit theorem certificates. It updates Lean to 4.35.0-rc2 and Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; the original standalone
repository and monorepo commit `95a3ceee2ad1ea240f89c6ece9343b1fd3fbb220`
remain available. Mathematical statements and proof arguments are preserved.

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
The port adds the actual pinned Palomar mechanical preflight. Its Challenge
contains the complete proof-bearing source and imports only canonical Mathlib,
so it can be compiled outside the candidate Lake plan. This duplication is
disclosed rather than presented as independent proof discovery. The separate
proposition specifications check the original statements independently.
Source attribution and licensing are retained; no registry acceptance is claimed.

Palomar cache compatibility: `SorgenfreyDefinitions.lean` is an exact copy of
`Counterexamples/SorgenfreyLine.lean` at the pinned Mathlib commit, including
Yury Kudryashov's attribution and complete declarations. The package checker
compares it byte-for-byte with the complete pinned definition evidence. The
Challenge inlines this source and imports its eight canonical Mathlib modules
plus Lindelof, avoiding an unavailable `Counterexamples` artifact. Solution
uses the same source as a local module. The lower-limit topology and all
mathematical statements are preserved.
