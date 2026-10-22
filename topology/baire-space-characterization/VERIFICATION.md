# Verification boundaries

The package has eight theorem targets and no definition holes. The protected
Challenge imports only pinned Mathlib modules. It and the proof source have
equal bytes; Solution imports the proof source. All source uses the module
system. Only propext, Classical.choice and Quot.sound are permitted.

Native checks compile the Challenge under a different protected module name,
export both sides, run unchanged pinned Lake.Check.compareAt/checkAxioms and
all26primitive targets, and reject three independently altered fixed helpers:
ClopenScheme.limit, HasClopenBasis and CompactInteriorEmpty. Lean kernel,
NanoDa and verified con-ron then replay the exported solution. No comparator
or kernel boundary is weakened. Native receipts are separate from canonical
full workflow/rendering reports for an exact frozen commit.

Independent mathematical/source review and exact imported-predicate audit
cover the current proof. Machine compilation does not certify research
significance or informal correspondence. The external final packet must bind
all retained hashes, source commit, manifests, reviews, logs and actual full
and rendering reports. scripts/check_release_packet.py at repository root is
the final exact-source guard; status-only mode is not a verified handoff.
No registry, credential, merge or runner-security authority is granted here.
