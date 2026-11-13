# Sources, correspondence and overlap

## Primary computational-path sources

The bibliography cites Arthur Freitas Ramos and collaborators' identity-witness
and labelled-deduction papers, together with version 4 of *Topological
Computational Paths: Presentation Invariance and Observable Quotients*:
https://arxiv.org/html/2608.04228v4 . The four authors of that paper are Ramos,
de Queiroz, de Oliveira and de Veras. This must not be confused with the
prepared author list for this formal development.

The correspondence is to the paper's algebraic setup: signed composable words,
literal flattening of binary witnesses, word-coded interpretations, and
conservative introduction of abbreviations. No topological invariant,
homeomorphism, realization timing, geometric completeness or full LND_EQ
rewrite calculus is asserted.

## Existing AFP mathematics reused directly

Joachim Breitner's **Free Groups** entry is imported, not copied:
https://isa-afp.org/entries/Free-Groups.html . Its `Cancelation` theory supplies
signed letters, adjacent inverse cancellation, termination, confluence and
unique normal forms. `FreeGroups` supplies signed inversion and cancellation
of a word against its inverse. The new `cp_reduce` is an executable refinement
of its choice-defined `normalize`, not a new free-group construction.

In particular `rename_gens_normalize` already covers injective generator
renaming. The new presentation-change theorem is different: a new primitive
is accompanied by a defining equation, and elimination preserves all old
named equations and reflects equality of old words. Arbitrary old equations
are permitted, but no algorithm for deciding their congruence is claimed.

The AFP **Abstract Rewriting** source was also inspected. Importing its larger
session would add no needed mathematics here, because Free Groups already
uses the Isabelle distribution's `HOL-Proofs-Lambda.Commutation` confluence
infrastructure. Dependency source pins are retained in
`AFP_DEPENDENCY_SHA256SUMS`; the inspected, non-imported Abstract Rewriting
source is pinned separately in `OVERLAP_SOURCE_SHA256SUMS`.

## Prior project overlap

The preceding public dependent-HIT development contains typed walks, presented
hom-set quotients and path-valued interpretations:
https://github.com/Arthur742Ramos/hott-hit-dependent/tree/78b41c87152a1e7ed11ed97aac44b01e95796625 .
The inspected local theory hashes are retained separately in the validation
record. These concepts are acknowledged prior work, not novelty claims.
That entry is not a dependency of this standalone session. A later connection
requires an explicit conversion of signed letters, endpoint typing and
presentation equations; any equality reflection needs its own proof.

The new package concentrates on an executable AFP-based normalizer, typed
binary-witness reification, and explicit abbreviation conservativity and
roundtrips. This source-level overlap assessment is not a claim of complete
worldwide novelty or an editorial judgment of AFP suitability.
