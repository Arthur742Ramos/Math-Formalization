# Dependency blueprint and release gates

The present milestone is a compiled integration and representative pilot.
The intended next mathematical milestone is actual E1 degeneration for the
column filtration of a bounded double complex over a field satisfying the
explicit `d′d″` identities. Completion means all higher differentials vanish
and the stable-page comparison is proved. Showing only `d₁ = 0` is insufficient.

## Evidence already available

| Component | Artifact | Status |
| --- | --- | --- |
| Actual bicomplex and totalization | `Integration.lean` | Compiled |
| Explicit boundary correction | `Representative.lean` | Proved |
| All vertical homology classes have biclosed representatives | `Representative.lean` | Proved using canonical mathlib homology isomorphisms |
| Soundness of representatives in the actual total complex | `TotalRepresentative.lean` | Proved |
| Sign involution, anticommutation, square-zero, kernel/range preservation | `SignBridge.lean` | Proved at operator level |
| Conventional E1 indexing data | `Indexing.lean` | Proved; no associated sequence yet |
| Transitive axiom dependencies | `AxiomAudit.lean` | Standard three only |
| Protected Comparator / other kernels / rendering | None | Not run |

## Remaining mathematical work

1. Package boundedness as vanishing outside an integer rectangle, and package
   the two DGMS (5.15)(b) identities as explicit submodule equalities at every
   bidegree. The existing one-sided identity suffices for the proved local
   correction; both identities are appropriate for the symmetric source target.
   Never include representatives or degeneration as assumed record fields.
2. Give the column filtration of `K.total` as a functor of cochain complexes:
   `F^p Tot^n = ⨁_{a+b=n, a≥p} K[a,b]`. Prove each inclusion is a cochain map,
   the filtration is decreasing, and boundedness makes it finite in each degree.
   The existing stupid truncation API may help restrict the horizontal complex;
   totalization maps and the filtration's direct-summand inclusions must be checked.
3. Apply `HomotopyCategory.spectralObjectMappingCone`, precompose with the
   increasing functor `i ↦ F^(-i)`, and map by the homological cohomology functor.
   Prove the mono-inclusion mapping cone computes the filtration quotient.
   This is a real categorical comparison, not an equality supplied as input.
4. Use `e1Data` with the genuine `SpectralObject.spectralSequence` constructor.
   Prove its `HasSpectralSequence` conditions and first-page computation.
   At page 1 the central interval is `F^(p+1) → F^p`; its quotient complex is
   the shifted vertical column. Prove the isomorphism with vertical cohomology,
   including the harmless column sign. Check differentials through the comparison.
5. Transfer the proved total-cocycle representatives to every actual page. One
   credible route is to prove that every page class is represented by a total
   cocycle, then use the spectral object's differential formula to prove
   `∀ r≥1, d_r=0`, inducting with the page homology isomorphisms. Prove the
   representative-surjectivity invariant; do not assume it. Another route is
   a filtered comparison from chosen biclosed representatives with zero
   differential, proved to induce an E1 isomorphism. Selection and filtered
   comparison require additional proofs even over a field.
6. Use boundedness to identify the stable page with the associated graded of
   total cohomology. State one-filtration degeneration precisely. If extending
   to DGMS (5.17)'s equivalence, prove both filtrations and their n-oppositeness:
   degeneration alone is not equivalent to the full `d′d″` lemma.
7. Complete the convention bridge from independently defined anticommuting
   double complexes to mathlib's commuting squares. Reuse the proved sign
   lemmas, prove the constructor's square laws, and prove its total differential
   is the original `d′+d″`. Do not claim this constructor already exists here.

For canonical mathlib E2 coordinates, the proved shear is
`(p,q,r) ↦ (2p+q+1,-p-1,r+1)`. Total degree is preserved and differential
degree matches. This explains the indexing choice but does not establish the
filtration/cone/quotient page comparison. Simply renaming an E2 object E1 is
not sufficient.

## Source, overlap, and significance

DGMS (Inventiones 29, 1975), §§5.15–5.17 gives the identities, cohomology
comparisons, and bounded double-complex degeneration/decomposition theorem.
The local proof formalizes its correction mechanism. Chen–Ho–Teh,
arXiv:1506.06451v2 supplies a direct algebraic degeneration argument; its
phrase "degenerates at E1" excludes already degenerating at E0, whereas the
planned statement "all d_r vanish for r≥1" should include that harmless case.
Stelzig, arXiv:1812.00865v3 supplies squares/zigzags as a longer alternative.
These are classical results. A reusable formal bridge from bicomplex
representatives to the genuine filtered spectral-sequence API could interest
researchers in Hodge theory and homological algebra. The current local lemma
alone has not been shown to satisfy Palomar's serious-research-note threshold.

The repository's inspected projects and 57 returned branch names were topology
work; no Hodge branch or PR was found in GitHub searches. The pinned mathlib
homology subtree was searched for Dolbeault, Bott–Chern, `ddbar`, `d'd''`, and
degeneration implementations; no corresponding theorem was found. This is a
scoped search, not a proof of universal non-overlap. Palomar's public recent
JSON was searched through the web reader: no "double complex" or "degeneration"
match; "Hodge" included an unrelated electromagnetic result. Direct cloud
download returned HTTP 403, so no complete machine-readable registry snapshot
was retained. Repeat a full current duplicate search before any intake.

ComputationalPathsLean at commit `257c659b7973aeda900d86a5da73b208712c7523`
is deliberately not imported or used as a semantic foundation. No computational
path contribution is claimed. Analytic compact-Kähler and noncommutative
Kaledin targets are outside this project.

## Palomar preparation plan

Read-only current policy observations are pinned in
`verification/policy-snapshot.json`: policy commit
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`, submission-tooling commit
`ad5db9e7ff8b17523d73aeb244aaeabcde810c64`. The observed minimum Lean version
is `v4.35.0-rc2`; this project's exact Lean version matches its mathlib pin.
These are planning observations, not an official preflight receipt. Recheck
all changing policy/toolchain/schema requirements before release.

After the full theorem is proved: freeze the precise scope; obtain independent
source-fidelity and research-interest review; assign explicitly authorized human
author/maintainer roles; provide v0.4 metadata with accurate AI disclosure,
classifications, citations, Apache-2.0 license, and limitations; create a small
independent Challenge and proved Solution, with no proof holes as required by
this user's constraint; configure selected theorem/definition names and allowed
imports; finish the material imported-definition inventory and compile its
bridges through both entrypoints. Run `scripts/check_imported_definitions.py`
in static and exact-dependency modes only when that structure exists.

Then obtain authorized exact-source protected Comparator and independent-kernel
checks, render/inspect the Challenge, independently review the exact release
packet and immutable evidence, and run `scripts/check_release_packet.py`.
No preflight, rendering, intake, registration, or editorial acceptance is
inferred from this pilot's local build. No credentials, security changes,
charges, new legal acceptance, or Palomar submission are authorized by this plan.
Any PR for this work must remain a draft. Existing topology sources and campaign
ledgers are untouched.
