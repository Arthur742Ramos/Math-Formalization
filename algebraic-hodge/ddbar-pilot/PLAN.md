# Dependency blueprint and release gates

The concrete quotient construction avoids a large mapping-cone comparison
while preserving the actual filtered complex, quotient pages, induced
operators, page homology transitions, and bounded stable-page meaning.

## Mathematical dependency graph

1. `Integration`, `Representative`, `TotalRepresentative`: actual commuting
   bicomplex, explicit d′d″ preimage correction, actual vertical homology
   representatives, and soundness under inclusion into the signed total complex.
2. `FilteredPages`: decreasing subcomplex filtration, actual Zr/Br quotient
   pages, descended total differential, and its square-zero law. These definitions
   have no d′d″ input.
3. `ColumnFiltration`, `ColumnComponents`, `FiltrationComplex`: the genuine
   column filtration, summand projections/inclusions and differential formulas,
   and its subcomplex/functor realization.
4. `VerticalClass`, `LeadingCycle`, `BoundaryLeading`, `PureRepresentative`,
   `LeadingKernel`: the leading component of an r-cycle is a vertical cycle;
   the leading component of a total boundary is vertically exact under the
   incoming image/kernel identity; zero leading class puts a cycle in the
   actual page denominator; biclosed pure summands supply representatives.
5. `PageComparison`, `PageIsomorphism`: actual E1 is vertical cohomology
   without d′d″; all Er, r≥1, are vertical cohomology under incoming/outgoing
   identities. No conclusion is a record field.
6. `Degeneration`: every actual dr, r≥1, vanishes, since its leading class is
   a proved vertical boundary and the target page comparison is injective.
7. `AssociatedSequence`, `SequenceTransitions`: conventional mathlib spectral
   sequence with actual quotient pages, induced dr and homology recurrence.
   Recurrence agrees on common representatives, and its inverse zero-page
   homology comparison is tied to the actual homology projection.
8. `FilteredInfinity`, `InfinityComparison`: the stable quotient consists of
   total cocycles modulo higher-filtered cocycles and actual total boundaries;
   its leading-component comparison is an isomorphism under the identities.
9. `CohomologyClass`, `GradedCohomology`: generic canonical comparison of that
   stable quotient with the associated graded of actual cohomology, filtered
   by classes of filtered cocycles. No d′d″ assumption or boundedness is needed.
10. `BoundedFiltration`, `E1Degeneration`: actual rectangular support implies
    finite horizontal support. Fp=0 for p>U and Fp=Tot for p≤L. For
    U<p+r and p−r+1≤L, actual Zr and denominators equal stable submodules.
    Thus the all-r vanishing result has the usual bounded E1=E∞=gr H meaning.

The local all-r vanishing and page comparisons require neither boundedness nor
finite dimensionality. This stronger statement is not used to infer convergence
for arbitrary unbounded filtrations; convergence here is proved from finite
horizontal support. The formal rectangular theorem allows any four integer
bounds; empty support causes no defect.

## Source, overlap, and research scope

DGMS (Inventiones 29, 1975) §§5.15–5.17 supplies the classical source.
The project proves one componentwise direction of its explicit identities
implies degeneration of one filtration. DGMS §5.17's equivalence includes both
filtrations and n-oppositeness. Degeneration of one filtration alone must not
be represented as the full d′d″ equivalence.

Chen–Ho–Teh, arXiv:1506.06451v2, supplies a direct algebraic degeneration
argument. Its theorem has an extra non-E0-degeneration assumption; its
definition permits earlier degeneration. The formal proof here handles all
cases directly and does not import that theorem while omitting its hypothesis.
Stelzig, arXiv:1812.00865v3, gives squares/zigzags as another architecture.
A reusable verified bridge between explicit corrections, quotient pages and
actual total cohomology has an audience in algebraic Hodge theory and
homological algebra. No new mathematics or editorial acceptance is asserted.

The initial repository/branch/PR survey found no duplicate Hodge campaign;
PR40 is now the single existing draft. The scoped pinned mathlib search found
no corresponding Dolbeault/Bott–Chern/d′d″ degeneration theorem. This does not
establish universal non-overlap. The public registry web survey found no
matching double-complex degeneration result; direct recent.json download
returned HTTP 403, so no complete machine-readable snapshot was retained.
Repeat current duplicates and prior-art checks before intake.

ComputationalPathsLean commit 257c659b7973aeda900d86a5da73b208712c7523 is not a
semantic dependency. No computational-path contribution is claimed. Analytic
compact-Kähler, noncommutative Kaledin, and other paper/topology campaigns are
outside this work.

## Remaining mathematical extensions

- Construct a bicomplex from independently specified anticommuting data and
  prove its totalization agrees with the original sum differential. Current
  operator sign lemmas are explicitly narrower.
- Compare the concrete quotient sequence with the abstract mapping-cone
  spectral-object sequence if that API interoperability is useful. Current
  pages and transitions already use the actual filtered complex and conventional
  cohomological indexing; no `HasSpectralSequence` instance is asserted.
- The second filtration, opposite filtrations, and the converse in DGMS §5.17
  are separate prospective extensions, not assumed or claimed here.

## Palomar preparation

Historical read-only policy observations are retained in
`verification/policy-snapshot.json`: policy commit
28bd48b9b71bbb2a82c718ce761d5a4220ef8e60 and submission tooling
ad5db9e7ff8b17523d73aeb244aaeabcde810c64. The observed minimum was Lean
v4.35.0-rc2, matching this project's pins. Recheck current policy, schema,
file/packaging limits and supported toolchains before any release; these
observations are not an official preflight.

Before verified intake, freeze the exact source scope and obtain independent
research-interest/source-fidelity review. Preserve the explicitly assigned
human roles and accurate metadata/AI disclosure. The proof-complete
Challenge/Solution, selected surface and schema-2 material inventory now exist;
both entrypoint bridges compile, and static/exact-dependency validators run.
The original preliminary inventories remain historical evidence. Local source
closure checks do not replace the canonical frozen-dependency audit, and
consistency checks do not certify semantic completeness.

Then obtain authorized protected Comparator and independent-kernel checks,
render/inspect Challenge, review the exact immutable release packet and run
`scripts/check_release_packet.py` with its exact-source full report. Current
local Lean/axiom checks satisfy none of those external release gates by
implication. No Palomar submission, credentials, security changes, charges or
new legal acceptance occur here. PR40 remains a draft.

## Current package milestone

The selected surface now consists of eight theorems and seventeen literal
definitions/constructions in comparator.json. HodgeChallenge has complete
proofs, 995 lines, and only Mathlib imports; HodgeSolution has the same generated proof-complete body and compiles separately; the modular development remains its source. This shares one proof implementation. A source map and reproducible generator retain 135 declarations
without changing mathematical commands/contracts. The hard size cap is met,
but the readability warning remains an editorial consideration.

ReleaseFidelity proves recurrence coverage of every next-page class, explicit
finite/exhaustive/separated induced cohomology filtration, canonical bounded
representative compatibility and equality of stabilization/degeneration maps
to graded cohomology. The source reviewer and primary contributor review each
other's contributions; no independent-kernel or human review is inferred.

Human author and responsible-maintainer roles were explicitly assigned for
this package to Arthur Freitas Ramos, Ruy Jose Guerra Barretto de Queiroz and
David Barros Hulak. Metadata preserves the separate AI contribution account.
No new credentials or terms acceptance were needed.

The material inventory retains 47 definitions/structures/classes, 30 exact-pin
source files and 63 excerpts. Its documented core/order/algebra/category
expansion boundaries are reviewed explicitly. Both entrypoint bridge modules
compile. The shared validator's apostrophe-final identifier bug was corrected
with regression coverage; no other project's mathematics or pins changed.

RUN-PLAN.md is the exact execution boundary: the current cloud cannot set up
bubblewrap user namespaces. The inert caller template is outside active
workflow directories. One predictive full preflight requires specific approval
of the immutable source, pinned pipeline, disposable zero-cost hosted runner,
runner-local setup and 19,800-second budget, with storage/cache costs independently
confirmed as zero before execution. Protected controls, external
kernels and later rendering are not represented as completed.
