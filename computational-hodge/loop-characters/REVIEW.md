# Scope and fidelity review

The selected result is an actual period correspondence between finite geometric
harmonic cochains and algebraic real characters of the represented ambient loop
subgroup, with an explicitly proved nonzero circle witness.

Independent internal AI scope review preceded implementation. It rejected an
initial proposal to root every ambient point: finite primitive edges would
force a finite ambient space, invalidating intended geometric examples. The
implemented `Rooting` covers only computational endpoints plus the root. Paths
and homotopies remain in the ambient space; replacing them by paths in the
finite endpoint subspace would invalidate the circle example and is not done.

The actual `GeometricTrace` and fourteen `ScopedRwEq` constructors are literal
attributed upstream definitions. The proof does not substitute equality-indexed
raw paths or assume a geometric completeness certificate. `G` uses all actual
endpoint-fixed homotopies as rules. `representedGroup` is a subgroup of the
existing ambient `FundamentalGroup`, with actual computational representatives
and proved closure. `Characters` is explicitly equivalent to ordinary group
homomorphisms into the additive reals via `Multiplicative`; no continuity requirement
is imposed on this character space.

The scope reviewer independently checked the reversed fundamental-group
multiplication convention, endpoint activity propagation, handling of inactive
points, and the need for rooting all computational endpoints. Forward period
integration uses no rooting. Reconstruction uses rooted edge loops, and
zero-loop exactness constructs the actual potential. Finite Hodge projection
then proves the representative existence, uniqueness and independence of
connectors. These are actual proofs, not representation assumptions.

The circle witness uses current pinned Mathlib covering and lifting APIs.
Winding is the real endpoint of the actual lift starting at zero. Translation
of lifts and winding additivity are proved, including the reversed group
convention. The standard circle loop lifts to the standard real interval, so
winding one and nonzero harmonicity follow without assuming a nonzero
character. Generic covering/path-lifting and orthogonal projection theory are
credited, and the prior user's lifting strategy is acknowledged. No full circle
fundamental-group classification is claimed.

Independent authoring review reconstructed the complete eight-module surface
and authenticated the predecessor mappings, without finding a mathematical
or source-fidelity blocker. That review does not replace final exact-source
checks or final packet review. The imported-definition inventory and semantic
modules retain actual definitions, dependency expansions, immutable source
URLs and hashes; their completeness and selected-use interpretation require
independent review in addition to automated consistency checks.

This result is classical in inspiration. Its focused research audience is
computational-path semantics, discrete period/cohomology correspondences and
formalized geometric topology. No novelty, editorial acceptance or registration
is inferred from successful machine verification or internal AI review.

Exact-source native, protected interfaces and literal definition values,
negative controls, standard axiom closure, original canonical CLI, Lean and
independent kernels, unmodified rendering, browser inspection and release-packet
review are separately bound in immutable external evidence. Shared complete
Challenge/Solution source is disclosed; independent proof implementations and
human review are not invented. Later edits require affected checks again.

No ambient fundamental-group surjectivity, singular/de Rham comparison,
continuous-character result, higher cohomology, analytic/Kähler Hodge theorem,
numerical algorithm or completeness of geometric rewrites is claimed. The
project's authorship, maintenance and AI-contribution disclosures retain the
explicitly authorized roles. Existing intakes and provider repositories are
outside this development task.

The inherited harmonic projection keeps every retained declaration statement and
operator formula. Its two record-law tactic proofs are replaced by explicit
`congrArg` equality chains, `add_sub_add_comm` and `smul_sub`. This avoids a
module-dependent generated helper proof detected by the unchanged strict
comparator. The old failure is preserved; `base-provenance.json` records both
complete source adaptations. No comparison rule, proof contract or resource
limit is weakened.
