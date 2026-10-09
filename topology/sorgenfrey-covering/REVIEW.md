# Statement and dependency review

The following checks were made separately from writing the proofs.

1. The space is Mathlib's `Counterexample.SorgenfreyLine`, with its generated
   lower-limit topology. No alternate definition of Lindelöfness or
   paracompactness is introduced.
2. `isLindelof_set` quantifies over every set A, without closedness, countability,
   openness, or any additional topological assumption. Mathlib's
   `isLindelof_iff_lindelofSpace` identifies this with Lindelöfness of the induced
   subspace.
3. `clopen_refinement` accepts any indexed open cover of the whole subspace.
   Its output proves countability of the index type, clopenness of every member,
   coverage, pairwise disjointness, local finiteness, and containment of each
   refined member in an original cover member. It does not merely produce a
   countable subcover or a point-finite family.
4. The nonempty branch obtains all basis intervals from open cover members in
   the actual induced topology. The empty branch uses an empty index type, so
   it remains valid when both the subspace and original cover index type are
   empty.
5. The disjointification proof uses the least index covering each point.
   Removing only finitely many earlier clopen sets preserves clopenness. A
   partition member containing the point meets no other member, establishing
   the required neighborhood form of local finiteness.
6. Subspace paracompactness is an instance of Mathlib's `ParacompactSpace` class.
   Whole-line paracompactness is transferred across Mathlib's homeomorphism
   from the universal subspace. No general regular-Lindelöf paracompactness
   theorem is assumed.
7. The negative plane results have no assumptions about a topology instance
   selected by the caller. The Lindelöf contradiction uses the closed discrete
   antidiagonal and its continuum cardinality. The paracompactness contradiction
   uses the plane's Hausdorff property and Mathlib's existing non-normality.

`AxiomAudit.lean` checks the transitive axiom dependencies of all twelve
declarations and verifies concrete space instances. The executable audit checker
rejects any dependency beyond `propext`, `Classical.choice`, and `Quot.sound`.
The hosted workflow rebuilds the sources at its recorded exact Git commit.
The bundled `leanchecker` also rechecks the compiled project modules after
elaboration; the local check completed with exit code 0.

This is an internal statement review and machine verification record; it is not
an external mathematical referee report or a claim of historical priority.

The Lean 4.35.0-rc2 port retains these statements and arguments. Three explicit
theorem certificates expose the existing typeclass results to Palomar's
theorem comparator. There are seven configured theorem targets and no
definition holes. The Challenge compiles complete proof-bearing declarations
against canonical Mathlib independently of the candidate Lake plan; it
duplicates the Solution source. Separate proposition specifications preserve
the earlier independent statement check. Source and metadata scans by the
pinned Palomar pipeline accept the port; hosted mechanical results are recorded
separately and must be distinguished from ordinary Lean checks.
