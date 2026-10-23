# Internal mathematical and semantic review

This is internal AI review, not human mathematical review, external peer
review, or Palomar editorial review. It supports a pilot, not intake readiness.

The primary agent implemented Integration, Representative, SignBridge,
TotalRepresentative, and AxiomAudit. A separate reviewer agent independently
checked those files, inspected the pinned mathlib definitions and the cited
mathematical sources, and separately ran
`lake env lean -DwarningAsError=true FILE` on each of the six Lean modules.
Every command exited 0 and the source hashes remained unchanged. The reviewer
authored Indexing; its formulas and proof contracts were independently checked
by the primary agent, rather than treating the author's self-review as
independent review. Both agents use the same Lean kernel and dependency cache;
these are not independent-kernel checks.

Reviewed source hashes:

| File | SHA256 |
| --- | --- |
| Integration.lean | `e8f61e07208d27985a7d6e4cfdd229bc50b9e07ff0fd37a6c7ca2c58696a0d79` |
| Representative.lean | `0d891530dfc123651194116596ef3110e5bb4cc3a57068450461c2ec1c6580a8` |
| SignBridge.lean | `5cf99fcababd32c73451857307c2fa800255f0f2b5131c82bfebb4139d85ac0a` |
| TotalRepresentative.lean | `d3cc3162bace9746351e3d003fdeda84aa825a61b1df4e64fe5d406a951e1a47` |
| Indexing.lean | `2a21798599e549bf16c27cd53e86215313c26185ae11e643ecee22eff0cba70c` |
| AxiomAudit.lean | `aa7debef8e17c0e86bdf488c934858f24365b7da06822c93defb5653ee5ab05c` |

The reviewer found the representative hypothesis is an explicit submodule
identity on actual differentials. The proof chooses a genuine preimage of
`h x`, corrects by `v b`, and proves both closure equations. The homology
statement uses `homologyIsoSc'` and `moduleCatHomologyIso`; equality of
classes follows from the actual boundary witness `-b`. Neither the conclusion
nor a dimension equality is supplied as an assumption. Boundedness is absent
because the local proof does not use it; this is an honest stronger local
statement, not a proof of the bounded global target.

The sign lemmas concern actual linear maps and prove anticommutation,
square-zero, involution, and kernel/range preservation in every characteristic.
They do not reconstruct arbitrary external anticommuting double complexes.
The total representative is mapped by `K.ιTotal` and its closure is proved
with mathlib's total differential. This is soundness into a genuine complex.
No filtered page or degeneration result is asserted.

The primary agent's independent indexing review checked total degree and
each interval equation. Under the differential shift `(p,q) ↦ (p+r,q+1-r)`,
the equations `i₀(r,p,q)=i₂(p+r,q+1-r)` and
`i₁(p,q)=i₃(r,p+r,q+1-r)` hold. The adjacent-page equations and the bounds
require `r≥1` and are proved in Lean. At `r=1` the outer intervals are
identities. The shear `(2p+q+1,-p-1,r+1)` preserves total degree and maps the
differential degree correctly. These checks establish indexing data only;
the filtration/quotient/first-page association is still missing.

Source fidelity: the local representative proof is one componentwise
direction of DGMS §5.15(b), consistent with §5.16. The full §5.17 equivalence
also involves opposite filtrations, so degeneration alone must not be stated
as its equivalent. Chen–Ho–Teh and Stelzig substantiate the broader classical
target and its audience in algebraic Hodge theory and homological algebra.
No mathematical novelty is claimed. The current local result alone has not
been established to meet Palomar's research-interest threshold.

The audit enumerates 20 declarations and reports only `propext`,
`Classical.choice`, and `Quot.sound`; `canonicalCoordinates` needs no axioms.
Text inspection found no proof holes, custom axiom declarations, `unsafe`,
`implemented_by`, or `native_decide` in the six reviewed modules.

Review limits: scoped overlap search, no full global prior-art audit, no
Challenge/Solution comparison, no external-kernel verification, no rendered
Challenge, and no release-packet review. The material imported-definition
inventory is preliminary; its completeness and future entrypoint bridges must
be independently re-reviewed before release. Documentation was checked
against the listed declarations and the explicit unproved milestones.
