# Scope and source audit

Sakai's second-edition author manuscript, dated November 2, 2023, states in
Proposition 2.4.5(1), pp.50–51, that the perfect image of a metrizable space is
metrizable. The statement explicitly describes the map as surjective. The
definition of perfect on p.33 is closed with compact fibers; continuity is
explicit in this formalization. The source treats Hausdorff spaces. Here the
existing registered perfect-map theorem derives codomain Hausdorffness from
the metrizable domain, so no codomain separation instance is assumed.

The new proof is the uniform two-radius estimate for metric neighborhoods of
compact fibers, followed by a sigma locally finite basis construction. The
existing registered image paracompactness and full Nagata–Smirnov proofs remain
credited prerequisites. The source uses the Alexandroff–Urysohn criterion at
the last step; the formal proof uses those prerequisites instead.

All finite unions of a locally finite basis layer need not form a locally
finite family. The proof makes no such inference. It obtains target layers
from paracompact open refinements, then proves the basis condition through
the uniform shrinking estimate. Each layer may have arbitrary cardinality.

The domain and codomain universes are independent. Surjectivity supplies points
of fibers only where needed; empty types are allowed. There is no hidden
second-countability, separability, compact-domain, locally compact, complete,
finite-fiber or bounded-fiber-size premise. The compatible metric conclusion
uses the exact original codomain topology.

The pinned Mathlib revision is `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Independent scans also checked current Mathlib master beginning `f0b4c815`,
including all 9,227 Lean files and 703 topology files, and all ten existing
repository projects. Complete public general-topology results and eight
related registry searches were checked at revision 276. No equivalent
perfect-image metrizability theorem was found. Embedding transfer, Urysohn's
second-countable criterion and the registered perfect-paracompact theorem have
different conclusions or hypotheses. This is an evidence-backed overlap
assessment with no worldwide priority claim.

The classical result supports metrizable quotients and upper semicontinuous
compact decompositions; Sakai immediately uses it for locally finite closed
gluing in Proposition 2.4.5(2). That corollary is not selected here. This audience
and application motivate the target; acceptance or a notability score is not
guaranteed.

Current policy and pipeline were checked at commits beginning `96b034c` and
`d4e41c1`, respectively. Lean v4.35.0-rc2 remains a supported minimum and matches
the pinned Mathlib toolchain exactly. Hosted checks are bound to the final
public source commit and protected Comparator configuration; their receipts
are recorded separately from local compilation and internal AI review.
