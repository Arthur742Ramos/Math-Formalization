# Frozen generation inputs

`kernel.json` and `witnesses.json` are the frozen rational construction data.
`input-provenance.json` identifies their exact bytes and the original handoff
archive, together with the two small retained generation inputs below.

`cover-proposal.json` supplies the seventeen intervals, their endpoints and mode names.
Its original coefficients and approximate `minimum_endpoint` are untrusted
proposal history. `assess_frontier_integrals.py` recomputes the coefficients
from the generated integral totals, actual normalization and kernel data.
`cover-template.txt` supplies the Lean text layout for the finite cover.
`assembly-template.txt` retains the generic outer-argument text used by the
bound generator; its numerical assumptions are replaced by actual leaf-tree
certificates in the generated source. These input files are not numerical
oracles or premises of the completed Lean proof.

The committed Lean sources suffice for verification. To regenerate proposals
in a separate checkout, Python 3.12's standard library is sufficient. Run:

```sh
python3 scripts/generate_frontier_kernel.py
python3 scripts/generate_frontier_witnesses.py
python3 scripts/generate_frontier_grid.py
python3 scripts/generate_frontier_trig_identities.py
python3 scripts/generate_frontier_normalization.py
python3 scripts/generate_frontier_affine.py
python3 scripts/generate_frontier_interfaces.py
python3 scripts/generate_frontier_integrals.py --output "$EVIDENCE_DIR/integrals.json.gz"
python3 scripts/assess_frontier_integrals.py --packet "$EVIDENCE_DIR/integrals.json.gz" --output "$EVIDENCE_DIR/assessment.json"
python3 scripts/emit_frontier_integrals.py --packet "$EVIDENCE_DIR/integrals.json.gz"
python3 scripts/generate_frontier_bound.py --assessment "$EVIDENCE_DIR/assessment.json"
```

Use an external owned `EVIDENCE_DIR`. The two derived JSON tables are ignored
because the grid and affine generators recreate them. The default integral
tolerances are `2e-12` for profiles and `2e-13` for the denominator.
The emitter combines up to 512 ordered leaves and their checked block theorem
in each module, then glues the blocks in balanced trees. This layout retains
every leaf and geometric check.
Floating estimates guide subdivisions and grid proposals; exact Lean checks establish
the accepted arithmetic. Platform differences can change a generated proposal.
Review any source diff and rebuild all affected modules before using it.
