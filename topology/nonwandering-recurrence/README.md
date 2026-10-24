# Nonwandering systems and generic recurrent points

For a continuous self-map of a Baire metric space, nonwandering is equivalent
to density of its actual recurrent-point set. That set is G-delta for every
continuous metric self-map, with no nonwandering or Baire premise. Under
nonwandering it is residual without Baire; density is the Baire-dependent step.

Nonwandering means each nonempty open set U contains a point whose positive
iterate returns to U. Recurrent means arbitrarily late natural returns to
every open neighborhood of the point. The proof first constructs late open
self-returns by shrinking U to U intersect an iterated preimage. Countable
positive metric scales then describe the exact recurrent set. Small balls
turn late open returns into dense open displacement stages, and countable
intersection/Baire category complete the result. No density premise is hidden
in the forward direction. Return times are strictly greater than their bound;
time zero is never used as a recurrence witness. Periodic points are included.

Hochman, Notes on Topological Dynamics (June15 2022), Definition1.18 and
Exercise1.5.9 with its small-ball hint were directly inspected. The compact
metric source context is generalized explicitly to Baire metric spaces.
Linero Bas and Soler Lopez, A Note on Recurrent Points (2015), Proposition1
and its proof were directly read for the neighborhood-intersection method.
No extra pointwise positive-return, sequential or omega-limit equivalence
from that paper is claimed. No measure-theoretic recurrence is used.

There is no global Nonempty X premise or existence claim: density in an empty
space is vacuous. Compactness, second countability, perfection, invertibility,
surjectivity and uniform recurrence are not assumed or concluded.

RecurrenceChallenge contains the complete standalone proof from Mathlib imports.
RecurrenceSolution imports the separate BirkhoffRecurrence source. The six
selected CategoryRecurrence names are nonwandering_iff_late_returns,
recurrent_iff_return_stages, isGdelta_recurrent, dense_return_stage,
residual_recurrent and nonwandering_iff_dense_recurrent. Fixed Nonwandering,
Recurrent, radius and ReturnStage have zero holes. Both semantic entrypoints
check literal definitions, positive times and identity-map recurrence.

Only propext, Quot.sound and Classical.choice are permitted; no holes or added
axioms. Exact-source release readiness is established by immutable external
local native, canonical, rendering, visual and independent-review receipts;
a build alone is not full certification. No intake or registration is claimed.

Campaign authors and responsible maintainers: Arthur Freitas Ramos;
David Barros Hulak; Ruy Jose Guerra Barretto de Queiroz. Codex formalization
and separate internal AI reviews disclosed; no human proof contribution or
external peer review inferred. Prior strongly-transitive packaging patterns,
Mathlib source and exact Lean core provenance are credited explicitly.

Run lake build and the package/material/core-definition audit scripts.
All necessary validation runs locally under root AGENTS.md; no author CI.
