# Representation crosswalk

This interprets the linked Lean model declarations from baseline commit
`e2a41fb46531b444d4a104ea9bc4d277e06d9dc3` against Isabelle source at
[`544f9084c00f4373581d230610e471fe445579e5`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/tree/544f9084c00f4373581d230610e471fe445579e5).
The accompanying `RepresentationBridge.lean` is added after that baseline.
This is not a cross-kernel theorem or a complete manuscript correspondence audit.

Lean regions are predicates, while the Isabelle theories use sets and
membership. Predicate equality and the fixed-point equalities rely on the
usual extensional reading; selected Lean proofs can use `propext`,
`Classical.choice`, and `Quot.sound`, as recorded by the separate axiom audit.
Function extensionality and Lean's proof irrelevance are part of the surrounding
logical interpretation. Source-file similarity alone does not translate proof
objects between the two systems.

Natural-number indices are interpreted as the standard zero/successor naturals
on each side. In the spine and copy graphs, Lean `n + 1` corresponds to
Isabelle `Suc n`; the local Lean lemma `index_successor` checks its Lean-side
identity. For finite prefixes, Lean natural order and addition are interpreted
as Isabelle's natural order and addition. This is an interpretation of the two
native types, not a formal isomorphism between kernels.

| Use | Isabelle source | Lean source | Correspondence and boundary |
| --- | --- | --- | --- |
| Labelled spine gate | [`gate_value`, `spine_solution`, `cofinal_forcing`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/source-sharing/Source_Sharing_Spines.thy#L7-L15) | [`SpineGate`, `SpineSolution`, `CofinalForcing`](https://github.com/Arthur742Ramos/Math-Formalization/blob/e2a41fb46531b444d4a104ea9bc4d277e06d9dc3/causal-efficacy/determination-patterns/DeterminationPatterns/LabelledSpine.lean#L7-L22) | Both choose OR when the gate bit is true and AND when false. Lean's third input is a proposition; represent a Boolean input `z` by `z = true`. The separately checked Lean truth table verifies the four gate/input-bit cases and the Boolean analogue of the Isabelle equation. It does not import Isabelle's definition into Lean. |
| Occurrence gate | [`occurrence_gate`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/source-sharing/Source_Sharing_Spines.thy#L166-L169) | [`OccurrenceParity`, `OccurrenceGate`](https://github.com/Arthur742Ramos/Math-Formalization/blob/e2a41fb46531b444d4a104ea9bc4d277e06d9dc3/causal-efficacy/determination-patterns/DeterminationPatterns/LabelledSpine.lean#L194-L200) | Isabelle chooses even prior-occurrence parity; Lean starts with `false` and toggles on prior occurrences. Under the informal cross-system interpretation they choose opposite witness bits, while both establish the existential synthesis property. No imported identity or gate-by-gate equality is claimed. |
| Labelled graph and state | [`labelled_node` and `labelled_dependency`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/source-sharing/Source_Sharing_Spines.thy#L221-L241), [`labelled_state`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/source-sharing/Source_Sharing_Spines.thy#L314-L317) | `LabelNode`, `LabelDependency`, `LabelState` in `LabelledSpine.lean` | Root/link constructors correspond, and each link has its labelled root and successor link as parents. The Lean gate selector `g` and root assignment `u` are Bool-valued; the link state `v` is Prop-valued. `LabelState` records `u` and `v`. Its fixed-state bridge is `label_state_fixed_iff`; the label type is inhabited by `l 0`. |
| Copy-majority graph | [`majority3`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/copy-majority/Copy_Majority_Representation.thy#L7-L8), [`copy_node` and `copy_dependency`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/copy-majority/Copy_Majority_Representation.thy#L63-L68), [`copy_state`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/copy-majority/Copy_Majority_Representation.thy#L133-L136) | [`Majority`, `CopyNode`, `CopyDependency`, `CopyState`](https://github.com/Arthur742Ramos/Math-Formalization/blob/e2a41fb46531b444d4a104ea9bc4d277e06d9dc3/causal-efficacy/determination-patterns/DeterminationPatterns/CopyMajority.lean) | Isabelle `MRoot`, `MCopy`, `MLink` correspond to Lean `.root`, `.copy`, `.link`; constructor disjointness is supplied independently by each datatype. Each link uses its root, copy and successor link. Lean's majority takes propositions, interpreted as Boolean truth in the Isabelle equation. |
| Projection and clamping | [`projection_solution`, `expanded_solution`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/copy-majority/Copy_Majority_Representation.thy#L16-L23), [`copies_clamped_solution`](https://github.com/Arthur742Ramos/causal-efficacy-isabelle/blob/544f9084c00f4373581d230610e471fe445579e5/copy-majority/Copy_Majority_Representation.thy#L291-L294) | `ProjectionSolution`, `ExpandedSolution`, `CopiesClampedSolution` in `CopyMajority.lean` | Predicates correspond to Boolean sequences by truth; paired copy/link sequences correspond to Isabelle `fst`/`snd` and Lean `Prod.fst`/`Prod.snd`. The negative example clamps every added copy on with roots off, using the explicit clamped-solution predicate; no general full-carrier clamping transport is proved. |

Classical choice in the forest construction selects witnesses satisfying an
existence property. The interpretation does not assert that Isabelle's
`SOME`/`LEAST` and Lean's `Classical.choose` choose identical representatives.
The carrier, graph orientation, context legality and edge relevance remain
separate hypotheses, as in the existing `CROSS-SYSTEM.md`; they must not be
inferred from this representation table.

The gate truth-table bridge is formalized in `RepresentationBridge.lean`;
its Boolean equation is a Lean analogue of the Isabelle equation, not an
imported Isabelle theorem. The retained core excerpts and per-configuration
imported-definition audit remain subject to final materiality and
source-to-compiled-artifact review.
