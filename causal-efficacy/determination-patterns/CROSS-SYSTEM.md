# Isabelle/HOL and Lean semantic interpretation

This is an explicit mathematical interpretation, supported by Lean theorems and
source inspection. It does not claim that either kernel has checked the other
system's proof. The source snapshot is Isabelle2025-2; the inspected installed
`src/HOL/Inductive.thy` has SHA-256
`5ddc62bb2560de070ddf2b7f5112ec911b5006610285edd43199bdd72a1c1fc5` and
defines `lfp f = Inf {u. f u ≤ u}` and `gfp f = Sup {u. u ≤ f u}`.

1. Interpret an Isabelle HOL vertex type as an inhabited Lean type α; HOL types
   are inhabited. The general model theorems permit an empty Lean vertex type. A labelled
   spine parameter `l : Nat → α` itself implies that α is inhabited, so that
   theorem has no empty-label-type instance. The carrier may be empty in
   either system; no nonempty-carrier assumption is introduced.
2. Interpret an Isabelle set as a Boolean characteristic function and then as
   a Lean predicate. `propRegion` and `boolRegion` form inverse maps by
   `prop_bool_region` and `bool_prop_region`; `propRelation` / `boolRelation`
   and `toBooleanMechanism` / `fromBooleanMechanism` provide the corresponding
   inverses for binary relations and mechanisms on every set input. The inverse
   uses classical choice/decidability and propositional/function extensionality.
3. `BooleanTransport.lean` independently defines Boolean parents, admissible
   mechanisms, edge relevance, roots and contextual steps. Its bridge theorems
   prove equivalence with the Prop-valued Lean definitions, including full
   input-set quantification, root legality, set insertion and possible local
   influence. `BooleanPartition` and legal-context bridges make these
   assumptions explicit. This is an in-Lean transport, not a formal import of
   Isabelle definitions.
4. On a powerset, infimum is intersection and supremum is union. Lean `Least`
   is membership in every pre-fixed set, and `Greatest` membership in some
   post-fixed set. `boolean_least_bridge`, `boolean_greatest_bridge` and the
   contextual-operator bridge preserve these quantifiers over all sets. For
   monotone operators Lean proves each is fixed and extremal, matching the
   source's Knaster–Tarski use. The Boolean pattern corollary has Boolean
   existence/legality/partition assumptions and uses transported Prop path
   conditions; it is not a separately imported Isabelle theorem.
5. `FiniteClosure` is finite reflexive-transitive closure of the carrier-
   restricted predecessor relation, in the source direction. The `InternalPath`
   and `internal_reach_source_form` bridge retains the endpoint carrier guard,
   including the zero-step case. `SourceSemantics.lean` proves the first-member
   and local-foundation equivalences, equivalence of carrier accessibility to
   well-foundedness of the restricted relation, and `RootLength` to finite
   edge powers. Isabelle's source lemma
   `well_founded_on_iff_accessible_members` supplies the source-side bridge.
6. The source Isabelle `LEAST`/`SOME` forest and the Lean chosen forest each
   choose a smaller-ranked parent when one exists; they need not pick the same
   parent or agree outside the carrier. Both prove the stated existential
   all-context theorem. Likewise Lean's alternating occurrence gate uses the
   opposite starting parity from Isabelle's gate; no witness equality is
   asserted. Every legal labelled-root context is represented, including roots
   whose labels never occur.

`LocalInputs.lean` separately treats manuscript rules on the literal subtype
of parent subsets. It proves total extension preserves admissibility, relevance
and the contextual operator; restriction of an admissible total rule gives a
paper rule preserving relevance and the contextual operator. Off-domain and
root entries need not agree, so this is not a bijection of total functions.
`TargetScope.lean` formalizes the manuscript’s ancestor-cone and single-parent
claims, and `PaperResults.lean` gives its active-determined equality and direct
contextual source consequences.

The principal numbered statements were independently compared against extracted manuscript version 6 text; independent byte hashing of the private manuscript matched the recorded digest. A
fresh independent review of the complete final patch, exact source, proof and
release evidence remains needed. This account does not establish novelty,
metaphysical adequacy, human review or external acceptance.
