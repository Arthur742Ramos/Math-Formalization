section \<open>Computational Path Presentations\<close>

theory CP_Introduction
  imports Main
begin

text \<open>This entry formalizes the algebraic, endpoint-typed core of
computational-path presentations. Finite binary witnesses are flattened to
composable signed words and reified as typed canonical trees. Given executable equality on generator labels, a cancellation algorithm
computes the free normal form and refines the normal form in Breitner's AFP entry
Free Groups \<^cite>\<open>Breitner2010FreeGroups\<close>. Its soundness and completeness are
for the free structural word congruence, defined independently by cancellation
steps, symmetry and transitivity.

Typed equations can then be declared between parallel words. Interpretation
by finite words preserves these equations under explicit typing and
relation-preservation hypotheses. Adjoining a fresh primitive together with
an equation defining it as an existing word is conservative on the old
presentation: eliminating that primitive reflects equality between old words.
The original equation set may be arbitrary; this does not assert a decision
procedure for equality in an arbitrary presentation.

The motivating literature treats equality witnesses as explicit computational
paths \<^cite>\<open>Ramos2017Identity\<close> and \<^cite>\<open>deVeras2021Topological\<close>. The
presentation-change viewpoint and the distinction between literal signed
words and binary syntax follow the algebraic setup of
\<^cite>\<open>Ramos2026Presentation\<close>. The present scope is deliberately narrower
than its topological results: no quotient topology, realization homeomorphism,
geometric completeness or equality of binary and equal-slot parametrizations
is claimed. The cancellation relation is not the full LND equality rewrite
calculus. Executable endpoint checking additionally requires executable
equality on the vertex type. The abstract HOL correctness statements are
independent of these code-execution requirements.

The earlier dependent-HIT development already has typed walks and presented
path quotients. This entry uses the existing AFP free-group cancellation core
and adds an executable refinement and the explicit conservative-abbreviation
package. It has no import-based connection to an intensional identity type.
A future HoTT interpretation must prove its endpoint and equation contracts
explicitly. Tree normalization here is complete for the word congruence after
flattening, not a claimed independent presentation of every binary-tree
rewrite rule.\<close>

end
