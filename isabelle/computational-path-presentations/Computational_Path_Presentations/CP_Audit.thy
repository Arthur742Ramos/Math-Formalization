section \<open>Proof-dependency audit\<close>

theory CP_Audit
  imports CP_Examples CP_Presentation_Equivalence CP_Torus_Presentation
begin

text \<open>The following read-only ML check rejects any recorded proof oracle in
the transitive dependencies of the selected headline results. It does not
construct proofs or introduce axioms. Standard Isabelle/HOL foundations,
including choice in the imported specification of normalization, remain in
use. This oracle check is not a separate audit of all logical axioms.\<close>

ML \<open>
  val computational_path_headlines =
    [@{thm cp_reduce_eq_normalize},
     @{thm cp_reduce_sound},
     @{thm cp_reduce_complete},
     @{thm cp_typed_tree_word_correspondence},
     @{thm cp_normal_tree_complete},
     @{thm cp_typed_reduction_diamond},
     @{thm cp_interpretation_sound},
     @{thm cp_primitive_codes_agree},
     @{thm cp_empty_presentation},
     @{thm cp_conservative_abbreviation},
     @{thm cp_abbreviation_roundtrip},
     @{thm cp_diamond_needs_equation},
     @{thm cp_declared_diamond},
     @{thm cp_tree_eq_sound},
     @{thm cp_tree_eq_quote_flat},
     @{thm cp_tree_eq_normalize},
     @{thm cp_tree_eq_complete},
     @{thm cp_tree_eq_decide},
     @{thm cp_tree_presented_sound},
     @{thm cp_tree_presented_complete},
     @{thm cp_tree_presented_empty},
     @{thm cp_relation_replacement_iff},
     @{thm cp_redundant_relations_iff},
     @{thm cp_tietze_relation_move},
     @{thm cp_word_code_compose},
     @{thm cp_presentation_map_compose},
     @{thm cp_presentation_map_reflects},
     @{thm cp_reversible_presentations.source_equivalence},
     @{thm cp_reversible_presentations.target_complete_invariant},
     @{thm cp_abbreviation_equivalence},
     @{thm cp_abbreviation_free_normal_form},
     @{thm cp_torus_exponent_invariant},
     @{thm cp_torus_equiv_iff_exponents},
     @{thm cp_torus_normalize_sound},
     @{thm cp_torus_canonical_unique},
     @{thm cp_torus_normalize_complete},
     @{thm cp_torus_decide_correct},
     @{thm cp_torus_tree_equiv_iff_exponents},
     @{thm cp_torus_tree_normalize_sound},
     @{thm cp_torus_tree_normalize_complete},
     @{thm cp_torus_tree_decide_correct}];
  val _ = if null (Thm_Deps.all_oracles computational_path_headlines) then ()
    else error "Unexpected oracle dependency in computational path results";
\<close>

end
