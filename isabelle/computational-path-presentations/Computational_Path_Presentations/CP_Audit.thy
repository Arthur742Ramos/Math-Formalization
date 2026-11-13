section \<open>Proof-dependency audit\<close>

theory CP_Audit
  imports CP_Examples
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
     @{thm cp_declared_diamond}];
  val _ = if null (Thm_Deps.all_oracles computational_path_headlines) then ()
    else error "Unexpected oracle dependency in computational path results";
\<close>

end
