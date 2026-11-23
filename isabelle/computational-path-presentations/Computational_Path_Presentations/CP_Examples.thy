section \<open>A declared diamond and executable examples\<close>

theory CP_Examples
  imports CP_Conservative_Extension CP_Tree_Congruence
begin

datatype cp_vertex = Top | Left | Right | Bottom

datatype cp_edge = To_Left | To_Right | Left_Down | Right_Down

fun cp_example_source :: "cp_edge \<Rightarrow> cp_vertex" where
  "cp_example_source To_Left = Top"
| "cp_example_source To_Right = Top"
| "cp_example_source Left_Down = Left"
| "cp_example_source Right_Down = Right"

fun cp_example_target :: "cp_edge \<Rightarrow> cp_vertex" where
  "cp_example_target To_Left = Left"
| "cp_example_target To_Right = Right"
| "cp_example_target Left_Down = Bottom"
| "cp_example_target Right_Down = Bottom"

definition cp_left_route :: "cp_edge word_g_i" where
  "cp_left_route = [(True,To_Left),(True,Left_Down)]"

definition cp_right_route :: "cp_edge word_g_i" where
  "cp_right_route = [(True,To_Right),(True,Right_Down)]"

definition cp_diamond_relations :: "(cp_vertex,cp_edge) cp_relations" where
  "cp_diamond_relations = {(Top,cp_left_route,cp_right_route,Bottom)}"

lemma cp_diamond_routes_typed:
  "cp_path cp_example_source cp_example_target Top cp_left_route Bottom"
  "cp_path cp_example_source cp_example_target Top cp_right_route Bottom"
  by (simp_all add: cp_left_route_def cp_right_route_def cp_source_def cp_target_def)

theorem cp_diamond_needs_equation:
  "\<not> cp_equiv cp_example_source cp_example_target {} Top cp_left_route cp_right_route Bottom"
  by (simp add: cp_empty_presentation cp_left_route_def cp_right_route_def canceling_def)

theorem cp_declared_diamond:
  "cp_equiv cp_example_source cp_example_target cp_diamond_relations
    Top cp_left_route cp_right_route Bottom"
  using cp_diamond_routes_typed
  by (auto intro: cp_equiv.named simp: cp_diamond_relations_def)

theorem cp_diamond_abbreviation_conservative:
  "cp_equiv (cp_ext_endpoint cp_example_source Top) (cp_ext_endpoint cp_example_target Bottom)
      (cp_extension cp_diamond_relations Top cp_left_route Bottom)
      x (cp_embed u) (cp_embed v) y \<longleftrightarrow>
    cp_equiv cp_example_source cp_example_target cp_diamond_relations x u v y"
  by (rule cp_conservative_abbreviation) (rule cp_diamond_routes_typed)

lemma cp_example_cancellation:
  "cp_reduce [(True,To_Left),(True,Left_Down),(False,Left_Down),(False,To_Left)] = []"
  by (simp add: canceling_def)

text \<open>The next computation tests the raw-word reducer. Its two letters are
not composable in the displayed graph; no endpoint-typing claim is made.\<close>

lemma cp_example_distinct_primitives:
  "cp_reduce [(True,To_Left),(False,To_Right)] = [(True,To_Left),(False,To_Right)]"
  by (simp add: canceling_def)

text \<open>The example is algebraic. The two routes are distinct in the free
presentation and become equal when the diamond equation is declared. A filled
geometric square would require a separate realization and a homotopy argument;
neither follows from the name of this graph.\<close>


text \<open>Flattening an identity erases its stored vertex. A malformed named
  tree equation must therefore be filtered before its words are admitted as
  a relation; checking only the flattened words would not suffice.\<close>

lemma cp_malformed_tree_relation_ignored:
  "cp_flat_relations (\<lambda>_::unit. False) (\<lambda>_. False)
    {(False, CP_Id True, CP_Gen (), False)} = {}"
  by (auto simp: cp_flat_relations_def elim: cp_typed.cases)

export_code cp_reduce in SML module_name Computational_Path_Normalizer

export_code cp_reduce checking SML

end
