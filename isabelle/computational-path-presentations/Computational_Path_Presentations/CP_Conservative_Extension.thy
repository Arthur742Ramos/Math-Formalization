section \<open>Conservative introduction of a named abbreviation\<close>

theory CP_Conservative_Extension
  imports CP_Presentations
begin

definition cp_embed :: "'g word_g_i \<Rightarrow> 'g option word_g_i" where
  "cp_embed w = map (map_prod id Some) w"

fun cp_ext_endpoint :: "('g \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'g option \<Rightarrow> 'v" where
  "cp_ext_endpoint e a None = a"
| "cp_ext_endpoint e a (Some g) = e g"

fun cp_eliminate_generator :: "'g word_g_i \<Rightarrow> 'g option \<Rightarrow> 'g word_g_i" where
  "cp_eliminate_generator r None = r"
| "cp_eliminate_generator r (Some g) = [(True,g)]"

abbreviation cp_eliminate :: "'g word_g_i \<Rightarrow> 'g option word_g_i \<Rightarrow> 'g word_g_i" where
  "cp_eliminate r w \<equiv> cp_word_code (cp_eliminate_generator r) w"

definition cp_extension :: "('v,'g) cp_relations \<Rightarrow> 'v \<Rightarrow> 'g word_g_i \<Rightarrow> 'v \<Rightarrow>
    ('v,'g option) cp_relations" where
  "cp_extension R a r b = {(x, cp_embed u, cp_embed v, y) |x u v y. (x,u,v,y) \<in> R}
    \<union> {(a, [(True,None)], cp_embed r, b)}"

lemma cp_embed_Nil [simp]: "cp_embed [] = []"
  by (simp add: cp_embed_def)

lemma cp_embed_Cons [simp]: "cp_embed ((d,g)#w) = (d,Some g)#cp_embed w"
  by (simp add: cp_embed_def)

lemma cp_embed_append [simp]: "cp_embed (u@v) = cp_embed u @ cp_embed v"
  by (simp add: cp_embed_def)

lemma cp_embed_code:
  "cp_word_code (\<lambda>g. [(True,Some g)]) w = cp_embed w"
  by (induction w) (auto simp: cp_code_letter_def inv_fg_def inv1_def cp_embed_def split: prod.splits)

lemma cp_eliminate_embed [simp]: "cp_eliminate r (cp_embed w) = w"
  by (induction w) (auto simp: cp_code_letter_def inv_fg_def inv1_def cp_embed_def split: prod.splits)

lemma cp_path_embed [simp]:
  "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x (cp_embed w) y
    \<longleftrightarrow> cp_path s t x w y"
  by (induction w arbitrary: x)
    (auto simp: cp_embed_def cp_source_def cp_target_def split: prod.splits)

lemma cp_embed_equiv:
  assumes "cp_equiv s t R x u v y"
  shows "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b)
    x (cp_embed u) (cp_embed v) y"
proof -
  have "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b)
      (id x) (cp_word_code (\<lambda>g. [(True,Some g)]) u)
      (cp_word_code (\<lambda>g. [(True,Some g)]) v) (id y)"
  proof (rule cp_interpretation_sound[OF assms])
    show "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b)
      (id (s g)) (cp_word_code (\<lambda>g. [(True,Some g)]) [(True,g)]) (id (t g))" for g
      by (simp add: cp_embed_code cp_source_def cp_target_def)
  next
    fix x u v y
    assume rel: "(x,u,v,y) \<in> R" and u: "cp_path s t x u y" and v: "cp_path s t x v y"
    show "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b)
      (id x) (cp_word_code (\<lambda>g. [(True,Some g)]) u)
      (cp_word_code (\<lambda>g. [(True,Some g)]) v) (id y)"
      using rel u v by (auto simp: cp_embed_code cp_extension_def intro!: cp_equiv.named)
  qed
  then show ?thesis by (simp add: cp_embed_code)
qed

lemma cp_eliminate_typed:
  assumes r: "cp_path s t a r b"
    and w: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x w y"
  shows "cp_path s t x (cp_eliminate r w) y"
proof -
  have codes: "cp_path s t (id (cp_ext_endpoint s a g))
      (cp_word_code (cp_eliminate_generator r) [(True,g)]) (id (cp_ext_endpoint t b g))" for g
    using r by (cases g) (simp_all add: cp_code_letter_def cp_source_def cp_target_def)
  from cp_path_code[OF codes w] show ?thesis by simp
qed

lemma cp_eliminate_equiv:
  assumes r: "cp_path s t a r b"
    and eq: "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b) x u v y"
  shows "cp_equiv s t R x (cp_eliminate r u) (cp_eliminate r v) y"
proof -
  have "cp_equiv s t R (id x) (cp_eliminate r u) (cp_eliminate r v) (id y)"
  proof (rule cp_interpretation_sound[OF eq])
    show "cp_path s t (id (cp_ext_endpoint s a g))
      (cp_eliminate r [(True,g)]) (id (cp_ext_endpoint t b g))" for g
      using r by (cases g) (simp_all add: cp_code_letter_def cp_source_def cp_target_def)
  next
    fix x u v y
    assume rel: "(x,u,v,y) \<in> cp_extension R a r b"
      and u: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x u y"
      and v: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x v y"
    show "cp_equiv s t R (id x) (cp_eliminate r u) (cp_eliminate r v) (id y)"
      using rel u v r
      by (auto simp: cp_extension_def cp_code_letter_def
        intro: cp_equiv.named cp_equiv_refl)
  qed
  then show ?thesis by simp
qed

text \<open>The new symbol is not merely added to an alphabet: it is accompanied by
its defining equation. Elimination proves that this equation cannot create a
new equality between old typed words, even in the presence of arbitrary old
named equations. No termination or decidability of those equations is assumed.\<close>

theorem cp_conservative_abbreviation:
  assumes "cp_path s t a r b"
  shows "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b)
      x (cp_embed u) (cp_embed v) y \<longleftrightarrow> cp_equiv s t R x u v y"
  using assms by (metis cp_eliminate_embed cp_eliminate_equiv cp_embed_equiv)


lemma cp_embed_inverse [simp]: "cp_embed (inv_fg w) = inv_fg (cp_embed w)"
  by (induction w) (auto simp: cp_embed_def inv1_def)

lemma cp_embed_word_code:
  "cp_word_code (\<lambda>g. cp_embed (F g)) w = cp_embed (cp_word_code F w)"
  by (induction w) (simp_all add: cp_code_letter_def)

theorem cp_abbreviation_roundtrip:
  assumes r: "cp_path s t a r b"
    and w: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x w y"
  shows "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b)
    x w (cp_embed (cp_eliminate r w)) y"
proof -
  let ?S = "cp_ext_endpoint s a"
  let ?T = "cp_ext_endpoint t b"
  let ?R = "cp_extension R a r b"
  have generators: "cp_equiv ?S ?T ?R (id (?S g)) [(True,g)]
      (cp_embed (cp_eliminate_generator r g)) (id (?T g))" for g
  proof (cases g)
    case None
    have "cp_equiv ?S ?T ?R a [(True,None)] (cp_embed r) b"
      using r by (auto intro: cp_equiv.named simp: cp_extension_def cp_source_def cp_target_def)
    then show ?thesis by (simp add: None)
  next
    case (Some e)
    then show ?thesis by (simp add: cp_equiv_refl cp_source_def cp_target_def)
  qed
  from cp_primitive_codes_agree[OF w generators]
  show ?thesis by (simp add: cp_embed_word_code)
qed

end
