section \<open>Changing relations and reversible word interpretations\<close>

theory CP_Presentation_Equivalence
  imports CP_Conservative_Extension
begin

text \<open>The results below are consequences of the typed presentation semantics.
They describe sufficient and necessary conditions for replacing equations, and
sufficient conditions for changing generators by reversible word interpretations.
Only well-typed declared equations are active: an ill-typed tuple in a relation
set has no effect on its generated equivalence. No decision procedure for an
arbitrary presentation is assumed.\<close>

subsection \<open>Replacement of defining equations\<close>

lemma cp_equiv_relation_transfer:
  assumes eq: "cp_equiv s t R a u v b"
    and relations: "\<And>a u v b. (a,u,v,b) \<in> R \<Longrightarrow>
      cp_path s t a u b \<Longrightarrow> cp_path s t a v b \<Longrightarrow>
      cp_equiv s t S a u v b"
  shows "cp_equiv s t S a u v b"
  using eq
proof (induction rule: cp_equiv.induct)
  case (structural a u b v)
  then show ?case by (rule cp_equiv.structural)
next
  case (named a u v b)
  then show ?case by (rule relations)
next
  case (sym a u v b)
  from sym.IH show ?case by (rule cp_equiv.sym)
next
  case (trans a u v b w)
  then show ?case by (meson cp_equiv.trans)
next
  case (comp a u v b x y c)
  then show ?case by (meson cp_equiv.comp)
next
  case (inverse a u v b)
  from inverse.IH show ?case by (rule cp_equiv.inverse)
qed

theorem cp_relation_replacement_iff:
  "(\<forall>a u v b. cp_equiv s t R a u v b \<longleftrightarrow> cp_equiv s t S a u v b)
   \<longleftrightarrow>
   ((\<forall>a u v b. (a,u,v,b) \<in> R \<longrightarrow> cp_path s t a u b \<longrightarrow>
       cp_path s t a v b \<longrightarrow> cp_equiv s t S a u v b) \<and>
    (\<forall>a u v b. (a,u,v,b) \<in> S \<longrightarrow> cp_path s t a u b \<longrightarrow>
       cp_path s t a v b \<longrightarrow> cp_equiv s t R a u v b))"
  by (meson cp_equiv.named cp_equiv_relation_transfer)

theorem cp_redundant_relations_iff:
  "(\<forall>a u v b. cp_equiv s t (R \<union> S) a u v b \<longleftrightarrow> cp_equiv s t R a u v b)
   \<longleftrightarrow>
   (\<forall>a u v b. (a,u,v,b) \<in> S \<longrightarrow> cp_path s t a u b \<longrightarrow>
      cp_path s t a v b \<longrightarrow> cp_equiv s t R a u v b)"
  by (simp only: cp_relation_replacement_iff)
    (auto intro: cp_equiv.named)

text \<open>Adding an already derivable equation, or deleting it again, is the
relation part of a Tietze move. This holds with any other named equations
present, not just for a free presentation.\<close>

theorem cp_tietze_relation_move:
  assumes derived: "cp_equiv s t R a r q b"
  shows "cp_equiv s t (Set.insert (a,r,q,b) R) x u v y \<longleftrightarrow>
    cp_equiv s t R x u v y"
proof -
  have "\<forall>x u v y. cp_equiv s t (R \<union> {(a,r,q,b)}) x u v y \<longleftrightarrow>
      cp_equiv s t R x u v y"
    using derived by (subst cp_redundant_relations_iff) auto
  then show ?thesis by simp
qed

subsection \<open>Composition of word interpretations\<close>

lemma cp_word_code_compose:
  "cp_word_code G (cp_word_code F w) =
    cp_word_code (\<lambda>g. cp_word_code G (F g)) w"
  by (induction w) (simp_all add: cp_code_letter_def)

text \<open>The following maps fix vertices, but may change the generator type.
A code can be any typed finite word, including an empty word for a loop.\<close>

definition cp_presentation_map ::
  "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow> ('v,'g) cp_relations \<Rightarrow>
   ('h \<Rightarrow> 'v) \<Rightarrow> ('h \<Rightarrow> 'v) \<Rightarrow> ('v,'h) cp_relations \<Rightarrow>
   ('g \<Rightarrow> 'h word_g_i) \<Rightarrow> bool" where
  "cp_presentation_map s t R s' t' S F \<longleftrightarrow>
    (\<forall>g. cp_path s' t' (s g) (F g) (t g)) \<and>
    (\<forall>a u v b. (a,u,v,b) \<in> R \<longrightarrow> cp_path s t a u b \<longrightarrow>
      cp_path s t a v b \<longrightarrow>
      cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b)"

lemma cp_presentation_map_codes:
  assumes "cp_presentation_map s t R s' t' S F"
  shows "cp_path s' t' (s g) (F g) (t g)"
  using assms unfolding cp_presentation_map_def by blast

lemma cp_presentation_map_relations:
  assumes "cp_presentation_map s t R s' t' S F"
    and "(a,u,v,b) \<in> R" "cp_path s t a u b" "cp_path s t a v b"
  shows "cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b"
  using assms unfolding cp_presentation_map_def by blast

lemma cp_presentation_map_path:
  assumes map: "cp_presentation_map s t R s' t' S F"
    and path: "cp_path s t a w b"
  shows "cp_path s' t' a (cp_word_code F w) b"
proof -
  have codes: "cp_path s' t' (id (s g))
      (cp_word_code F [(True,g)]) (id (t g))" for g
    using cp_presentation_map_codes[OF map, of g] by (simp add: cp_code_letter_def)
  from cp_path_code[where s=s and t=t and s'=s' and t'=t' and f=id and F=F,
      OF codes path]
  show ?thesis by simp
qed

lemma cp_presentation_map_sound:
  assumes map: "cp_presentation_map s t R s' t' S F"
    and eq: "cp_equiv s t R a u v b"
  shows "cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b"
  using eq
proof (induction rule: cp_equiv.induct)
  case (structural a u b v)
  show ?case
    by (rule cp_equiv.structural[OF
      cp_presentation_map_path[OF map structural.hyps(1)]
      cp_presentation_map_path[OF map structural.hyps(2)]
      cp_word_code_cong[OF structural.hyps(3)]])
next
  case (named a u v b)
  show ?case by (rule cp_presentation_map_relations[OF map named.hyps])
next
  case (sym a u v b)
  from sym.IH show ?case by (rule cp_equiv.sym)
next
  case (trans a u v b w)
  show ?case by (rule cp_equiv.trans[OF trans.IH])
next
  case (comp a u v b x y c)
  from cp_equiv.comp[OF comp.IH] show ?case by simp
next
  case (inverse a u v b)
  from cp_equiv.inverse[OF inverse.IH] show ?case by simp
qed

lemma cp_presentation_map_identity:
  "cp_presentation_map s t R s t R (\<lambda>g. [(True,g)])"
  by (auto simp: cp_presentation_map_def cp_source_def cp_target_def
    intro: cp_equiv.named)

theorem cp_presentation_map_compose:
  assumes F: "cp_presentation_map s t R s' t' S F"
    and G: "cp_presentation_map s' t' S s'' t'' T G"
  shows "cp_presentation_map s t R s'' t'' T (\<lambda>g. cp_word_code G (F g))"
proof (unfold cp_presentation_map_def, intro conjI allI impI)
  fix g
  have "cp_path s' t' (s g) (F g) (t g)"
    by (rule cp_presentation_map_codes[OF F])
  from cp_presentation_map_path[OF G this]
  show "cp_path s'' t'' (s g) (cp_word_code G (F g)) (t g)" .
next
  fix a u v b
  assume rel: "(a,u,v,b) \<in> R" and u: "cp_path s t a u b" and v: "cp_path s t a v b"
  have "cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b"
    by (rule cp_presentation_map_relations[OF F rel u v])
  from cp_presentation_map_sound[OF G this]
  show "cp_equiv s'' t'' T a (cp_word_code (\<lambda>g. cp_word_code G (F g)) u)
      (cp_word_code (\<lambda>g. cp_word_code G (F g)) v) b"
    by (simp add: cp_word_code_compose)
qed

subsection \<open>Reversible interpretations\<close>

text \<open>Checking a roundtrip on primitive generators suffices to check it on
all paths. The roundtrip need only hold in the presented equivalence, not as
literal equality of words or as free cancellation equivalence.\<close>

theorem cp_word_code_roundtrip:
  assumes path: "cp_path s t a w b"
    and primitive: "\<And>g. cp_equiv s t R (s g)
      (cp_word_code G (F g)) [(True,g)] (t g)"
  shows "cp_equiv s t R a (cp_word_code G (cp_word_code F w)) w b"
proof -
  have generators: "cp_equiv s t R (id (s g))
      (cp_word_code G (F g)) [(True,g)] (id (t g))" for g
    by (simp add: primitive)
  from cp_primitive_codes_agree[where s=s and t=t and s'=s and t'=t and S=R and f=id
      and F="\<lambda>g. cp_word_code G (F g)" and G="\<lambda>g. [(True,g)]", OF path generators]
  show ?thesis by (simp add: cp_word_code_compose)
qed

theorem cp_presentation_map_reflects:
  assumes F: "cp_presentation_map s t R s' t' S F"
    and G: "cp_presentation_map s' t' S s t R G"
    and primitive: "\<And>g. cp_equiv s t R (s g)
      (cp_word_code G (F g)) [(True,g)] (t g)"
    and u: "cp_path s t a u b" and v: "cp_path s t a v b"
  shows "cp_equiv s t R a u v b \<longleftrightarrow>
    cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b"
proof
  assume "cp_equiv s t R a u v b"
  then show "cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b"
    by (rule cp_presentation_map_sound[OF F])
next
  assume "cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b"
  from cp_presentation_map_sound[OF G this]
  have image: "cp_equiv s t R a (cp_word_code G (cp_word_code F u))
      (cp_word_code G (cp_word_code F v)) b" .
  have left: "cp_equiv s t R a (cp_word_code G (cp_word_code F u)) u b"
    by (rule cp_word_code_roundtrip[OF u primitive])
  have right: "cp_equiv s t R a (cp_word_code G (cp_word_code F v)) v b"
    by (rule cp_word_code_roundtrip[OF v primitive])
  from cp_equiv.trans[OF cp_equiv.sym[OF left] cp_equiv.trans[OF image right]]
  show "cp_equiv s t R a u v b" .
qed

locale cp_reversible_presentations =
  fixes s :: "'g \<Rightarrow> 'v" and t :: "'g \<Rightarrow> 'v"
    and R :: "('v,'g) cp_relations"
    and s' :: "'h \<Rightarrow> 'v" and t' :: "'h \<Rightarrow> 'v"
    and S :: "('v,'h) cp_relations"
    and F :: "'g \<Rightarrow> 'h word_g_i" and G :: "'h \<Rightarrow> 'g word_g_i"
  assumes forward: "cp_presentation_map s t R s' t' S F"
    and backward: "cp_presentation_map s' t' S s t R G"
    and primitive_source: "\<And>g. cp_equiv s t R (s g)
      (cp_word_code G (F g)) [(True,g)] (t g)"
    and primitive_target: "\<And>h. cp_equiv s' t' S (s' h)
      (cp_word_code F (G h)) [(True,h)] (t' h)"
begin

theorem source_roundtrip:
  "cp_path s t a w b \<Longrightarrow>
    cp_equiv s t R a (cp_word_code G (cp_word_code F w)) w b"
  by (rule cp_word_code_roundtrip[OF _ primitive_source])

theorem target_roundtrip:
  "cp_path s' t' a w b \<Longrightarrow>
    cp_equiv s' t' S a (cp_word_code F (cp_word_code G w)) w b"
  by (rule cp_word_code_roundtrip[OF _ primitive_target])

theorem source_equivalence:
  assumes "cp_path s t a u b" "cp_path s t a v b"
  shows "cp_equiv s t R a u v b \<longleftrightarrow>
    cp_equiv s' t' S a (cp_word_code F u) (cp_word_code F v) b"
  by (rule cp_presentation_map_reflects[OF forward backward primitive_source assms])

theorem target_equivalence:
  assumes "cp_path s' t' a u b" "cp_path s' t' a v b"
  shows "cp_equiv s' t' S a u v b \<longleftrightarrow>
    cp_equiv s t R a (cp_word_code G u) (cp_word_code G v) b"
  by (rule cp_presentation_map_reflects[OF backward forward primitive_target assms])

theorem target_coverage:
  assumes "cp_path s' t' a w b"
  shows "\<exists>u. cp_path s t a u b \<and> cp_equiv s' t' S a (cp_word_code F u) w b"
  using cp_presentation_map_path[OF backward assms] target_roundtrip[OF assms]
  by blast

theorem source_coverage:
  assumes "cp_path s t a w b"
  shows "\<exists>u. cp_path s' t' a u b \<and> cp_equiv s t R a (cp_word_code G u) w b"
  using cp_presentation_map_path[OF forward assms] source_roundtrip[OF assms]
  by blast

text \<open>A complete invariant on one presentation transports along the reverse
interpretation. If the reverse generator codes, the invariant, and equality on
its result type are executable, this gives a decision procedure on typed target
paths. The hypothesis supplies
the complete source invariant; it is not asserted for arbitrary presentations.\<close>

theorem target_complete_invariant:
  assumes invariant: "\<And>a u v b. cp_path s t a u b \<Longrightarrow> cp_path s t a v b \<Longrightarrow>
      (cp_equiv s t R a u v b \<longleftrightarrow> N u = N v)"
    and u: "cp_path s' t' a u b" and v: "cp_path s' t' a v b"
  shows "cp_equiv s' t' S a u v b \<longleftrightarrow>
    N (cp_word_code G u) = N (cp_word_code G v)"
  using target_equivalence[OF u v]
    invariant[OF cp_presentation_map_path[OF backward u] cp_presentation_map_path[OF backward v]]
  by blast

end

subsection \<open>Decision transport for a defined generator\<close>

text \<open>A generator added with its defining equation can be eliminated from
arbitrary extended paths, not only from embedded old paths. Consequently a
free base presentation still has an executable complete invariant after the
new equation is introduced.\<close>

theorem cp_abbreviation_equivalence:
  assumes r: "cp_path s t a r b"
    and u: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x u y"
    and v: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x v y"
  shows "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b) x u v y
    \<longleftrightarrow> cp_equiv s t R x (cp_eliminate r u) (cp_eliminate r v) y"
proof
  assume "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension R a r b) x u v y"
  then show "cp_equiv s t R x (cp_eliminate r u) (cp_eliminate r v) y"
    by (rule cp_eliminate_equiv[OF r])
next
  let ?s = "cp_ext_endpoint s a"
  let ?t = "cp_ext_endpoint t b"
  let ?R = "cp_extension R a r b"
  assume "cp_equiv s t R x (cp_eliminate r u) (cp_eliminate r v) y"
  from cp_embed_equiv[OF this]
  have image: "cp_equiv ?s ?t ?R x (cp_embed (cp_eliminate r u)) (cp_embed (cp_eliminate r v)) y" .
  have left: "cp_equiv ?s ?t ?R x u (cp_embed (cp_eliminate r u)) y"
    by (rule cp_abbreviation_roundtrip[OF r u])
  have right: "cp_equiv ?s ?t ?R x v (cp_embed (cp_eliminate r v)) y"
    by (rule cp_abbreviation_roundtrip[OF r v])
  from cp_equiv.trans[OF left cp_equiv.trans[OF image cp_equiv.sym[OF right]]]
  show "cp_equiv ?s ?t ?R x u v y" .
qed

theorem cp_abbreviation_free_normal_form:
  assumes r: "cp_path s t a r b"
  shows "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension {} a r b) x u v y
    \<longleftrightarrow>
    cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x u y \<and>
    cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x v y \<and>
    cp_reduce (cp_eliminate r u) = cp_reduce (cp_eliminate r v)"
proof
  assume eq: "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension {} a r b) x u v y"
  from cp_equiv_typed[OF eq] cp_eliminate_equiv[OF r eq]
  show "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x u y \<and>
      cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x v y \<and>
      cp_reduce (cp_eliminate r u) = cp_reduce (cp_eliminate r v)"
    by (simp add: cp_empty_presentation)
next
  assume rhs: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x u y \<and>
      cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x v y \<and>
      cp_reduce (cp_eliminate r u) = cp_reduce (cp_eliminate r v)"
  then have u: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x u y"
    and v: "cp_path (cp_ext_endpoint s a) (cp_ext_endpoint t b) x v y" by auto
  have "cp_equiv s t {} x (cp_eliminate r u) (cp_eliminate r v) y"
    using rhs cp_eliminate_typed[OF r u] cp_eliminate_typed[OF r v]
    by (simp add: cp_empty_presentation)
  then show "cp_equiv (cp_ext_endpoint s a) (cp_ext_endpoint t b) (cp_extension {} a r b) x u v y"
    using cp_abbreviation_equivalence[OF r u v] by blast
qed

end
