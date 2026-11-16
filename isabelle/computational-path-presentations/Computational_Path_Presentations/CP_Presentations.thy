section \<open>Typed presentations and interpretation by words\<close>

theory CP_Presentations
  imports CP_Typed_Witnesses
begin

text \<open>A presentation declares equations between parallel words.  The structural
part is the free cancellation equivalence from the imported free-group theory;
it does not identify different primitive names.  Endpoints are retained in each
judgement, including the empty word.\<close>

type_synonym ('v, 'g) cp_relations = "('v \<times> 'g word_g_i \<times> 'g word_g_i \<times> 'v) set"

inductive cp_equiv :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow>
    ('v, 'g) cp_relations \<Rightarrow> 'v \<Rightarrow> 'g word_g_i \<Rightarrow> 'g word_g_i \<Rightarrow> 'v \<Rightarrow> bool"
  for s t R where
  structural: "cp_path s t a u b \<Longrightarrow> cp_path s t a v b \<Longrightarrow>
    cp_word_eq u v \<Longrightarrow> cp_equiv s t R a u v b"
| named: "(a,u,v,b) \<in> R \<Longrightarrow> cp_path s t a u b \<Longrightarrow>
    cp_path s t a v b \<Longrightarrow> cp_equiv s t R a u v b"
| sym: "cp_equiv s t R a u v b \<Longrightarrow> cp_equiv s t R a v u b"
| trans: "cp_equiv s t R a u v b \<Longrightarrow> cp_equiv s t R a v w b \<Longrightarrow>
    cp_equiv s t R a u w b"
| comp: "cp_equiv s t R a u v b \<Longrightarrow> cp_equiv s t R b x y c \<Longrightarrow>
    cp_equiv s t R a (u@x) (v@y) c"
| inverse: "cp_equiv s t R a u v b \<Longrightarrow>
    cp_equiv s t R b (inv_fg u) (inv_fg v) a"

lemma cp_equiv_typed:
  "cp_equiv s t R a u v b \<Longrightarrow> cp_path s t a u b \<and> cp_path s t a v b"
  by (induction rule: cp_equiv.induct)
    (auto simp: cp_path_append intro: cp_path_inverse)

lemma cp_equiv_refl:
  "cp_path s t a u b \<Longrightarrow> cp_equiv s t R a u u b"
  by (rule cp_equiv.structural) (auto simp: cp_word_eq_iff_normalize)

lemma cp_equiv_mono:
  assumes "cp_equiv s t R a u v b" "R \<subseteq> S"
  shows "cp_equiv s t S a u v b"
  using assms(1)
proof (induction rule: cp_equiv.induct)
  case (structural a u b v)
  then show ?case by (rule cp_equiv.structural)
next
  case (named a u v b)
  with assms(2) show ?case by (meson cp_equiv.named subsetD)
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

text \<open>Interpretation can change the vertex map and send a primitive to an
arbitrary finite word, including the empty word.  Its hypotheses are exactly
typing of primitive codes and preservation of the declared equations.\<close>

lemma cp_path_code:
  assumes codes: "\<And>g. cp_path s' t' (f (s g)) (cp_word_code F [(True,g)]) (f (t g))"
    and path: "cp_path s t a w b"
  shows "cp_path s' t' (f a) (cp_word_code F w) (f b)"
  by (rule cp_word_code_typed[OF _ path])
    (use codes in \<open>simp add: cp_code_letter_def\<close>)

theorem cp_interpretation_sound:
  assumes eq: "cp_equiv s t R a u v b"
    and codes: "\<And>g. cp_path s' t' (f (s g)) (cp_word_code F [(True,g)]) (f (t g))"
    and relations: "\<And>a u v b. (a,u,v,b) \<in> R \<Longrightarrow>
      cp_path s t a u b \<Longrightarrow> cp_path s t a v b \<Longrightarrow>
      cp_equiv s' t' S (f a) (cp_word_code F u) (cp_word_code F v) (f b)"
  shows "cp_equiv s' t' S (f a) (cp_word_code F u) (cp_word_code F v) (f b)"
  using eq
proof (induction rule: cp_equiv.induct)
  case (structural a u b v)
  then show ?case
    by (meson cp_equiv.structural cp_path_code[where s=s and t=t and s'=s' and t'=t' and f=f and F=F, OF codes] cp_word_code_cong)
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
  then show ?case by (simp add: cp_word_code_append cp_equiv.comp)
next
  case (inverse a u v b)
  then show ?case by (simp add: cp_word_code_inverse cp_equiv.inverse)
qed

text \<open>For an empty equation set, the presentation introduces no identifications
beyond free structural cancellation. This is the precise scope of the decision
procedure; arbitrary named equations are not claimed decidable.\<close>

theorem cp_empty_presentation:
  "cp_equiv s t {} a u v b \<longleftrightarrow>
   cp_path s t a u b \<and> cp_path s t a v b \<and> cp_reduce u = cp_reduce v"
proof
  assume eq: "cp_equiv s t {} a u v b"
  have "cp_word_eq u v"
    using eq
  proof (induction rule: cp_equiv.induct)
    case (structural a u b v)
    from structural.hyps(3) show ?case .
  next
    case (named a u v b)
    then show ?case by simp
  next
    case (sym a u v b)
    from sym.IH show ?case by (rule cp_word_eq.sym)
  next
    case (trans a u v b w)
    then show ?case by (meson cp_word_eq.trans)
  next
    case (comp a u v b x y c)
    then show ?case by (meson cp_word_eq_append)
  next
    case (inverse a u v b)
    from inverse.IH show ?case by (rule cp_word_eq_inverse)
  qed
  with cp_equiv_typed[OF eq] show
    "cp_path s t a u b \<and> cp_path s t a v b \<and> cp_reduce u = cp_reduce v"
    by (simp add: cp_reduce_complete)
next
  assume "cp_path s t a u b \<and> cp_path s t a v b \<and> cp_reduce u = cp_reduce v"
  then show "cp_equiv s t {} a u v b"
    by (auto intro: cp_equiv.structural simp: cp_reduce_complete)
qed


lemma cp_word_code_identity [simp]:
  "cp_word_code (\<lambda>g. [(True,g)]) w = w"
  by (induction w) (auto simp: cp_code_letter_def inv_fg_def inv1_def split: prod.splits)

theorem cp_primitive_codes_agree:
  assumes path: "cp_path s t a w b"
    and generators: "\<And>g. cp_equiv s' t' S (f (s g)) (F g) (G g) (f (t g))"
  shows "cp_equiv s' t' S (f a) (cp_word_code F w) (cp_word_code G w) (f b)"
  using path
proof (induction w arbitrary: a)
  case Nil
  then show ?case by (simp add: cp_equiv_refl)
next
  case (Cons l w)
  obtain d g where l: "l = (d,g)" by (cases l) auto
  have letter: "cp_equiv s' t' S (f (cp_source s t l))
      (cp_code_letter F l) (cp_code_letter G l) (f (cp_target s t l))"
    using generators[of g] cp_equiv.inverse[OF generators[of g]]
    by (cases d) (simp_all add: l cp_source_def cp_target_def cp_code_letter_def)
  have tail: "cp_equiv s' t' S (f (cp_target s t l))
      (cp_word_code F w) (cp_word_code G w) (f b)"
    using Cons by auto
  show ?case using cp_equiv.comp[OF letter tail] Cons.prems by simp
qed

end
