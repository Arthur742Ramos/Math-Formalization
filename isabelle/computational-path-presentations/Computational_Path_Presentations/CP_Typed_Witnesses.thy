section \<open>Endpoint-typed witnesses and their signed words\<close>

theory CP_Typed_Witnesses
  imports CP_Word_Normalization
begin

text \<open>Signs use the convention that True traverses a generator forwards.
  Endpoint typing is a predicate, rather than an identification of all words
  with paths. In particular an empty word has an explicitly supplied vertex.\<close>

definition cp_source :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow> 'g g_i \<Rightarrow> 'v" where
  "cp_source s t l = (if fst l then s (snd l) else t (snd l))"

definition cp_target :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow> 'g g_i \<Rightarrow> 'v" where
  "cp_target s t l = (if fst l then t (snd l) else s (snd l))"

fun cp_path :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'g word_g_i \<Rightarrow> 'v \<Rightarrow> bool" where
  "cp_path s t a [] b = (a = b)"
| "cp_path s t a (l # w) b = (a = cp_source s t l \<and> cp_path s t (cp_target s t l) w b)"

lemma cp_inverse_endpoints [simp]:
  "cp_source s t (inv1 l) = cp_target s t l"
  "cp_target s t (inv1 l) = cp_source s t l"
  by (simp_all add: cp_source_def cp_target_def inv1_def)

lemma cp_path_append:
  "cp_path s t a (u @ v) c \<longleftrightarrow> (\<exists>b. cp_path s t a u b \<and> cp_path s t b v c)"
  by (induction u arbitrary: a) auto

lemma cp_path_inverse:
  "cp_path s t a w b \<Longrightarrow> cp_path s t b (inv_fg w) a"
  by (induction w arbitrary: a) (auto simp: inv_fg_def cp_path_append)

lemma cp_path_inverse_iff [simp]:
  "cp_path s t b (inv_fg w) a \<longleftrightarrow> cp_path s t a w b"
  using cp_path_inverse inv_idemp by metis

lemma cp_canceling_endpoints:
  assumes "canceling x y"
  shows "cp_source s t x = cp_target s t y"
    and "cp_target s t x = cp_source s t y"
  using assms by (auto simp: canceling_def cp_source_def cp_target_def)

lemma cp_path_cancel_step:
  assumes "cp_path s t a u b" and "cancels_to_1 u v"
  shows "cp_path s t a v b"
proof -
  obtain p x y q where uv: "u = p @ x # y # q" "v = p @ q" and xy: "canceling x y"
    using assms(2) by (rule cancels_to_1_unfold)
  have endpoint: "cp_source s t x = cp_target s t y"
    by (rule cp_canceling_endpoints[OF xy])
  show ?thesis
    using assms(1) endpoint by (auto simp: uv cp_path_append)
qed

lemma cp_path_cancels_to:
  assumes "cancels_to u v" and "cp_path s t a u b"
  shows "cp_path s t a v b"
  using assms(1) unfolding cancels_to_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule assms(2))
next
  case (step y z)
  show ?case by (rule cp_path_cancel_step[OF step.IH step.hyps(2)])
qed

lemma cp_path_normalize:
  "cp_path s t a w b \<Longrightarrow> cp_path s t a (normalize w) b"
  by (rule cp_path_cancels_to[OF normalized_cancels_to]; assumption)

text \<open>Confluence is inherited from the AFP cancellation relation;
  the additional assertion is that the joining word retains both endpoints.\<close>

theorem cp_typed_reduction_diamond:
  assumes "cp_path s t a w b" "cancels_to w u" "cancels_to w v"
  shows "\<exists>z. cp_path s t a z b \<and> cancels_to u z \<and> cancels_to v z"
proof -
  obtain z where z: "cancels_to u z" "cancels_to v z"
    using confluentD[OF confluent_cancels_to_1] assms(2,3)
    unfolding cancels_to_def by blast
  have "cp_path s t a u b"
    by (rule cp_path_cancels_to[OF assms(2) assms(1)])
  then have "cp_path s t a z b"
    by (rule cp_path_cancels_to[OF z(1)])
  with z show ?thesis by blast
qed

subsection \<open>Binary witnesses\<close>

datatype ('v, 'g) cp_tree =
    CP_Id 'v
  | CP_Gen 'g
  | CP_Inv "('v, 'g) cp_tree"
  | CP_Comp "('v, 'g) cp_tree" "('v, 'g) cp_tree"

inductive cp_typed :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow> ('v, 'g) cp_tree \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  for s t where
  identity: "cp_typed s t (CP_Id a) a a"
| generator: "cp_typed s t (CP_Gen e) (s e) (t e)"
| inverse: "cp_typed s t p a b \<Longrightarrow> cp_typed s t (CP_Inv p) b a"
| composition: "cp_typed s t p a b \<Longrightarrow> cp_typed s t q b c \<Longrightarrow> cp_typed s t (CP_Comp p q) a c"

fun cp_flat :: "('v, 'g) cp_tree \<Rightarrow> 'g word_g_i" where
  "cp_flat (CP_Id a) = []"
| "cp_flat (CP_Gen e) = [(True, e)]"
| "cp_flat (CP_Inv p) = inv_fg (cp_flat p)"
| "cp_flat (CP_Comp p q) = cp_flat p @ cp_flat q"

lemma cp_flat_typed:
  "cp_typed s t p a b \<Longrightarrow> cp_path s t a (cp_flat p) b"
  by (induction rule: cp_typed.induct)
     (auto simp: cp_source_def cp_target_def cp_path_append intro: cp_path_inverse)

fun cp_letter_tree :: "'g g_i \<Rightarrow> ('v, 'g) cp_tree" where
  "cp_letter_tree (True, e) = CP_Gen e"
| "cp_letter_tree (False, e) = CP_Inv (CP_Gen e)"

lemma cp_letter_tree_flat [simp]: "cp_flat (cp_letter_tree l) = [l]"
  by (cases l; cases "fst l") (auto simp: inv_fg_def inv1_def)

lemma cp_letter_tree_typed:
  "cp_typed s t (cp_letter_tree l) (cp_source s t l) (cp_target s t l)"
  by (cases l; cases "fst l")
     (auto simp: cp_source_def cp_target_def intro: cp_typed.intros)

fun cp_quote :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'g word_g_i \<Rightarrow> ('v, 'g) cp_tree" where
  "cp_quote s t a [] = CP_Id a"
| "cp_quote s t a (l # w) = CP_Comp (cp_letter_tree l) (cp_quote s t (cp_target s t l) w)"

lemma cp_flat_quote [simp]: "cp_flat (cp_quote s t a w) = w"
  by (induction w arbitrary: a) auto

lemma cp_quote_typed:
  "cp_path s t a w b \<Longrightarrow> cp_typed s t (cp_quote s t a w) a b"
  by (induction w arbitrary: a)
     (auto intro: cp_typed.intros cp_letter_tree_typed)

text \<open>The word is recovered literally. The converse returns a canonical
  right-associated tree, not the original parentheses. This statement does not
  identify a binary realization schedule with an equal-slot realization.\<close>

theorem cp_typed_tree_word_correspondence:
  "(\<exists>p. cp_typed s t p a b \<and> cp_flat p = w) \<longleftrightarrow> cp_path s t a w b"
proof
  assume "\<exists>p. cp_typed s t p a b \<and> cp_flat p = w"
  then obtain p where "cp_typed s t p a b" "cp_flat p = w" by blast
  then show "cp_path s t a w b" using cp_flat_typed[of s t p a b] by simp
next
  assume "cp_path s t a w b"
  then have "cp_typed s t (cp_quote s t a w) a b" by (rule cp_quote_typed)
  then show "\<exists>p. cp_typed s t p a b \<and> cp_flat p = w" by force
qed


lemma cp_path_reduce:
  "cp_path s t a w b \<Longrightarrow> cp_path s t a (cp_reduce w) b"
  by (simp add: cp_reduce_eq_normalize cp_path_normalize)

theorem cp_typed_word_eq_iff_common_reduct:
  assumes "cp_path s t a u b" "cp_path s t a v b"
  shows "cp_word_eq u v \<longleftrightarrow>
    (\<exists>z. cp_path s t a z b \<and> cancels_to u z \<and> cancels_to v z)"
proof
  assume "cp_word_eq u v"
  then have "cp_reduce u = cp_reduce v" by (simp add: cp_reduce_complete)
  moreover have "cp_path s t a (cp_reduce u) b"
    using assms(1) by (rule cp_path_reduce)
  ultimately show "\<exists>z. cp_path s t a z b \<and> cancels_to u z \<and> cancels_to v z"
    using cp_reduce_sound by metis
next
  assume "\<exists>z. cp_path s t a z b \<and> cancels_to u z \<and> cancels_to v z"
  then obtain z where "cp_word_eq u z" "cp_word_eq v z"
    by (blast intro: cp_cancels_word_eq)
  then show "cp_word_eq u v" using cp_word_eq.sym cp_word_eq.trans by blast
qed

subsection \<open>Endpoint-preserving word substitutions\<close>

lemma cp_code_letter_typed:
  assumes "\<And>e. cp_path s' t' (f (s e)) (F e) (f (t e))"
  shows "cp_path s' t' (f (cp_source s t l)) (cp_code_letter F l)
    (f (cp_target s t l))"
  using assms cp_path_inverse
  by (auto simp: cp_source_def cp_target_def cp_code_letter_def)

theorem cp_word_code_typed:
  assumes code: "\<And>e. cp_path s' t' (f (s e)) (F e) (f (t e))"
    and path: "cp_path s t a w b"
  shows "cp_path s' t' (f a) (cp_word_code F w) (f b)"
  using path
  by (induction w arbitrary: a)
     (auto simp: cp_path_append intro: cp_code_letter_typed[where s=s and t=t and s'=s' and t'=t' and f=f and F=F, OF code])

subsection \<open>Canonical typed representatives\<close>

definition cp_normal_tree :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> ('v, 'g) cp_tree \<Rightarrow> ('v, 'g) cp_tree" where
  "cp_normal_tree s t a p = cp_quote s t a (cp_reduce (cp_flat p))"

lemma cp_normal_tree_typed:
  "cp_typed s t p a b \<Longrightarrow> cp_typed s t (cp_normal_tree s t a p) a b"
  unfolding cp_normal_tree_def
  by (intro cp_quote_typed cp_path_reduce cp_flat_typed; assumption)

lemma cp_flat_normal_tree [simp]:
  "cp_flat (cp_normal_tree s t a p) = cp_reduce (cp_flat p)"
  by (simp add: cp_normal_tree_def)

lemma cp_normal_tree_idempotent:
  "cp_normal_tree s t a (cp_normal_tree s t a p) = cp_normal_tree s t a p"
  by (simp add: cp_normal_tree_def)

text \<open>The following equality criterion concerns the explicit word
  congruence. It is not a claim that two literal binary trees are equal, nor
  a completeness theorem for arbitrary additional presentation equations.\<close>

theorem cp_normal_tree_complete:
  "cp_normal_tree s t a p = cp_normal_tree s t a q \<longleftrightarrow>
    cp_word_eq (cp_flat p) (cp_flat q)"
proof
  assume "cp_normal_tree s t a p = cp_normal_tree s t a q"
  then have "cp_reduce (cp_flat p) = cp_reduce (cp_flat q)"
    by (metis cp_flat_normal_tree)
  then show "cp_word_eq (cp_flat p) (cp_flat q)"
    by (simp add: cp_reduce_complete)
next
  assume "cp_word_eq (cp_flat p) (cp_flat q)"
  then show "cp_normal_tree s t a p = cp_normal_tree s t a q"
    by (simp add: cp_normal_tree_def cp_reduce_complete)
qed

end
