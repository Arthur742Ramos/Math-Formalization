section \<open>The algebraic torus presentation\<close>

theory CP_Torus_Presentation
  imports CP_Presentations CP_Tree_Congruence
begin

text \<open>This is the algebraic presentation with one vertex, two generators,
  and the single relation AB = BA.  It formalizes the normal-form calculation
  of Section 13.3, Proposition 13.15 of the companion preprint of
  \<^cite>\<open>Ramos2026Calculus\<close>.  No geometric torus, topological fundamental group, or completeness
  theorem for geometric homotopy is asserted.\<close>

datatype cp_torus_generator = Torus_A | Torus_B

abbreviation cp_torus_vertex :: "cp_torus_generator \<Rightarrow> unit" where
  "cp_torus_vertex \<equiv> \<lambda>_. ()"

definition cp_torus_relations :: "(unit, cp_torus_generator) cp_relations" where
  "cp_torus_relations = {((), [(True,Torus_A),(True,Torus_B)],
    [(True,Torus_B),(True,Torus_A)], ())}"

abbreviation cp_torus_equiv ::
    "cp_torus_generator word_g_i \<Rightarrow> cp_torus_generator word_g_i \<Rightarrow> bool" where
  "cp_torus_equiv u v \<equiv>
    cp_equiv cp_torus_vertex cp_torus_vertex cp_torus_relations () u v ()"

lemma cp_torus_path [simp]: "cp_path cp_torus_vertex cp_torus_vertex a w b"
  by (induction w arbitrary: a) (simp_all add: cp_source_def cp_target_def)

lemma cp_torus_refl [simp]: "cp_torus_equiv w w"
  by (rule cp_equiv_refl) simp

lemma cp_torus_structural:
  "cp_word_eq u v \<Longrightarrow> cp_torus_equiv u v"
  by (rule cp_equiv.structural) simp_all

lemma cp_torus_context:
  assumes uv: "cp_torus_equiv u v"
  shows "cp_torus_equiv (p @ u @ q) (p @ v @ q)"
proof -
  have tail: "cp_torus_equiv (u @ q) (v @ q)"
    by (rule cp_equiv.comp[OF uv cp_torus_refl])
  show ?thesis by (rule cp_equiv.comp[OF cp_torus_refl tail])
qed

subsection \<open>The integer-pair invariant\<close>

fun cp_torus_weight :: "cp_torus_generator \<Rightarrow> cp_torus_generator g_i \<Rightarrow> int" where
  "cp_torus_weight g (d,h) = (if h = g then if d then 1 else -1 else 0)"

definition cp_torus_exponent :: "cp_torus_generator \<Rightarrow> cp_torus_generator word_g_i \<Rightarrow> int" where
  "cp_torus_exponent g w = sum_list (map (cp_torus_weight g) w)"

definition cp_torus_exponents :: "cp_torus_generator word_g_i \<Rightarrow> int \<times> int" where
  "cp_torus_exponents w = (cp_torus_exponent Torus_A w, cp_torus_exponent Torus_B w)"

lemma cp_torus_exponent_Nil [simp]: "cp_torus_exponent g [] = 0"
  by (simp add: cp_torus_exponent_def)

lemma cp_torus_exponent_Cons [simp]:
  "cp_torus_exponent g (l # w) = cp_torus_weight g l + cp_torus_exponent g w"
  by (simp add: cp_torus_exponent_def)

lemma cp_torus_exponent_append [simp]:
  "cp_torus_exponent g (u @ v) = cp_torus_exponent g u + cp_torus_exponent g v"
  by (simp add: cp_torus_exponent_def)

lemma cp_torus_weight_inverse [simp]:
  "cp_torus_weight g (inv1 l) = - cp_torus_weight g l"
  by (cases l) (simp add: inv1_def)

lemma cp_torus_exponent_inverse [simp]:
  "cp_torus_exponent g (inv_fg w) = - cp_torus_exponent g w"
  by (induction w) simp_all

lemma cp_torus_exponent_cancel:
  assumes "cancels_to_1 u v"
  shows "cp_torus_exponent g u = cp_torus_exponent g v"
proof -
  obtain p x y q where uv: "u = p @ x # y # q" "v = p @ q"
    and xy: "canceling x y" using assms by (rule cancels_to_1_unfold)
  from xy have "y = inv1 x" by (rule cp_canceling_inv1)
  then show ?thesis by (simp add: uv)
qed

lemma cp_torus_exponent_structural:
  "cp_word_eq u v \<Longrightarrow> cp_torus_exponent g u = cp_torus_exponent g v"
  by (induction rule: cp_word_eq.induct) (auto intro: cp_torus_exponent_cancel)

theorem cp_torus_exponent_invariant:
  "cp_equiv cp_torus_vertex cp_torus_vertex cp_torus_relations a u v b \<Longrightarrow>
    cp_torus_exponent g u = cp_torus_exponent g v"
  by (induction rule: cp_equiv.induct)
     (auto simp: cp_torus_relations_def intro: cp_torus_exponent_structural)

corollary cp_torus_exponents_invariant:
  "cp_torus_equiv u v \<Longrightarrow> cp_torus_exponents u = cp_torus_exponents v"
  by (simp add: cp_torus_exponents_def cp_torus_exponent_invariant)

subsection \<open>Commutation derived from the single declared relation\<close>

lemma cp_torus_commute:
  "cp_torus_equiv [(True,Torus_A),(True,Torus_B)] [(True,Torus_B),(True,Torus_A)]"
  by (rule cp_equiv.named) (simp_all add: cp_torus_relations_def)

lemma cp_torus_cancel_pair:
  "cp_torus_equiv (l # inv1 l # w) w"
proof (rule cp_torus_structural, rule cp_word_eq.cancel)
  show "cancels_to_1 (l # inv1 l # w) w"
    using cancels_to_1_fold[of l "inv1 l" "[]" w]
    by (simp add: canceling_def inv1_def)
qed

lemma cp_torus_commute_inverse_left:
  assumes commute: "cp_torus_equiv [l,k] [k,l]"
  shows "cp_torus_equiv [inv1 l,k] [k,inv1 l]"
proof -
  have left: "cp_torus_equiv [inv1 l,l,k,inv1 l] [k,inv1 l]"
    using cp_torus_cancel_pair[of "inv1 l" "[k,inv1 l]"] by simp
  have right: "cp_torus_equiv [inv1 l,k,l,inv1 l] [inv1 l,k]"
    using cp_torus_context[OF cp_torus_cancel_pair[of l "[]"], of "[inv1 l,k]" "[]"] by simp
  have middle: "cp_torus_equiv [inv1 l,l,k,inv1 l] [inv1 l,k,l,inv1 l]"
    using cp_torus_context[OF commute, of "[inv1 l]" "[inv1 l]"] by simp
  show ?thesis
    by (rule cp_equiv.trans[OF cp_equiv.sym[OF right]
        cp_equiv.trans[OF cp_equiv.sym[OF middle] left]])
qed

lemma cp_torus_signed_commute:
  "cp_torus_equiv [(d,Torus_A),(e,Torus_B)] [(e,Torus_B),(d,Torus_A)]"
proof -
  have pp: "cp_torus_equiv [(True,Torus_A),(True,Torus_B)] [(True,Torus_B),(True,Torus_A)]"
    by (rule cp_torus_commute)
  have np: "cp_torus_equiv [(False,Torus_A),(True,Torus_B)] [(True,Torus_B),(False,Torus_A)]"
    using cp_torus_commute_inverse_left[OF pp] by (simp add: inv1_def)
  have pn: "cp_torus_equiv [(True,Torus_A),(False,Torus_B)] [(False,Torus_B),(True,Torus_A)]"
    using cp_equiv.sym[OF cp_torus_commute_inverse_left[OF cp_equiv.sym[OF pp]]]
    by (simp add: inv1_def)
  have nn: "cp_torus_equiv [(False,Torus_A),(False,Torus_B)] [(False,Torus_B),(False,Torus_A)]"
    using cp_torus_commute_inverse_left[OF pn] by (simp add: inv1_def)
  show ?thesis by (cases d; cases e) (use pp np pn nn in auto)
qed

lemma cp_torus_commute_replicate:
  "cp_torus_equiv ((e,Torus_B) # replicate n (d,Torus_A))
    (replicate n (d,Torus_A) @ [(e,Torus_B)])"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have swap: "cp_torus_equiv
    ((e,Torus_B) # (d,Torus_A) # replicate n (d,Torus_A))
    ((d,Torus_A) # (e,Torus_B) # replicate n (d,Torus_A))"
    using cp_equiv.comp[OF cp_equiv.sym[OF cp_torus_signed_commute[of d e]]
      cp_torus_refl[of "replicate n (d,Torus_A)"]] by simp
  have tail: "cp_torus_equiv
    ((d,Torus_A) # (e,Torus_B) # replicate n (d,Torus_A))
    ((d,Torus_A) # (replicate n (d,Torus_A) @ [(e,Torus_B)]))"
    using cp_equiv.comp[OF cp_torus_refl[of "[(d,Torus_A)]"] Suc.IH] by simp
  show ?case using cp_equiv.trans[OF swap tail] by simp
qed

subsection \<open>Signed powers and canonical representatives\<close>

definition cp_torus_power :: "cp_torus_generator \<Rightarrow> int \<Rightarrow> cp_torus_generator word_g_i" where
  "cp_torus_power g z = (if 0 \<le> z then replicate (nat z) (True,g)
    else replicate (nat (-z)) (False,g))"

lemma cp_torus_power_nonneg [simp]: "cp_torus_power g (int n) = replicate n (True,g)"
  by (simp add: cp_torus_power_def)

lemma cp_torus_power_neg [simp]: "cp_torus_power g (- int n) = replicate n (False,g)"
  by (cases "n = 0") (simp_all add: cp_torus_power_def)

lemma cp_torus_power_zero [simp]: "cp_torus_power g 0 = []"
  by (simp add: cp_torus_power_def)

lemma cp_torus_power_positive_step:
  "cp_torus_equiv ((True,g) # cp_torus_power g z) (cp_torus_power g (1+z))"
proof (cases z rule: int_cases)
  case (nonneg n)
  then show ?thesis by (simp add: cp_torus_power_def nat_add_distrib)
next
  case (neg n)
  have cancel: "cp_torus_equiv ((True,g) # (False,g) # replicate n (False,g))
      (replicate n (False,g))"
    using cp_torus_cancel_pair[of "(True,g)" "replicate n (False,g)"] by (simp add: inv1_def)
  have shift: "1 + - int (Suc n) = - int n" by simp
  show ?thesis using cancel unfolding neg
    by (simp only: shift cp_torus_power_neg replicate_Suc)
qed

lemma cp_torus_power_negative_step:
  "cp_torus_equiv ((False,g) # cp_torus_power g z) (cp_torus_power g (-1+z))"
proof (cases z rule: int_cases)
  case (nonneg n)
  show ?thesis
  proof (cases n)
    case 0
    with nonneg show ?thesis by (simp add: cp_torus_power_def)
  next
    case (Suc k)
    have cancel: "cp_torus_equiv ((False,g) # (True,g) # replicate k (True,g))
        (replicate k (True,g))"
      using cp_torus_cancel_pair[of "(False,g)" "replicate k (True,g)"] by (simp add: inv1_def)
    have shift: "-1 + int (Suc k) = int k" by simp
    show ?thesis using cancel unfolding nonneg Suc
      by (simp only: shift cp_torus_power_nonneg replicate_Suc)
  qed
next
  case (neg n)
  have shift: "-1 + - int (Suc n) = - int (Suc (Suc n))" by simp
  show ?thesis unfolding neg
    by (simp only: shift cp_torus_power_neg replicate_Suc cp_torus_refl)
qed

lemma cp_torus_power_step:
  "cp_torus_equiv ((d,g) # cp_torus_power g z)
    (cp_torus_power g ((if d then 1 else -1) + z))"
  by (cases d)
    (simp_all only: if_True if_False cp_torus_power_positive_step cp_torus_power_negative_step)

lemma cp_torus_commute_power:
  "cp_torus_equiv ((e,Torus_B) # cp_torus_power Torus_A m)
    (cp_torus_power Torus_A m @ [(e,Torus_B)])"
  by (simp add: cp_torus_power_def cp_torus_commute_replicate split: if_splits)

definition cp_torus_canonical :: "int \<times> int \<Rightarrow> cp_torus_generator word_g_i" where
  "cp_torus_canonical z = cp_torus_power Torus_A (fst z) @ cp_torus_power Torus_B (snd z)"

definition cp_torus_normalize ::
  "cp_torus_generator word_g_i \<Rightarrow> cp_torus_generator word_g_i" where
  "cp_torus_normalize w = cp_torus_canonical (cp_torus_exponents w)"

lemma cp_torus_prepend_canonical:
  "cp_torus_equiv (l # cp_torus_canonical (m,n))
    (cp_torus_canonical (cp_torus_weight Torus_A l + m, cp_torus_weight Torus_B l + n))"
proof (cases l)
  case (Pair d g)
  show ?thesis
  proof (cases g)
    case Torus_A
    show ?thesis using cp_equiv.comp[OF cp_torus_power_step[of d Torus_A m]
      cp_torus_refl[of "cp_torus_power Torus_B n"]]
      by (simp add: Pair Torus_A cp_torus_canonical_def)
  next
    case Torus_B
    have swap: "cp_torus_equiv
      ((d,Torus_B) # (cp_torus_power Torus_A m @ cp_torus_power Torus_B n))
      (cp_torus_power Torus_A m @ ((d,Torus_B) # cp_torus_power Torus_B n))"
      using cp_equiv.comp[OF cp_torus_commute_power[of d m]
        cp_torus_refl[of "cp_torus_power Torus_B n"]] by (simp add: append_assoc)
    have step: "cp_torus_equiv
      (cp_torus_power Torus_A m @ ((d,Torus_B) # cp_torus_power Torus_B n))
      (cp_torus_power Torus_A m @ cp_torus_power Torus_B ((if d then 1 else -1) + n))"
      by (rule cp_equiv.comp[OF cp_torus_refl cp_torus_power_step])
    show ?thesis using cp_equiv.trans[OF swap step]
      by (simp add: Pair Torus_B cp_torus_canonical_def append_assoc)
  qed
qed

theorem cp_torus_normalize_sound:
  "cp_torus_equiv w (cp_torus_normalize w)"
proof (induction w)
  case Nil
  show ?case by (simp add: cp_torus_normalize_def cp_torus_canonical_def
    cp_torus_exponents_def)
next
  case (Cons l w)
  have tail: "cp_torus_equiv (l # w) (l # cp_torus_normalize w)"
    using cp_equiv.comp[OF cp_torus_refl[of "[l]"] Cons.IH] by simp
  have head: "cp_torus_equiv (l # cp_torus_normalize w) (cp_torus_normalize (l # w))"
    using cp_torus_prepend_canonical[of l "cp_torus_exponent Torus_A w"
      "cp_torus_exponent Torus_B w"]
    by (simp add: cp_torus_normalize_def cp_torus_exponents_def)
  show ?case by (rule cp_equiv.trans[OF tail head])
qed

text \<open>Unlike the empty-presentation decision theorem, this theorem has an
  active named equation.  Completeness follows from the normalization proof,
  not from assuming that exponent pairs characterize the presentation.\<close>

theorem cp_torus_equiv_iff_exponents:
  "cp_torus_equiv u v \<longleftrightarrow> cp_torus_exponents u = cp_torus_exponents v"
proof
  show "cp_torus_equiv u v \<Longrightarrow> cp_torus_exponents u = cp_torus_exponents v"
    by (rule cp_torus_exponents_invariant)
next
  assume "cp_torus_exponents u = cp_torus_exponents v"
  then have "cp_torus_normalize u = cp_torus_normalize v"
    by (simp add: cp_torus_normalize_def)
  then have "cp_torus_equiv u (cp_torus_normalize v)"
    using cp_torus_normalize_sound[of u] by simp
  then show "cp_torus_equiv u v"
    by (rule cp_equiv.trans[OF _ cp_equiv.sym[OF cp_torus_normalize_sound]])
qed

lemma cp_torus_exponent_replicate [simp]:
  "cp_torus_exponent g (replicate n l) = int n * cp_torus_weight g l"
  by (induction n) (simp_all add: algebra_simps)

lemma cp_torus_exponent_power [simp]:
  "cp_torus_exponent g (cp_torus_power h z) = (if h = g then z else 0)"
proof (cases z rule: int_cases)
  case (nonneg n)
  show ?thesis unfolding nonneg
    by (simp only: cp_torus_power_nonneg cp_torus_exponent_replicate cp_torus_weight.simps;
      simp split: if_splits)
next
  case (neg n)
  show ?thesis unfolding neg
    by (simp only: cp_torus_power_neg cp_torus_exponent_replicate cp_torus_weight.simps;
      simp split: if_splits)
qed

lemma cp_torus_exponents_canonical [simp]:
  "cp_torus_exponents (cp_torus_canonical z) = z"
  by (cases z) (simp add: cp_torus_exponents_def cp_torus_canonical_def)

theorem cp_torus_canonical_unique:
  "cp_torus_equiv w (cp_torus_canonical z) \<longleftrightarrow> cp_torus_exponents w = z"
  by (simp add: cp_torus_equiv_iff_exponents)

corollary cp_torus_normal_form_exists_unique:
  "\<exists>!z. cp_torus_equiv w (cp_torus_canonical z)"
  by (simp add: cp_torus_canonical_unique)

lemma cp_torus_normalize_canonical [simp]:
  "cp_torus_normalize (cp_torus_canonical z) = cp_torus_canonical z"
  by (simp add: cp_torus_normalize_def)

lemma cp_torus_normalize_idempotent [simp]:
  "cp_torus_normalize (cp_torus_normalize w) = cp_torus_normalize w"
  by (simp add: cp_torus_normalize_def)

theorem cp_torus_normalize_complete:
  "cp_torus_equiv u v \<longleftrightarrow> cp_torus_normalize u = cp_torus_normalize v"
proof
  assume "cp_torus_equiv u v"
  then show "cp_torus_normalize u = cp_torus_normalize v"
    by (simp add: cp_torus_equiv_iff_exponents cp_torus_normalize_def)
next
  assume "cp_torus_normalize u = cp_torus_normalize v"
  then have "cp_torus_exponents u = cp_torus_exponents v"
    by (metis cp_torus_exponents_canonical cp_torus_normalize_def)
  then show "cp_torus_equiv u v" by (simp add: cp_torus_equiv_iff_exponents)
qed

lemma cp_torus_words_commute:
  "cp_torus_equiv (u @ v) (v @ u)"
  by (simp add: cp_torus_equiv_iff_exponents cp_torus_exponents_def add.commute)

lemma cp_torus_canonical_product:
  "cp_torus_equiv (cp_torus_canonical (m,n) @ cp_torus_canonical (p,q))
    (cp_torus_canonical (m+p,n+q))"
  by (simp add: cp_torus_equiv_iff_exponents cp_torus_canonical_def cp_torus_exponents_def)

lemma cp_torus_canonical_inverse:
  "cp_torus_equiv (inv_fg (cp_torus_canonical (m,n))) (cp_torus_canonical (-m,-n))"
  by (simp add: cp_torus_equiv_iff_exponents cp_torus_canonical_def cp_torus_exponents_def)

subsection \<open>Executable decision and boundary examples\<close>

definition cp_torus_decide ::
    "cp_torus_generator word_g_i \<Rightarrow> cp_torus_generator word_g_i \<Rightarrow> bool" where
  "cp_torus_decide u v = (cp_torus_exponents u = cp_torus_exponents v)"

theorem cp_torus_decide_correct:
  "cp_torus_decide u v \<longleftrightarrow> cp_torus_equiv u v"
  by (simp add: cp_torus_decide_def cp_torus_equiv_iff_exponents)

lemma cp_torus_relation_not_structural:
  "\<not> cp_word_eq [(True,Torus_A),(True,Torus_B)] [(True,Torus_B),(True,Torus_A)]"
  by (simp add: cp_reduce_complete canceling_def)

lemma cp_torus_generators_distinct:
  "\<not> cp_torus_equiv [(True,Torus_A)] [(True,Torus_B)]"
  by (simp add: cp_torus_equiv_iff_exponents cp_torus_exponents_def)

lemma cp_torus_commutator_trivial:
  "cp_torus_equiv [(True,Torus_A),(True,Torus_B),(False,Torus_A),(False,Torus_B)] []"
  by (simp add: cp_torus_equiv_iff_exponents cp_torus_exponents_def)

lemma cp_torus_mixed_signed_example:
  "cp_torus_normalize
    [(False,Torus_B),(True,Torus_A),(True,Torus_B),
      (False,Torus_A),(False,Torus_A),(False,Torus_B)]
    = [(False,Torus_A),(False,Torus_B)]"
  by (simp add: cp_torus_normalize_def cp_torus_exponents_def
    cp_torus_canonical_def cp_torus_power_def)

subsection \<open>Complete decision for binary torus witnesses\<close>

text \<open>The named tree equation below is independent syntax.  The general
  tree-presentation correspondence then transfers the complete invariant to
  binary witnesses with arbitrary parentheses, inverses, and identities.\<close>

definition cp_torus_tree_relations :: "(unit, cp_torus_generator) cp_tree_relations" where
  "cp_torus_tree_relations = {((), CP_Comp (CP_Gen Torus_A) (CP_Gen Torus_B),
    CP_Comp (CP_Gen Torus_B) (CP_Gen Torus_A), ())}"

abbreviation cp_torus_tree_equiv ::
    "(unit,cp_torus_generator) cp_tree \<Rightarrow> (unit,cp_torus_generator) cp_tree \<Rightarrow> bool" where
  "cp_torus_tree_equiv p q \<equiv> cp_tree_presented
    cp_torus_vertex cp_torus_vertex cp_torus_tree_relations () p q ()"

lemma cp_torus_tree_typed [simp]: "cp_typed cp_torus_vertex cp_torus_vertex p a b"
  by (induction p) (auto intro: cp_typed.intros)

lemma cp_torus_flat_relations [simp]:
  "cp_flat_relations cp_torus_vertex cp_torus_vertex cp_torus_tree_relations
    = cp_torus_relations"
  by (auto simp: cp_flat_relations_def cp_torus_tree_relations_def cp_torus_relations_def)

theorem cp_torus_tree_equiv_iff_exponents:
  "cp_torus_tree_equiv p q \<longleftrightarrow> cp_torus_exponents (cp_flat p) = cp_torus_exponents (cp_flat q)"
  by (simp add: cp_tree_presented_complete cp_torus_equiv_iff_exponents)

definition cp_torus_tree_normalize ::
    "(unit,cp_torus_generator) cp_tree \<Rightarrow> (unit,cp_torus_generator) cp_tree" where
  "cp_torus_tree_normalize p = cp_quote cp_torus_vertex cp_torus_vertex ()
    (cp_torus_normalize (cp_flat p))"

lemma cp_torus_tree_normalize_flat [simp]:
  "cp_flat (cp_torus_tree_normalize p) = cp_torus_normalize (cp_flat p)"
  by (simp add: cp_torus_tree_normalize_def)

theorem cp_torus_tree_normalize_sound:
  "cp_torus_tree_equiv p (cp_torus_tree_normalize p)"
  by (simp add: cp_torus_tree_equiv_iff_exponents cp_torus_normalize_def)

lemma cp_torus_tree_normalize_idempotent [simp]:
  "cp_torus_tree_normalize (cp_torus_tree_normalize p) = cp_torus_tree_normalize p"
  by (simp add: cp_torus_tree_normalize_def)

theorem cp_torus_tree_normalize_complete:
  "cp_torus_tree_equiv p q \<longleftrightarrow> cp_torus_tree_normalize p = cp_torus_tree_normalize q"
proof
  assume "cp_torus_tree_equiv p q"
  then have "cp_torus_normalize (cp_flat p) = cp_torus_normalize (cp_flat q)"
    by (simp add: cp_torus_tree_equiv_iff_exponents cp_torus_normalize_def)
  then show "cp_torus_tree_normalize p = cp_torus_tree_normalize q"
    by (simp add: cp_torus_tree_normalize_def)
next
  assume "cp_torus_tree_normalize p = cp_torus_tree_normalize q"
  then have "cp_torus_normalize (cp_flat p) = cp_torus_normalize (cp_flat q)"
    by (metis cp_torus_tree_normalize_flat)
  then show "cp_torus_tree_equiv p q"
    by (simp add: cp_torus_tree_equiv_iff_exponents
      cp_torus_normalize_complete[symmetric] cp_torus_equiv_iff_exponents)
qed

definition cp_torus_tree_decide ::
    "(unit,cp_torus_generator) cp_tree \<Rightarrow> (unit,cp_torus_generator) cp_tree \<Rightarrow> bool" where
  "cp_torus_tree_decide p q = cp_torus_decide (cp_flat p) (cp_flat q)"

theorem cp_torus_tree_decide_correct:
  "cp_torus_tree_decide p q \<longleftrightarrow> cp_torus_tree_equiv p q"
  by (simp add: cp_torus_tree_decide_def cp_torus_decide_def cp_torus_tree_equiv_iff_exponents)

export_code cp_torus_exponents cp_torus_normalize cp_torus_decide
  cp_torus_tree_normalize cp_torus_tree_decide checking SML

end
