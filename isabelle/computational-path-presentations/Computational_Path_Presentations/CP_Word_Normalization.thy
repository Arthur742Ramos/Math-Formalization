section \<open>Executable refinement of AFP free-word normalization\<close>

theory CP_Word_Normalization
  imports "Free-Groups.FreeGroups"
begin

text \<open>The cancellation relation, its confluence and its unique normal form
  are those of Breitner's AFP entry Free Groups.  The recursive function below
  refines that existing normal form; the free-group results are not claimed as
  new.  A Boolean sign and a generator form a letter.  Endpoint constraints
  are imposed by the subsequent theory, not by the untyped cancellation core.\<close>

fun cp_push :: "'g g_i \<Rightarrow> 'g word_g_i \<Rightarrow> 'g word_g_i" where
  "cp_push x [] = [x]"
| "cp_push x (y # ys) = (if canceling x y then ys else x # y # ys)"

fun cp_reduce :: "'g word_g_i \<Rightarrow> 'g word_g_i" where
  "cp_reduce [] = []"
| "cp_reduce (x # xs) = cp_push x (cp_reduce xs)"

lemma cp_canceled_consI:
  assumes "canceled (y # ys)" "\<not> canceling x y"
  shows "canceled (x # y # ys)"
proof (unfold canceled_def, rule notI)
  assume "Domainp cancels_to_1 (x # y # ys)"
  then obtain z where "cancels_to_1 (x # y # ys) z" by blast
  then obtain p a b q where eq: "x # y # ys = p @ a # b # q"
    and ab: "canceling a b" by (auto elim: cancels_to_1_unfold)
  show False
  proof (cases p)
    case Nil
    with eq ab assms(2) show False by simp
  next
    case (Cons h t)
    with eq have "y # ys = t @ a # b # q" by simp
    with ab have "cancels_to_1 (y # ys) (t @ q)"
      using cancels_to_1_fold by metis
    with assms(1) show False by (auto simp: canceled_def)
  qed
qed

lemma cp_push_canceled:
  "canceled xs \<Longrightarrow> canceled (cp_push x xs)"
  by (cases xs) (auto intro: cp_canceled_consI dest: cons_canceled)

lemma cp_push_sound: "cancels_to (x # xs) (cp_push x xs)"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  have "canceling x y \<Longrightarrow> cancels_to_1 (x # y # ys) ys"
    using cancels_to_1_fold[of x y "[]" ys] by simp
  with Cons show ?thesis by (auto simp: cancels_to_def)
qed

lemma cp_reduce_canceled [simp]: "canceled (cp_reduce xs)"
  by (induction xs) (auto intro: cp_push_canceled)

lemma cp_reduce_sound: "cancels_to xs (cp_reduce xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "cancels_to (x # xs) (x # cp_reduce xs)"
    using cancel_to_append[OF Cons.IH, of "[x]" "[]"] by simp
  also have "cancels_to (x # cp_reduce xs) (cp_push x (cp_reduce xs))"
    by (rule cp_push_sound)
  finally show ?case by simp
qed

theorem cp_reduce_eq_normalize: "cp_reduce xs = normalize xs"
  by (rule HOL.sym, rule normalize_discover) (simp_all add: cp_reduce_sound)

lemma cp_reduce_idempotent [simp]: "cp_reduce (cp_reduce xs) = cp_reduce xs"
  by (simp add: cp_reduce_eq_normalize)

subsection \<open>Free structural equality\<close>

inductive cp_word_eq :: "'g word_g_i \<Rightarrow> 'g word_g_i \<Rightarrow> bool" where
  refl: "cp_word_eq x x"
| cancel: "cancels_to_1 x y \<Longrightarrow> cp_word_eq x y"
| sym: "cp_word_eq x y \<Longrightarrow> cp_word_eq y x"
| trans: "cp_word_eq x y \<Longrightarrow> cp_word_eq y z \<Longrightarrow> cp_word_eq x z"

lemma cp_cancels_word_eq:
  "cancels_to x y \<Longrightarrow> cp_word_eq x y"
  unfolding cancels_to_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule cp_word_eq.refl)
next
  case (step y z)
  from step.hyps(2) have "cp_word_eq y z" by (rule cp_word_eq.cancel)
  with step.IH show ?case by (rule cp_word_eq.trans)
qed

lemma cp_word_eq_normalize:
  "cp_word_eq x y \<Longrightarrow> normalize x = normalize y"
proof (induction rule: cp_word_eq.induct)
  case (cancel x y)
  then have "cancels_to x y" by (auto simp: cancels_to_def)
  then show ?case by simp
qed auto

theorem cp_word_eq_iff_normalize:
  "cp_word_eq x y \<longleftrightarrow> normalize x = normalize y"
proof
  show "cp_word_eq x y \<Longrightarrow> normalize x = normalize y"
    by (rule cp_word_eq_normalize)
next
  assume eq: "normalize x = normalize y"
  have "cp_word_eq x (normalize x)" "cp_word_eq y (normalize y)"
    by (auto intro: cp_cancels_word_eq)
  then have "cp_word_eq x (normalize y)" "cp_word_eq (normalize y) y"
    using eq cp_word_eq.sym by auto
  then show "cp_word_eq x y" by (rule cp_word_eq.trans)
qed

theorem cp_reduce_complete:
  "cp_word_eq x y \<longleftrightarrow> cp_reduce x = cp_reduce y"
  by (simp add: cp_word_eq_iff_normalize cp_reduce_eq_normalize)

lemma cp_word_eq_append:
  assumes "cp_word_eq x x'" "cp_word_eq y y'"
  shows "cp_word_eq (x @ y) (x' @ y')"
proof -
  have "normalize (x @ y) = normalize (normalize x @ normalize y)"
    by (rule normalize_append_cancel_to) simp_all
  also have "\<dots> = normalize (normalize x' @ normalize y')"
    using cp_word_eq_normalize[OF assms(1)] cp_word_eq_normalize[OF assms(2)] by simp
  also have "\<dots> = normalize (x' @ y')"
    by (rule HOL.sym, rule normalize_append_cancel_to) simp_all
  finally show ?thesis by (simp add: cp_word_eq_iff_normalize)
qed

lemma cp_reduce_append:
  "cp_reduce (x @ y) = cp_reduce (cp_reduce x @ cp_reduce y)"
  unfolding cp_reduce_eq_normalize
  by (rule normalize_append_cancel_to) simp_all

subsection \<open>Inversion\<close>

lemma cp_inv1_involution [simp]: "inv1 (inv1 x) = x"
  by (cases x) (simp add: inv1_def apfst_def)

lemma cp_inv_fg_Nil [simp]: "inv_fg [] = []"
  by (simp add: inv_fg_def)

lemma cp_inv_fg_append [simp]: "inv_fg (x @ y) = inv_fg y @ inv_fg x"
  by (simp add: inv_fg_def)

lemma cp_inv_fg_cons [simp]: "inv_fg (x # xs) = inv_fg xs @ [inv1 x]"
  by (simp add: inv_fg_def)

lemma cp_cancels_inverse_step:
  assumes "cancels_to_1 x y"
  shows "cancels_to_1 (inv_fg x) (inv_fg y)"
proof -
  from assms obtain p a b q where
    x: "x = p @ a # b # q" and y: "y = p @ q" and ab: "canceling a b"
    by (rule cancels_to_1_unfold)
  have "canceling (inv1 b) (inv1 a)" using ab cancel_sym by simp
  then have "cancels_to_1 (inv_fg q @ inv1 b # inv1 a # inv_fg p)
      (inv_fg q @ inv_fg p)" by (rule cancels_to_1_fold)
  then show ?thesis by (simp add: x y)
qed

lemma cp_cancels_inverse:
  "cancels_to x y \<Longrightarrow> cancels_to (inv_fg x) (inv_fg y)"
  unfolding cancels_to_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from step.hyps(2) have "cancels_to_1 (inv_fg y) (inv_fg z)"
    by (rule cp_cancels_inverse_step)
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma cp_normalize_inverse:
  "normalize (inv_fg x) = inv_fg (normalize x)"
  by (rule normalize_discover)
    (auto intro: inv_fg_closure1 cp_cancels_inverse)

lemma cp_reduce_inverse:
  "cp_reduce (inv_fg x) = inv_fg (cp_reduce x)"
  by (simp add: cp_reduce_eq_normalize cp_normalize_inverse)

lemma cp_word_eq_inverse:
  "cp_word_eq x y \<Longrightarrow> cp_word_eq (inv_fg x) (inv_fg y)"
  by (simp add: cp_word_eq_iff_normalize cp_normalize_inverse)

lemma cp_word_eq_inverse_right [simp]: "cp_word_eq (x @ inv_fg x) []"
  by (simp add: cp_word_eq_iff_normalize inv_fg_cancel)

lemma cp_word_eq_inverse_left [simp]: "cp_word_eq (inv_fg x @ x) []"
  by (simp add: cp_word_eq_iff_normalize inv_fg_cancel2)


theorem cp_reduction_diamond:
  assumes "cancels_to x y" "cancels_to x z"
  shows "cancels_to y (cp_reduce x) \<and> cancels_to z (cp_reduce x)"
proof
  show "cancels_to y (cp_reduce x)"
    using normalize_canceled[OF assms(1)] by (simp add: cp_reduce_eq_normalize)
  show "cancels_to z (cp_reduce x)"
    using normalize_canceled[OF assms(2)] by (simp add: cp_reduce_eq_normalize)
qed

subsection \<open>Substitution by signed words\<close>

definition cp_code_letter :: "('g \<Rightarrow> 'h word_g_i) \<Rightarrow> 'g g_i \<Rightarrow> 'h word_g_i" where
  "cp_code_letter F l = (if fst l then F (snd l) else inv_fg (F (snd l)))"

definition cp_word_code :: "('g \<Rightarrow> 'h word_g_i) \<Rightarrow> 'g word_g_i \<Rightarrow> 'h word_g_i" where
  "cp_word_code F w = concat (map (cp_code_letter F) w)"

lemma cp_word_code_Nil [simp]: "cp_word_code F [] = []"
  by (simp add: cp_word_code_def)

lemma cp_word_code_Cons [simp]:
  "cp_word_code F (x # xs) = cp_code_letter F x @ cp_word_code F xs"
  by (simp add: cp_word_code_def)

lemma cp_word_code_append [simp]:
  "cp_word_code F (x @ y) = cp_word_code F x @ cp_word_code F y"
  by (simp add: cp_word_code_def)

lemma cp_code_letter_inverse [simp]:
  "cp_code_letter F (inv1 x) = inv_fg (cp_code_letter F x)"
  by (simp add: cp_code_letter_def inv1_def apfst_def inv_idemp)

lemma cp_word_code_inverse [simp]:
  "cp_word_code F (inv_fg x) = inv_fg (cp_word_code F x)"
  by (induction x) simp_all

lemma cp_word_eq_context:
  "cp_word_eq x y \<Longrightarrow> cp_word_eq (p @ x @ q) (p @ y @ q)"
  by (intro cp_word_eq_append cp_word_eq.refl)

lemma cp_canceling_inv1:
  "canceling a b \<Longrightarrow> b = inv1 a"
  by (auto simp: canceling_def inv1_def apfst_def prod_eq_iff)

lemma cp_word_code_cancel:
  assumes "cancels_to_1 x y"
  shows "cp_word_eq (cp_word_code F x) (cp_word_code F y)"
proof -
  from assms obtain p a b q where
    x: "x = p @ a # b # q" and y: "y = p @ q" and ab: "canceling a b"
    by (rule cancels_to_1_unfold)
  from ab have b: "b = inv1 a" by (rule cp_canceling_inv1)
  have "cp_word_eq (cp_code_letter F a @ cp_code_letter F b) []"
    by (simp add: b)
  then have "cp_word_eq
    (cp_word_code F p @ (cp_code_letter F a @ cp_code_letter F b) @ cp_word_code F q)
    (cp_word_code F p @ [] @ cp_word_code F q)"
    by (rule cp_word_eq_context)
  then show ?thesis by (simp add: x y append_assoc)
qed

theorem cp_word_code_cong:
  "cp_word_eq x y \<Longrightarrow> cp_word_eq (cp_word_code F x) (cp_word_code F y)"
proof (induction rule: cp_word_eq.induct)
  case (refl x)
  show ?case by (rule cp_word_eq.refl)
next
  case (cancel x y)
  then show ?case by (rule cp_word_code_cancel)
next
  case (sym x y)
  from sym.IH show ?case by (rule cp_word_eq.sym)
next
  case (trans x y z)
  from trans.IH show ?case by (rule cp_word_eq.trans)
qed

end
