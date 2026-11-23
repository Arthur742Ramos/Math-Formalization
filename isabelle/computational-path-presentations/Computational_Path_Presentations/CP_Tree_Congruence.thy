section \<open>Independent equations for binary path witnesses\<close>

theory CP_Tree_Congruence
  imports CP_Presentations
begin

text \<open>This is an equational presentation of the structural groupoid laws.
  Its generators do not refer to flattened words or their normal forms.  The
  correspondence with word cancellation is proved below, not stipulated by the
  definition.  No termination claim for an oriented tree rewrite system is
  made.\<close>

inductive cp_tree_eq :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow>
    'v \<Rightarrow> ('v,'g) cp_tree \<Rightarrow> ('v,'g) cp_tree \<Rightarrow> 'v \<Rightarrow> bool"
  for s t where
  refl: "cp_typed s t p a b \<Longrightarrow> cp_tree_eq s t a p p b"
| sym: "cp_tree_eq s t a p q b \<Longrightarrow> cp_tree_eq s t a q p b"
| trans: "cp_tree_eq s t a p q b \<Longrightarrow> cp_tree_eq s t a q r b \<Longrightarrow>
    cp_tree_eq s t a p r b"
| comp: "cp_tree_eq s t a p p' b \<Longrightarrow> cp_tree_eq s t b q q' c \<Longrightarrow>
    cp_tree_eq s t a (CP_Comp p q) (CP_Comp p' q') c"
| inverse: "cp_tree_eq s t a p q b \<Longrightarrow>
    cp_tree_eq s t b (CP_Inv p) (CP_Inv q) a"
| inverse_identity: "cp_tree_eq s t a (CP_Inv (CP_Id a)) (CP_Id a) a"
| inverse_inverse: "cp_typed s t p a b \<Longrightarrow>
    cp_tree_eq s t a (CP_Inv (CP_Inv p)) p b"
| left_unit: "cp_typed s t p a b \<Longrightarrow>
    cp_tree_eq s t a (CP_Comp (CP_Id a) p) p b"
| right_unit: "cp_typed s t p a b \<Longrightarrow>
    cp_tree_eq s t a (CP_Comp p (CP_Id b)) p b"
| right_inverse: "cp_typed s t p a b \<Longrightarrow>
    cp_tree_eq s t a (CP_Comp p (CP_Inv p)) (CP_Id a) a"
| left_inverse: "cp_typed s t p a b \<Longrightarrow>
    cp_tree_eq s t b (CP_Comp (CP_Inv p) p) (CP_Id b) b"
| inverse_comp: "cp_typed s t p a b \<Longrightarrow> cp_typed s t q b c \<Longrightarrow>
    cp_tree_eq s t c (CP_Inv (CP_Comp p q)) (CP_Comp (CP_Inv q) (CP_Inv p)) a"
| assoc: "cp_typed s t p a b \<Longrightarrow> cp_typed s t q b c \<Longrightarrow>
    cp_typed s t r c d \<Longrightarrow>
    cp_tree_eq s t a (CP_Comp (CP_Comp p q) r) (CP_Comp p (CP_Comp q r)) d"

lemma cp_tree_eq_typed:
  "cp_tree_eq s t a p q b \<Longrightarrow> cp_typed s t p a b \<and> cp_typed s t q a b"
  by (induction rule: cp_tree_eq.induct) (auto intro: cp_typed.intros)

theorem cp_tree_eq_sound:
  "cp_tree_eq s t a p q b \<Longrightarrow> cp_word_eq (cp_flat p) (cp_flat q)"
  by (induction rule: cp_tree_eq.induct)
    (auto simp: inv_idemp cp_word_eq.refl intro: cp_word_eq.sym cp_word_eq.trans
      cp_word_eq_append cp_word_eq_inverse)

lemma cp_tree_eq_quote_append:
  assumes u: "cp_path s t a u b" and v: "cp_path s t b v c"
  shows "cp_tree_eq s t a (CP_Comp (cp_quote s t a u) (cp_quote s t b v))
    (cp_quote s t a (u @ v)) c"
  using u
proof (induction u arbitrary: a)
  case Nil
  with cp_tree_eq.left_unit[OF cp_quote_typed[OF v]] show ?case by simp
next
  case (Cons l u)
  have a: "a = cp_source s t l" and u: "cp_path s t (cp_target s t l) u b"
    using Cons.prems by auto
  have first: "cp_tree_eq s t a
      (CP_Comp (CP_Comp (cp_letter_tree l) (cp_quote s t (cp_target s t l) u))
        (cp_quote s t b v))
      (CP_Comp (cp_letter_tree l)
        (CP_Comp (cp_quote s t (cp_target s t l) u) (cp_quote s t b v))) c"
    unfolding a by (rule cp_tree_eq.assoc)
      (auto intro: cp_letter_tree_typed cp_quote_typed[OF u] cp_quote_typed[OF v])
  have second: "cp_tree_eq s t a
      (CP_Comp (cp_letter_tree l)
        (CP_Comp (cp_quote s t (cp_target s t l) u) (cp_quote s t b v)))
      (CP_Comp (cp_letter_tree l) (cp_quote s t (cp_target s t l) (u @ v))) c"
    unfolding a by (rule cp_tree_eq.comp)
      (auto intro: cp_tree_eq.refl cp_letter_tree_typed Cons.IH[OF u])
  from cp_tree_eq.trans[OF first second] show ?case by simp
qed

lemma cp_tree_eq_quote_letter:
  "cp_tree_eq s t (cp_source s t l) (cp_letter_tree l)
    (cp_quote s t (cp_source s t l) [l]) (cp_target s t l)"
  using cp_tree_eq.sym[OF cp_tree_eq.right_unit[OF cp_letter_tree_typed[of s t l]]]
  by simp

lemma cp_tree_eq_inverse_letter:
  "cp_tree_eq s t (cp_target s t l) (CP_Inv (cp_letter_tree l))
    (cp_letter_tree (inv1 l)) (cp_source s t l)"
  by (cases l; cases "fst l")
    (auto simp: inv1_def cp_source_def cp_target_def
      intro: cp_tree_eq.refl cp_tree_eq.inverse_inverse cp_typed.intros)

lemma cp_tree_eq_quote_inverse:
  assumes path: "cp_path s t a u b"
  shows "cp_tree_eq s t b (CP_Inv (cp_quote s t a u))
    (cp_quote s t b (inv_fg u)) a"
  using path
proof (induction u arbitrary: a)
  case Nil
  then show ?case by (simp add: cp_tree_eq.inverse_identity)
next
  case (Cons l u)
  have a: "a = cp_source s t l" and u: "cp_path s t (cp_target s t l) u b"
    using Cons.prems by auto
  have quoted_letter: "cp_tree_eq s t (cp_target s t l) (cp_letter_tree (inv1 l))
      (cp_quote s t (cp_target s t l) [inv1 l]) a"
    using cp_tree_eq_quote_letter[of s t "inv1 l"] by (simp add: a)
  have inverse_letter: "cp_tree_eq s t (cp_target s t l) (CP_Inv (cp_letter_tree l))
      (cp_letter_tree (inv1 l)) a"
    using cp_tree_eq_inverse_letter[of s t l] by (simp add: a)
  have letter: "cp_tree_eq s t (cp_target s t l) (CP_Inv (cp_letter_tree l))
      (cp_quote s t (cp_target s t l) [inv1 l]) a"
    by (rule cp_tree_eq.trans[OF inverse_letter quoted_letter])
  have first: "cp_tree_eq s t b
      (CP_Inv (CP_Comp (cp_letter_tree l) (cp_quote s t (cp_target s t l) u)))
      (CP_Comp (CP_Inv (cp_quote s t (cp_target s t l) u))
        (CP_Inv (cp_letter_tree l))) a"
    unfolding a by (rule cp_tree_eq.inverse_comp)
      (auto intro: cp_letter_tree_typed cp_quote_typed[OF u])
  have second: "cp_tree_eq s t b
      (CP_Comp (CP_Inv (cp_quote s t (cp_target s t l) u))
        (CP_Inv (cp_letter_tree l)))
      (CP_Comp (cp_quote s t b (inv_fg u))
        (cp_quote s t (cp_target s t l) [inv1 l])) a"
    by (rule cp_tree_eq.comp[OF Cons.IH[OF u] letter])
  have third: "cp_tree_eq s t b
      (CP_Comp (cp_quote s t b (inv_fg u))
        (cp_quote s t (cp_target s t l) [inv1 l]))
      (cp_quote s t b (inv_fg u @ [inv1 l])) a"
    by (rule cp_tree_eq_quote_append[OF cp_path_inverse[OF u]])
      (simp add: a)
  from cp_tree_eq.trans[OF cp_tree_eq.trans[OF first second] third]
  show ?case by simp
qed

theorem cp_tree_eq_quote_flat:
  assumes "cp_typed s t p a b"
  shows "cp_tree_eq s t a p (cp_quote s t a (cp_flat p)) b"
  using assms
proof (induction rule: cp_typed.induct)
  case (identity a)
  then show ?case by (simp add: cp_tree_eq.refl cp_typed.identity)
next
  case (generator e)
  from cp_tree_eq_quote_letter[of s t "(True,e)"]
  show ?case by (simp add: cp_source_def cp_target_def)
next
  case (inverse p a b)
  from cp_tree_eq.trans[OF cp_tree_eq.inverse[OF inverse.IH]
    cp_tree_eq_quote_inverse[OF cp_flat_typed[OF inverse.hyps]]]
  show ?case by simp
next
  case (composition p a b q c)
  from cp_tree_eq.trans[OF cp_tree_eq.comp[OF composition.IH]
    cp_tree_eq_quote_append[OF cp_flat_typed[OF composition.hyps(1)]
      cp_flat_typed[OF composition.hyps(2)]]]
  show ?case by simp
qed

lemma cp_tree_eq_cancel_head:
  assumes p: "cp_typed s t p a b" and q: "cp_typed s t q a c"
  shows "cp_tree_eq s t a (CP_Comp p (CP_Comp (CP_Inv p) q)) q c"
proof -
  have first: "cp_tree_eq s t a (CP_Comp p (CP_Comp (CP_Inv p) q))
      (CP_Comp (CP_Comp p (CP_Inv p)) q) c"
    by (rule cp_tree_eq.sym[OF cp_tree_eq.assoc[OF p cp_typed.inverse[OF p] q]])
  have second: "cp_tree_eq s t a (CP_Comp (CP_Comp p (CP_Inv p)) q)
      (CP_Comp (CP_Id a) q) c"
    by (rule cp_tree_eq.comp[OF cp_tree_eq.right_inverse[OF p] cp_tree_eq.refl[OF q]])
  from cp_tree_eq.trans[OF cp_tree_eq.trans[OF first second] cp_tree_eq.left_unit[OF q]]
  show ?thesis .
qed

lemma cp_tree_eq_quote_cancel_head:
  assumes xy: "canceling x y" and path: "cp_path s t a (x # y # w) b"
  shows "cp_tree_eq s t a (cp_quote s t a (x # y # w)) (cp_quote s t a w) b"
proof -
  have y: "y = inv1 x" using xy by (rule cp_canceling_inv1)
  have a: "a = cp_source s t x" and w: "cp_path s t a w b"
    using path xy cp_canceling_endpoints[OF xy, of s t] by auto
  have letter: "cp_tree_eq s t (cp_target s t x) (cp_letter_tree y)
      (CP_Inv (cp_letter_tree x)) a"
    using cp_tree_eq.sym[OF cp_tree_eq_inverse_letter[of s t x]] by (simp add: a y)
  have inner: "cp_tree_eq s t (cp_target s t x)
      (CP_Comp (cp_letter_tree y) (cp_quote s t a w))
      (CP_Comp (CP_Inv (cp_letter_tree x)) (cp_quote s t a w)) b"
    by (rule cp_tree_eq.comp[OF letter cp_tree_eq.refl[OF cp_quote_typed[OF w]]])
  have first: "cp_tree_eq s t a
      (CP_Comp (cp_letter_tree x) (CP_Comp (cp_letter_tree y) (cp_quote s t a w)))
      (CP_Comp (cp_letter_tree x)
        (CP_Comp (CP_Inv (cp_letter_tree x)) (cp_quote s t a w))) b"
    using cp_tree_eq.comp[OF cp_tree_eq.refl[OF cp_letter_tree_typed[of s t x]] inner]
    by (simp add: a)
  have second: "cp_tree_eq s t a
      (CP_Comp (cp_letter_tree x)
        (CP_Comp (CP_Inv (cp_letter_tree x)) (cp_quote s t a w)))
      (cp_quote s t a w) b"
    unfolding a by (rule cp_tree_eq_cancel_head[OF cp_letter_tree_typed])
      (use w a in \<open>auto intro: cp_quote_typed\<close>)
  from cp_tree_eq.trans[OF first second] show ?thesis by (simp add: a y)
qed

lemma cp_tree_eq_quote_cancel_context:
  assumes xy: "canceling x y" and path: "cp_path s t a (u @ x # y # v) b"
  shows "cp_tree_eq s t a (cp_quote s t a (u @ x # y # v))
    (cp_quote s t a (u @ v)) b"
  using path
proof (induction u arbitrary: a)
  case Nil
  have path: "cp_path s t a (x # y # v) b" using Nil.prems by simp
  from cp_tree_eq_quote_cancel_head[OF xy path] show ?case by (simp only: append_Nil)
next
  case (Cons l u)
  have a: "a = cp_source s t l" and tail: "cp_path s t (cp_target s t l) (u @ x # y # v) b"
    using Cons.prems by auto
  from cp_tree_eq.comp[OF cp_tree_eq.refl[OF cp_letter_tree_typed[of s t l]]
    Cons.IH[OF tail]] show ?case by (simp add: a)
qed

lemma cp_tree_eq_quote_cancel_step:
  assumes step: "cancels_to_1 u v" and path: "cp_path s t a u b"
  shows "cp_tree_eq s t a (cp_quote s t a u) (cp_quote s t a v) b"
proof -
  from step obtain p x y q where u: "u = p @ x # y # q" and v: "v = p @ q"
    and xy: "canceling x y" by (rule cancels_to_1_unfold)
  have path': "cp_path s t a (p @ x # y # q) b" using path by (simp only: u)
  from cp_tree_eq_quote_cancel_context[OF xy path'] show ?thesis by (simp only: u v)
qed

lemma cp_tree_eq_quote_cancels:
  assumes reduction: "cancels_to u v" and path: "cp_path s t a u b"
  shows "cp_tree_eq s t a (cp_quote s t a u) (cp_quote s t a v) b"
  using reduction unfolding cancels_to_def
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule cp_tree_eq.refl[OF cp_quote_typed[OF path]])
next
  case (step v w)
  have reduction: "cancels_to u v"
    using step.hyps(1) by (simp add: cancels_to_def)
  have v: "cp_path s t a v b"
    by (rule cp_path_cancels_to[OF reduction path])
  from cp_tree_eq.trans[OF step.IH cp_tree_eq_quote_cancel_step[OF step.hyps(2) v]]
  show ?case .
qed

theorem cp_tree_eq_normalize:
  assumes "cp_typed s t p a b"
  shows "cp_tree_eq s t a p (cp_normal_tree s t a p) b"
  unfolding cp_normal_tree_def
  by (rule cp_tree_eq.trans[OF cp_tree_eq_quote_flat[OF assms]
    cp_tree_eq_quote_cancels[OF cp_reduce_sound cp_flat_typed[OF assms]]])

theorem cp_tree_eq_complete:
  assumes p: "cp_typed s t p a b" and q: "cp_typed s t q a b"
  shows "cp_tree_eq s t a p q b \<longleftrightarrow> cp_word_eq (cp_flat p) (cp_flat q)"
proof
  show "cp_tree_eq s t a p q b \<Longrightarrow> cp_word_eq (cp_flat p) (cp_flat q)"
    by (rule cp_tree_eq_sound)
next
  assume "cp_word_eq (cp_flat p) (cp_flat q)"
  then have "cp_normal_tree s t a p = cp_normal_tree s t a q"
    by (simp add: cp_normal_tree_complete)
  with cp_tree_eq_normalize[OF p] cp_tree_eq.sym[OF cp_tree_eq_normalize[OF q]]
  show "cp_tree_eq s t a p q b" by (metis cp_tree_eq.trans)
qed

corollary cp_tree_eq_decide:
  assumes "cp_typed s t p a b" "cp_typed s t q a b"
  shows "cp_tree_eq s t a p q b \<longleftrightarrow> cp_reduce (cp_flat p) = cp_reduce (cp_flat q)"
  using cp_tree_eq_complete[OF assms] by (simp add: cp_reduce_complete)

subsection \<open>Named equations between binary witnesses\<close>

type_synonym ('v,'g) cp_tree_relations =
  "('v \<times> ('v,'g) cp_tree \<times> ('v,'g) cp_tree \<times> 'v) set"

inductive cp_tree_presented :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow>
    ('v,'g) cp_tree_relations \<Rightarrow> 'v \<Rightarrow> ('v,'g) cp_tree \<Rightarrow>
    ('v,'g) cp_tree \<Rightarrow> 'v \<Rightarrow> bool"
  for s t R where
  structural: "cp_tree_eq s t a p q b \<Longrightarrow> cp_tree_presented s t R a p q b"
| named: "(a,p,q,b) \<in> R \<Longrightarrow> cp_typed s t p a b \<Longrightarrow>
    cp_typed s t q a b \<Longrightarrow> cp_tree_presented s t R a p q b"
| sym: "cp_tree_presented s t R a p q b \<Longrightarrow> cp_tree_presented s t R a q p b"
| trans: "cp_tree_presented s t R a p q b \<Longrightarrow> cp_tree_presented s t R a q r b \<Longrightarrow>
    cp_tree_presented s t R a p r b"
| comp: "cp_tree_presented s t R a p p' b \<Longrightarrow> cp_tree_presented s t R b q q' c \<Longrightarrow>
    cp_tree_presented s t R a (CP_Comp p q) (CP_Comp p' q') c"
| inverse: "cp_tree_presented s t R a p q b \<Longrightarrow>
    cp_tree_presented s t R b (CP_Inv p) (CP_Inv q) a"

definition cp_flat_relations :: "('g \<Rightarrow> 'v) \<Rightarrow> ('g \<Rightarrow> 'v) \<Rightarrow>
    ('v,'g) cp_tree_relations \<Rightarrow> ('v,'g) cp_relations" where
  "cp_flat_relations s t R = {(a, cp_flat p, cp_flat q, b) | a p q b.
    (a,p,q,b) \<in> R \<and> cp_typed s t p a b \<and> cp_typed s t q a b}"

text \<open>Only well-typed declared equations are translated.  Flattening an
  ill-typed tree can erase the offending identity vertex, so omitting these
  guards would incorrectly activate some otherwise unusable declarations.\<close>

lemma cp_tree_presented_typed:
  "cp_tree_presented s t R a p q b \<Longrightarrow> cp_typed s t p a b \<and> cp_typed s t q a b"
  by (induction rule: cp_tree_presented.induct)
    (auto dest: cp_tree_eq_typed intro: cp_typed.intros)

theorem cp_tree_presented_sound:
  "cp_tree_presented s t R a p q b \<Longrightarrow>
    cp_equiv s t (cp_flat_relations s t R) a (cp_flat p) (cp_flat q) b"
proof (induction rule: cp_tree_presented.induct)
  case (structural a p q b)
  from cp_tree_eq_typed[OF structural.hyps] cp_tree_eq_sound[OF structural.hyps]
  show ?case by (auto intro: cp_equiv.structural cp_flat_typed)
next
  case (named a p q b)
  then show ?case by (auto intro!: cp_equiv.named intro: cp_flat_typed
    simp: cp_flat_relations_def)
next
  case (sym a p q b)
  from sym.IH show ?case by (rule cp_equiv.sym)
next
  case (trans a p q b r)
  from trans.IH show ?case by (rule cp_equiv.trans)
next
  case (comp a p p' b q q' c)
  from cp_equiv.comp[OF comp.IH] show ?case by simp
next
  case (inverse a p q b)
  from cp_equiv.inverse[OF inverse.IH] show ?case by simp
qed

lemma cp_tree_presented_quote:
  assumes "cp_equiv s t (cp_flat_relations s t R) a u v b"
  shows "cp_tree_presented s t R a (cp_quote s t a u) (cp_quote s t a v) b"
  using assms
proof (induction rule: cp_equiv.induct)
  case (structural a u b v)
  have "cp_tree_eq s t a (cp_quote s t a u) (cp_quote s t a v) b"
    using cp_tree_eq_complete[OF cp_quote_typed[OF structural.hyps(1)]
      cp_quote_typed[OF structural.hyps(2)]] structural.hyps(3) by simp
  then show ?case by (rule cp_tree_presented.structural)
next
  case (named a u v b)
  then obtain p q where rel: "(a,p,q,b) \<in> R" and p: "cp_typed s t p a b"
    and q: "cp_typed s t q a b" and u: "u = cp_flat p" and v: "v = cp_flat q"
    by (auto simp: cp_flat_relations_def)
  have first: "cp_tree_presented s t R a (cp_quote s t a u) p b"
    unfolding u by (rule cp_tree_presented.structural[OF cp_tree_eq.sym[OF cp_tree_eq_quote_flat[OF p]]])
  have middle: "cp_tree_presented s t R a p q b"
    by (rule cp_tree_presented.named[OF rel p q])
  have last: "cp_tree_presented s t R a q (cp_quote s t a v) b"
    unfolding v by (rule cp_tree_presented.structural[OF cp_tree_eq_quote_flat[OF q]])
  from cp_tree_presented.trans[OF cp_tree_presented.trans[OF first middle] last] show ?case .
next
  case (sym a u v b)
  from sym.IH show ?case by (rule cp_tree_presented.sym)
next
  case (trans a u v b w)
  from trans.IH show ?case by (rule cp_tree_presented.trans)
next
  case (comp a u v b x y c)
  have u: "cp_path s t a u b" and v: "cp_path s t a v b"
    and x: "cp_path s t b x c" and y: "cp_path s t b y c"
    using comp.hyps by (auto dest: cp_equiv_typed)
  have first: "cp_tree_presented s t R a (cp_quote s t a (u @ x))
      (CP_Comp (cp_quote s t a u) (cp_quote s t b x)) c"
    by (rule cp_tree_presented.structural[OF cp_tree_eq.sym[OF cp_tree_eq_quote_append[OF u x]]])
  have middle: "cp_tree_presented s t R a
      (CP_Comp (cp_quote s t a u) (cp_quote s t b x))
      (CP_Comp (cp_quote s t a v) (cp_quote s t b y)) c"
    by (rule cp_tree_presented.comp[OF comp.IH])
  have last: "cp_tree_presented s t R a
      (CP_Comp (cp_quote s t a v) (cp_quote s t b y)) (cp_quote s t a (v @ y)) c"
    by (rule cp_tree_presented.structural[OF cp_tree_eq_quote_append[OF v y]])
  from cp_tree_presented.trans[OF cp_tree_presented.trans[OF first middle] last] show ?case .
next
  case (inverse a u v b)
  have u: "cp_path s t a u b" and v: "cp_path s t a v b"
    using inverse.hyps by (auto dest: cp_equiv_typed)
  have first: "cp_tree_presented s t R b (cp_quote s t b (inv_fg u))
      (CP_Inv (cp_quote s t a u)) a"
    by (rule cp_tree_presented.structural[OF cp_tree_eq.sym[OF cp_tree_eq_quote_inverse[OF u]]])
  have middle: "cp_tree_presented s t R b
      (CP_Inv (cp_quote s t a u)) (CP_Inv (cp_quote s t a v)) a"
    by (rule cp_tree_presented.inverse[OF inverse.IH])
  have last: "cp_tree_presented s t R b (CP_Inv (cp_quote s t a v))
      (cp_quote s t b (inv_fg v)) a"
    by (rule cp_tree_presented.structural[OF cp_tree_eq_quote_inverse[OF v]])
  from cp_tree_presented.trans[OF cp_tree_presented.trans[OF first middle] last] show ?case .
qed

theorem cp_tree_presented_complete:
  assumes p: "cp_typed s t p a b" and q: "cp_typed s t q a b"
  shows "cp_tree_presented s t R a p q b \<longleftrightarrow>
    cp_equiv s t (cp_flat_relations s t R) a (cp_flat p) (cp_flat q) b"
proof
  show "cp_tree_presented s t R a p q b \<Longrightarrow>
      cp_equiv s t (cp_flat_relations s t R) a (cp_flat p) (cp_flat q) b"
    by (rule cp_tree_presented_sound)
next
  assume eq: "cp_equiv s t (cp_flat_relations s t R) a (cp_flat p) (cp_flat q) b"
  have first: "cp_tree_presented s t R a p (cp_quote s t a (cp_flat p)) b"
    by (rule cp_tree_presented.structural[OF cp_tree_eq_quote_flat[OF p]])
  have last: "cp_tree_presented s t R a (cp_quote s t a (cp_flat q)) q b"
    by (rule cp_tree_presented.structural[OF cp_tree_eq.sym[OF cp_tree_eq_quote_flat[OF q]]])
  from cp_tree_presented.trans[OF cp_tree_presented.trans[OF first cp_tree_presented_quote[OF eq]] last]
  show "cp_tree_presented s t R a p q b" .
qed

corollary cp_tree_presented_empty:
  assumes p: "cp_typed s t p a b" and q: "cp_typed s t q a b"
  shows "cp_tree_presented s t {} a p q b \<longleftrightarrow> cp_tree_eq s t a p q b"
  using cp_tree_presented_complete[OF p q] cp_tree_eq_decide[OF p q]
  by (simp add: cp_flat_relations_def cp_empty_presentation
    cp_flat_typed[OF p] cp_flat_typed[OF q])

end
