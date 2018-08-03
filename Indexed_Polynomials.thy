theory Indexed_Polynomials
  imports Weak_Morphisms "HOL-Library.Multiset" (* Polynomials *)
    
begin

section \<open>Indexed Polynomials\<close>

text \<open>In this theory, we build a basic framework to the study of polynomials on letters
      indexed by a set. The main interest is to then apply these concepts to the construction
      of the algebraic closure of a field. \<close>


subsection \<open>Definitions\<close>

text \<open>We formalize indexed monomials as multisets with its support a subset of the index set.
      On top of those, we build indexed polynomials which are simply functions mapping a monomial
      to its coefficient. \<close>

definition (in ring) indexed_const :: "'a \<Rightarrow> ('c multiset \<Rightarrow> 'a)" 
  where "indexed_const k = (\<lambda>m. if m = {#} then k else \<zero>)"

definition (in ring) indexed_pmult :: "('c multiset \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)" (infixl "\<Otimes>" 65)
  where "indexed_pmult P i = (\<lambda>m. if i \<in># m then P (m - {# i #}) else \<zero>)"

definition (in ring) indexed_padd :: "_ \<Rightarrow> _ \<Rightarrow> ('c multiset \<Rightarrow> 'a)" (infixl "\<Oplus>" 65)
  where "indexed_padd P Q = (\<lambda>m. (P m) \<oplus> (Q m))"

definition (in ring) indexed_var :: "'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)" ("\<X>\<index>")
  where "indexed_var i = (indexed_const \<one>) \<Otimes> i"

definition (in ring) index_free :: "('c multiset \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> bool"
  where "index_free P i \<longleftrightarrow> (\<forall>m. i \<in># m \<longrightarrow> P m = \<zero>)"

definition (in ring) carrier_coeff :: "('c multiset \<Rightarrow> 'a) \<Rightarrow> bool"
  where "carrier_coeff P \<longleftrightarrow> (\<forall>m. P m \<in> carrier R)"

inductive_set (in ring) indexed_pset :: "'c set \<Rightarrow> 'a set \<Rightarrow> ('c multiset \<Rightarrow> 'a) set" ("_ [\<X>\<index>]" 80)
  for I and K where
    indexed_const:  "k \<in> K \<Longrightarrow> indexed_const k \<in> (K[\<X>\<^bsub>I\<^esub>])"
  | indexed_padd:  "\<lbrakk> P \<in> (K[\<X>\<^bsub>I\<^esub>]); Q \<in> (K[\<X>\<^bsub>I\<^esub>]) \<rbrakk> \<Longrightarrow> P \<Oplus> Q \<in> (K[\<X>\<^bsub>I\<^esub>])"
  | indexed_pmult: "\<lbrakk> P \<in> (K[\<X>\<^bsub>I\<^esub>]); i \<in> I \<rbrakk> \<Longrightarrow> P \<Otimes> i \<in> (K[\<X>\<^bsub>I\<^esub>])"

fun (in ring) indexed_eval_aux :: "('c multiset \<Rightarrow> 'a) list \<Rightarrow> 'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)"
  where "indexed_eval_aux Ps i = foldr (\<lambda>P Q. (Q \<Otimes> i) \<Oplus> P) Ps (indexed_const \<zero>)"

fun (in ring) indexed_eval :: "('c multiset \<Rightarrow> 'a) list \<Rightarrow> 'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)"
  where "indexed_eval Ps i = indexed_eval_aux (rev Ps) i"


subsection \<open>Basic Properties\<close>

lemma (in ring) carrier_coeffE:
  assumes "carrier_coeff P" shows "P m \<in> carrier R"
  using assms unfolding carrier_coeff_def by simp

lemma (in ring) indexed_zero_def: "indexed_const \<zero> = (\<lambda>_. \<zero>)"
  unfolding indexed_const_def by simp

lemma (in ring) indexed_pmult_zero [simp]:
  shows "indexed_pmult (indexed_const \<zero>) i = indexed_const \<zero>"
  unfolding indexed_zero_def indexed_pmult_def by auto

lemma (in ring) indexed_padd_zero:
  assumes "carrier_coeff P" shows "P \<Oplus> (indexed_const \<zero>) = P" and "(indexed_const \<zero>) \<Oplus> P = P"
  using assms unfolding carrier_coeff_def indexed_zero_def indexed_padd_def by auto

lemma (in ring) indexed_padd_const:
  shows "(indexed_const k1) \<Oplus> (indexed_const k2) = indexed_const (k1 \<oplus> k2)"
  unfolding indexed_padd_def indexed_const_def by auto

lemma (in ring) indexed_const_in_carrier:
  assumes "K \<subseteq> carrier R" and "k \<in> K" shows "\<And>m. (indexed_const k) m \<in> carrier R"
  using assms unfolding indexed_const_def by auto

lemma (in ring) indexed_padd_in_carrier:
  assumes "carrier_coeff P" and "carrier_coeff Q" shows "carrier_coeff (indexed_padd P Q)"
  using assms unfolding carrier_coeff_def indexed_padd_def by simp

lemma (in ring) indexed_pmult_in_carrier:
  assumes "carrier_coeff P" shows "carrier_coeff (P \<Otimes> i)"
  using assms unfolding carrier_coeff_def indexed_pmult_def by simp

lemma (in ring) indexed_eval_aux_in_carrier:
  assumes "list_all carrier_coeff Ps" shows "carrier_coeff (indexed_eval_aux Ps i)"
  using assms unfolding carrier_coeff_def
  by (induct Ps) (auto simp add: indexed_zero_def indexed_padd_def indexed_pmult_def)

lemma (in ring) indexed_eval_in_carrier:
  assumes "list_all carrier_coeff Ps" shows "carrier_coeff (indexed_eval Ps i)"
  using assms indexed_eval_aux_in_carrier[of "rev Ps"] by auto

lemma (in ring) indexed_pset_in_carrier:
  assumes "K \<subseteq> carrier R" and "P \<in> (K[\<X>\<^bsub>I\<^esub>])" shows "carrier_coeff P"
  using assms(2,1) indexed_const_in_carrier unfolding carrier_coeff_def
  by (induction) (auto simp add: indexed_zero_def indexed_padd_def indexed_pmult_def)


subsection \<open>Indexed Eval\<close>

lemma (in ring) exists_indexed_eval_aux_monomial:
  assumes "carrier_coeff P" and "list_all carrier_coeff Qs"
    and "count n i = k" and "P n \<noteq> \<zero>" and "list_all (\<lambda>Q. index_free Q i) Qs"
  obtains m where "count m i = length Qs + k" and "(indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
proof -
  from assms(2,5) have "\<exists>m. count m i = length Qs + k \<and> (indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
  proof (induct Qs)
    case Nil thus ?case
      using indexed_padd_zero(2)[OF assms(1)] assms(3-4) by auto
  next
    case (Cons Q Qs)
    then obtain m where m: "count m i = length Qs + k" "(indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
      by auto
    define m' where "m' = m + {# i #}"
    hence "Q m' = \<zero>"
      using Cons(3) unfolding index_free_def by simp
    moreover have "(indexed_eval_aux (Qs @ [ P ]) i) m \<in> carrier R"
      using indexed_eval_aux_in_carrier[of "Qs @ [ P ]" i] Cons(2) assms(1) carrier_coeffE by auto
    hence "((indexed_eval_aux (Qs @ [ P ]) i) \<Otimes> i) m' \<in> carrier R - { \<zero> }"
      using m unfolding indexed_pmult_def m'_def by simp
    ultimately have "(indexed_eval_aux (Q # (Qs @ [ P ])) i) m' \<noteq> \<zero>"
      by (auto simp add: indexed_padd_def)
    moreover from \<open>count m i = length Qs + k\<close> have "count m' i = length (Q # Qs) + k"
      unfolding m'_def by simp
    ultimately show ?case
      by auto
  qed
  thus thesis
    using that by blast
qed

lemma (in ring) indexed_eval_aux_monomial_degree_le:
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
    and "(indexed_eval_aux Ps i) m \<noteq> \<zero>" shows "count m i \<le> length Ps - 1"
  using assms(1-3)
proof (induct Ps arbitrary: m, simp add: indexed_zero_def)
  case (Cons P Ps) show ?case
  proof (cases "count m i = 0", simp)
    assume "count m i \<noteq> 0"
    hence "P m = \<zero>"
      using Cons(3) unfolding index_free_def by simp
    moreover have "(indexed_eval_aux Ps i) m \<in> carrier R"
      using indexed_eval_aux_in_carrier Cons(2) carrier_coeffE by simp
    ultimately have "((indexed_eval_aux Ps i) \<Otimes> i) m \<noteq> \<zero>"
      using Cons(4) by (auto simp add: indexed_padd_def)
    with \<open>count m i \<noteq> 0\<close> have "(indexed_eval_aux Ps i) (m - {# i #}) \<noteq> \<zero>"
      unfolding indexed_pmult_def by (auto simp del: indexed_eval_aux.simps)
    hence "count m i - 1 \<le> length Ps - 1"
      using Cons(1)[of "m - {# i #}"] Cons(2-3) by auto
    moreover from \<open>(indexed_eval_aux Ps i) (m - {# i #}) \<noteq> \<zero>\<close> have "length Ps > 0"
      by (auto simp add: indexed_zero_def)
    moreover from \<open>count m i \<noteq> 0\<close> have "count m i > 0"
      by simp
    ultimately show ?thesis
      by (simp add: Suc_leI le_diff_iff)
  qed
qed

lemma (in ring) indexed_eval_aux_is_inj:
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
      and "list_all carrier_coeff Qs" and "list_all (\<lambda>Q. index_free Q i) Qs"
    and "indexed_eval_aux Ps i = indexed_eval_aux Qs i" and "length Ps = length Qs"
  shows "Ps = Qs"
  using assms
proof (induct Ps arbitrary: Qs, simp)
  case (Cons P Ps)
  from \<open>length (P # Ps) = length Qs\<close> obtain Q' Qs' where Qs: "Qs = Q' # Qs'" and "length Ps = length Qs'"
    by (metis Suc_length_conv)

  have in_carrier:
    "((indexed_eval_aux Ps  i) \<Otimes> i) m \<in> carrier R" "P  m \<in> carrier R"
    "((indexed_eval_aux Qs' i) \<Otimes> i) m \<in> carrier R" "Q' m \<in> carrier R" for m
    using indexed_eval_aux_in_carrier[of Ps  i]
          indexed_eval_aux_in_carrier[of Qs' i] Cons(2,4) carrier_coeffE
    unfolding Qs indexed_pmult_def by auto

  have "(indexed_eval_aux (P # Ps) i) m = (indexed_eval_aux (Q' # Qs') i) m" for m
    using Cons(6) unfolding Qs by simp
  hence eq: "((indexed_eval_aux Ps i) \<Otimes> i) m \<oplus> P m = ((indexed_eval_aux Qs' i) \<Otimes> i) m \<oplus> Q' m" for m
    by (simp add: indexed_padd_def)

  have "P m = Q' m" if "i \<in># m" for m
    using that Cons(3,5) unfolding index_free_def Qs by auto
  moreover have "P m = Q' m" if "i \<notin># m" for m
    using in_carrier(2,4) eq[of m] that by (auto simp add: indexed_pmult_def)
  ultimately have "P = Q'"
    by auto

  hence "(indexed_eval_aux Ps i) m = (indexed_eval_aux Qs' i) m" for m
    using eq[of "m + {# i #}"] in_carrier[of "m + {# i #}"] unfolding indexed_pmult_def by auto
  with \<open>length Ps = length Qs'\<close> have "Ps = Qs'"
    using Cons(1)[of Qs'] Cons(2-5) unfolding Qs by auto
  with \<open>P = Q'\<close> show ?case
    unfolding Qs by simp
qed

lemma (in ring) indexed_eval_aux_is_inj':
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
      and "list_all carrier_coeff Qs" and "list_all (\<lambda>Q. index_free Q i) Qs"
      and "carrier_coeff P" and "index_free P i" "P \<noteq> indexed_const \<zero>"
      and "carrier_coeff Q" and "index_free Q i" "Q \<noteq> indexed_const \<zero>"
    and "indexed_eval_aux (Ps @ [ P ]) i = indexed_eval_aux (Qs @ [ Q ]) i"
  shows "Ps = Qs" and "P = Q"
proof -
  obtain m n where "P m \<noteq> \<zero>" and "Q n \<noteq> \<zero>"
    using assms(7,10) unfolding indexed_zero_def by blast
  hence "count m i = 0" and "count n i = 0"
    using assms(6,9) unfolding index_free_def by (meson count_inI)+ 
  with \<open>P m \<noteq> \<zero>\<close> and \<open>Q n \<noteq> \<zero>\<close> obtain m' n'
    where m': "count m' i = length Ps" "(indexed_eval_aux (Ps @ [ P ]) i) m' \<noteq> \<zero>"
      and n': "count n' i = length Qs" "(indexed_eval_aux (Qs @ [ Q ]) i) n' \<noteq> \<zero>"
    using exists_indexed_eval_aux_monomial[of P Ps m i 0]
          exists_indexed_eval_aux_monomial[of Q Qs n i 0] assms(1-5,8)
    by (metis (no_types, lifting) add.right_neutral)
  have "(indexed_eval_aux (Qs @ [ Q ]) i) m' \<noteq> \<zero>"
    using m'(2) assms(11) by simp
  with \<open>count m' i = length Ps\<close> have "length Ps \<le> length Qs"
    using indexed_eval_aux_monomial_degree_le[of "Qs @ [ Q ]" i m'] assms(3-4,8-9) by auto
  moreover have "(indexed_eval_aux (Ps @ [ P ]) i) n' \<noteq> \<zero>"
    using n'(2) assms(11) by simp
  with \<open>count n' i = length Qs\<close> have "length Qs \<le> length Ps"
    using indexed_eval_aux_monomial_degree_le[of "Ps @ [ P ]" i n'] assms(1-2,5-6) by auto
  ultimately have same_len: "length (Ps @ [ P ]) = length (Qs @ [ Q ])"
    by simp
  thus "Ps = Qs" and "P = Q"
    using indexed_eval_aux_is_inj[of "Ps @ [ P ]" i "Qs @ [ Q ]"] assms(1-6,8-9,11) by auto
qed

lemma (in ring) indexed_eval_is_inj:
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
      and "list_all carrier_coeff Qs" and "list_all (\<lambda>Q. index_free Q i) Qs"
      and "carrier_coeff P" and "index_free P i" "P \<noteq> indexed_const \<zero>"
      and "carrier_coeff Q" and "index_free Q i" "Q \<noteq> indexed_const \<zero>"
    and "indexed_eval (P # Ps) i = indexed_eval (Q # Qs) i"
  shows "Ps = Qs" and "P = Q"
proof -
  have rev_cond:
    "list_all carrier_coeff (rev Ps)" "list_all (\<lambda>P. index_free P i) (rev Ps)"
    "list_all carrier_coeff (rev Qs)" "list_all (\<lambda>Q. index_free Q i) (rev Qs)"
    using assms(1-4) by auto
  show "Ps = Qs" and "P = Q"
    using indexed_eval_aux_is_inj'[OF rev_cond assms(5-10)] assms(11) by auto
qed

(*lemma (in ring) indexed_pset_empty:
  shows "K[\<X>\<^bsub>{}\<^esub>] = (\<Union>k \<in> K. { indexed_const k })"
  using indexed_pset.simps *)

(*
subsection \<open>Definitions\<close>

definition (in ring) indexed_const :: "'a \<Rightarrow> (('b \<Rightarrow> nat) \<Rightarrow> 'a)" 
  where "indexed_const k = (\<lambda>m. if m = (\<lambda>_. 0) then k else \<zero>)"

definition indexed_pmult :: "(('b \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> (('b \<Rightarrow> nat) \<Rightarrow> 'a)"
  where "indexed_pmult P i = (\<lambda>m. P (\<lambda>j. if i = j then (m i) - 1 else (m j)))"

definition (in ring) indexed_padd :: "(('b \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> (('b \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> (('b \<Rightarrow> nat) \<Rightarrow> 'a)"
  where "indexed_padd P Q = (\<lambda>m. (P m) \<oplus> (Q m))"

definition (in ring) index_free :: "(('b \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
  where "index_free P i \<longleftrightarrow> (\<forall>m. m i > 0 \<longrightarrow> P m = \<zero>)"

(*
definition (in ring) index_free_list :: "(('b \<Rightarrow> nat) \<Rightarrow> 'a) list \<Rightarrow> 'b \<Rightarrow> bool"
  where "index_free_list Ps i \<longleftrightarrow> (\<forall>P \<in> set Ps. index_free P i)"
*)

inductive_set (in ring) indexed_pset :: "'a set \<Rightarrow> 'b set \<Rightarrow> (('b \<Rightarrow> nat) \<Rightarrow> 'a) set"
  for K and I where
    indexed_zero: "indexed_const \<zero> \<in> indexed_pset K I"
  | indexed_padd: "\<lbrakk> P \<in> indexed_pset K I; i \<in> I; k \<in> K \<rbrakk> \<Longrightarrow>
                 indexed_padd (indexed_pmult P i) (indexed_const k) \<in> indexed_pset K I"

fun (in ring) indexed_eval_aux :: "(('b \<Rightarrow> nat) \<Rightarrow> 'a) list \<Rightarrow> 'b \<Rightarrow> (('b \<Rightarrow> nat) \<Rightarrow> 'a)"
  where "indexed_eval_aux Ps i = foldr (\<lambda>k Q. indexed_padd (indexed_pmult Q i) k) Ps (indexed_const \<zero>)"

fun (in ring) indexed_eval :: "(('b \<Rightarrow> nat) \<Rightarrow> 'a) list \<Rightarrow> 'b \<Rightarrow> (('b \<Rightarrow> nat) \<Rightarrow> 'a)"
  where "indexed_eval Ps i = indexed_eval_aux (rev Ps) i"


subsection \<open>Basic Properties\<close>

lemma (in ring) indexed_zero_def: "indexed_const \<zero> = (\<lambda>_. \<zero>)"
  unfolding indexed_const_def by simp

lemma (in ring) indexed_pmult_zero [simp]:
  shows "indexed_pmult (indexed_const \<zero>) i = indexed_const \<zero>"
  unfolding indexed_zero_def indexed_pmult_def ..

lemma (in ring) indexed_padd_zero:
  assumes "\<And>m. P m \<in> carrier R" shows "indexed_padd P (indexed_const \<zero>) = P" and "indexed_padd (indexed_const \<zero>) P = P"
  using assms unfolding indexed_zero_def indexed_padd_def by auto

lemma (in ring) indexed_const_in_carrier:
  assumes "K \<subseteq> carrier R" and "k \<in> K" shows "\<And>m. (indexed_const k) m \<in> carrier R"
  using assms unfolding indexed_const_def by auto

lemma (in ring) indexed_padd_in_carrier:
  assumes "\<And>m. P m \<in> carrier R" and "\<And>m. Q m \<in> carrier R" shows "\<And>m. (indexed_padd P Q) m \<in> carrier R"
  using assms unfolding indexed_padd_def by simp

lemma (in ring) indexed_pmult_in_carrier:
  assumes "\<And>m. P m \<in> carrier R" shows "\<And>m. (indexed_pmult P i) m \<in> carrier R"
  using assms unfolding indexed_pmult_def by simp

lemma (in ring) indexed_eval_aux_in_carrier:
  assumes "\<And>m P. P \<in> set Ps \<Longrightarrow> P m \<in> carrier R" shows "\<And>m. (indexed_eval_aux Ps i) m \<in> carrier R"
  using assms by (induct Ps) (auto simp add: indexed_zero_def indexed_padd_def indexed_pmult_def)

lemma (in ring) indexed_eval_in_carrier:
  assumes "\<And>m P. P \<in> set Ps \<Longrightarrow> P m \<in> carrier R" shows "\<And>m. (indexed_eval Ps i) m \<in> carrier R"
  using assms indexed_eval_aux_in_carrier[of "rev Ps"] by auto

lemma (in ring) indexed_pset_in_carrier:
  assumes "K \<subseteq> carrier R" and "P \<in> indexed_pset K I" shows "\<And>m. P m \<in> carrier R"
  using assms(2,1) indexed_const_in_carrier
  by (induction) (auto simp add: indexed_zero_def indexed_padd_def indexed_pmult_def)

lemma (in ring) indexed_pset_empty:
  shows "indexed_pset K {} = { indexed_const \<zero> }"
  using indexed_pset.simps by auto

lemma (in ring) indexed_const_incl:
  assumes "K \<subseteq> carrier R" and "k \<in> K" and "I \<noteq> {}" shows "indexed_const k \<in> indexed_pset K I"
proof -
  from \<open>I \<noteq> {}\<close> obtain i where "i \<in> I"
    by blast
  hence "indexed_padd (indexed_const \<zero>) (indexed_const k) \<in> indexed_pset K I"
    using indexed_padd[OF indexed_zero _ assms(2)] by simp
  thus ?thesis
    using indexed_padd_zero(2)[OF indexed_const_in_carrier[OF assms(1-2)]] by simp
qed

lemma (in ring)
  assumes "\<And>m. P m \<in> carrier R" and "\<And>m Q. Q \<in> set Qs \<Longrightarrow> Q m \<in> carrier R"
    and "n i = k" and "P n \<noteq> \<zero>" and "\<And>Q. Q \<in> set Qs \<Longrightarrow> index_free Q i"
  obtains m where "m i = length Qs + k" and "(indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
proof -
  from assms(2,5) have "\<exists>m. m i = length Qs + k \<and> (indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
  proof (induct Qs)
    case Nil thus ?case
      using indexed_padd_zero(2)[OF assms(1)] assms(3-4) by auto
  next
    case (Cons Q Qs)
    then obtain m where m: "m i = length Qs + k" "indexed_eval_aux (Qs @ [ P ]) i m \<noteq> \<zero>"
      by auto
    define m' where "m' = (\<lambda>j. if j = i then Suc (length Qs + k) else m j)"
    hence "m = (\<lambda>j. if i = j then m' i - 1 else m' j)"
      using m(1) by auto
    moreover have "indexed_eval_aux (Qs @ [ P ]) i m \<in> carrier R"
      using indexed_eval_aux_in_carrier[of "Qs @ [ P ]" i m] Cons(2) assms(1) by auto
    ultimately have "(indexed_pmult (indexed_eval_aux (Qs @ [ P ]) i) i) m' \<in> carrier R - { \<zero> }"
      using m unfolding indexed_pmult_def by simp
    moreover have "Q m' = \<zero>"
      using Cons(3) unfolding index_free_def m'_def by auto
    ultimately have "indexed_eval_aux (Q # (Qs @ [ P ])) i m' \<noteq> \<zero>"
      by (auto simp add: indexed_padd_def)
    moreover from \<open>m i = length Qs + k\<close> have "m' i = length (Q # Qs) + k"
      unfolding m'_def by simp
    ultimately show ?case by auto
  qed
  thus thesis
    using that by blast
qed

lemma (in ring) indexed_eval_aux_is_inj:
  assumes "\<And>P. P \<in> set Ps \<Longrightarrow> index_free P i" and "\<And>Q. Q \<in> set Qs \<Longrightarrow> index_free Q i"
    and "indexed_eval_aux Ps i = indexed_eval_aux Qs i" and "length Ps \<ge> length Qs"
  shows "Ps = (replicate (length Ps - length Qs) (indexed_const \<zero>)) @ Qs"
  using assms
proof (induct Ps arbitrary: Qs, simp)
  case (Cons P Ps)
  then show ?case 
qed


*)

end