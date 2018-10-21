(*  Title:      HOL/Algebra/Multiplicative_Group_Revised.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Multiplicative_Group_Revised
  imports Cycles Generated_Groups Polynomials

begin

section \<open>Multiplicative Group\<close>

subsection \<open>Definitions\<close>

definition l_mult :: "_ \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("l'_mult\<index>")
  where "l_mult\<^bsub>G\<^esub> a = (\<lambda>b. if b \<in> carrier G then a \<otimes>\<^bsub>G\<^esub> b else b)"

definition ord :: "_ \<Rightarrow> 'a \<Rightarrow> nat"
  where "ord G a = least_power (l_mult\<^bsub>G\<^esub> a) \<one>\<^bsub>G\<^esub>"


subsection \<open>Basic Properties\<close>

lemma (in monoid) l_mult_one:
  shows "a \<in> carrier G \<Longrightarrow> (l_mult a) \<one> = a" and "(l_mult \<one>) a = a"
  unfolding l_mult_def by auto 

lemma (in monoid) l_mult_mult:
  assumes "a \<in> carrier G" and "b \<in> carrier G" shows "(l_mult a) \<circ> (l_mult b) = (l_mult (a \<otimes> b))"
  using assms unfolding l_mult_def by (auto simp add: m_assoc)

lemma (in group) l_mult_inv:
  assumes "a \<in> carrier G" shows "((l_mult a) \<circ> (l_mult (inv a))) b = b"
  using assms l_mult_one(2) l_mult_mult[OF _ inv_closed] by simp

lemma (in monoid) exp_of_l_mult:
  assumes "a \<in> carrier G" shows "(l_mult a) ^^ n = (l_mult (a [^]\<^bsub>G\<^esub> n))"
  using assms
proof (induct n)
  case 0 thus ?case
    unfolding l_mult_def by auto
next
  case (Suc n)
  hence "(l_mult a) ^^ Suc n = (l_mult a) \<circ> (l_mult (a [^]\<^bsub>G\<^esub> n))"
    by (simp add: funpow_swap1)
  thus ?case
    using l_mult_mult[of a "a [^]\<^bsub>G\<^esub> n"] Suc(2) nat_pow_Suc2 by auto 
qed

lemma (in group) l_mult_permutes:
  assumes "a \<in> carrier G" shows "(l_mult a) permutes (carrier G)"
proof (rule bij_imp_permutes)
  show "l_mult a b = b" if "b \<notin> carrier G" for b
    using that unfolding l_mult_def by simp
next
  show "bij_betw (l_mult a) (carrier G) (carrier G)"
  proof (rule bij_betw_byWitness[where ?f' = "l_mult (inv a)"])
    show "\<forall>b \<in> carrier G. l_mult (inv a) (l_mult a b) = b"
      using l_mult_inv[OF inv_closed[OF assms]] unfolding inv_inv[OF assms] by simp
    show "\<forall>b \<in> carrier G. l_mult a (l_mult (inv a) b) = b"
      using l_mult_inv[OF assms] by simp 
    show "l_mult a ` carrier G \<subseteq> carrier G" and "l_mult (inv a) ` carrier G \<subseteq> carrier G"
      using assms inv_closed[OF assms] unfolding l_mult_def by auto
  qed
qed

lemma (in group) l_mult_permutation:
  assumes "finite (carrier G)" and "a \<in> carrier G" shows "permutation (l_mult a)"
  using assms(1) l_mult_permutes[OF assms(2)] unfolding permutation_permutes by auto

lemma (in group) ord_pow:
  assumes "finite (carrier G)" and "a \<in> carrier G"
  shows "a [^] (ord G a) = \<one>" and "(ord G a) > 0"
  using least_power_of_permutation[OF l_mult_permutation[OF assms], of \<one>] l_mult_one(1) assms(2)
  unfolding ord_def exp_of_l_mult[OF assms(2)] by auto

lemma (in group) ord_gt_one:
  assumes "finite (carrier G)" and "a \<in> carrier G - { \<one> }" shows "(ord G a) > 1"
proof -
  have "a = \<one>" if "ord G a = 1"
    using ord_pow[OF assms(1), of a] assms(2) unfolding that by simp
  hence "ord G a \<noteq> 1"
    using assms(2) by blast
  thus ?thesis
    using ord_pow[of a] assms by simp
qed

lemma (in group) ord_minimal:
  assumes "a \<in> carrier G" and "a [^] n = \<one>" shows "(ord G a) dvd n"
  using assms(1) l_mult_one exp_of_l_mult[of a n] unfolding ord_def assms(2)
  by (simp add: least_power_minimal)

lemma (in group) ord_dvd:
  assumes "finite (carrier G)" and "a \<in> carrier G" shows "(ord G a) dvd n \<longleftrightarrow> a [^] n = \<one>"
  using assms(2) l_mult_one(1) exp_of_l_mult
  unfolding ord_def least_power_dvd[OF l_mult_permutation[OF assms(1-2)]] by simp


end