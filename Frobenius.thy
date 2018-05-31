(* ************************************************************************** *)
(* Title:      Frobenius.thy                                                  *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Frobenius
imports Ideal Ring "HOL.Binomial" Int_Ring

begin

section \<open>Frobenius Endomorphism\<close>

subsection \<open>Binomials\<close>

text \<open>In order to study the Frobenius Endomorphim, we will only need two results from the
      theory of Binomials. Therefore, instead of porting them from HOL.Binomial, we will
      redemonstrate these lemmas inside the formalism we developed so far (more concretely,
      the one proposed by the FiniteProduct theory).\<close>

lemma (in cring) binomial:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "(a \<oplus> b) (^) n = (\<Oplus> k \<in> {.. n :: nat}. [(n choose k)] \<cdot> (a (^) k \<otimes> b (^) (n - k)))"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  let ?f   = "\<lambda>k. (a (^) k \<otimes> b (^) (n - k))"
  let ?f_a = "\<lambda>k. (a (^) Suc k \<otimes> b (^) (n - k))"
  let ?f_b = "\<lambda>k. (a (^) k \<otimes> b (^) Suc (n - k))"
  let ?choose = "\<lambda>f. \<lambda>k. [(n choose k)] \<cdot> (f k)"
  have in_carrier: "\<And>k. k \<in> {.. n :: nat} \<Longrightarrow> ?choose ?f k \<in> carrier R"
    using assms by blast 
  have "(a \<oplus> b) (^) Suc n = (a \<oplus> b) \<otimes> ((a \<oplus> b) (^) n)"
    using assms m_comm by simp
  also have " ... = (a \<oplus> b) \<otimes> (\<Oplus> k \<in> {.. n}. ?choose ?f k)"
    using Suc.hyps by simp
  also have " ... = (a \<otimes> (\<Oplus> k \<in> {.. n}. ?choose ?f k)) \<oplus> (b \<otimes> (\<Oplus> k \<in> {.. n}. ?choose ?f k))"
    using assms l_distr by simp
  also have " ... = (\<Oplus> k \<in> {.. n}. a \<otimes> (?choose ?f k)) \<oplus> (\<Oplus> k \<in> {.. n}. b \<otimes> (?choose ?f k))"
    using finsum_rdistr[of "{.. n}" a "?choose ?f"] 
          finsum_rdistr[of "{.. n}" b "?choose ?f"] assms in_carrier by simp
  also have " ... =
    (\<Oplus> k \<in> {.. n}. ?choose (\<lambda>k. a \<otimes> (?f k)) k) \<oplus> (\<Oplus> k \<in> {.. n}. ?choose (\<lambda>k. b \<otimes> (?f k)) k)"
    using add_pow_rdistr assms in_carrier by auto
  also have " ... = (\<Oplus> k \<in> {.. n}. ?choose ?f_a k) \<oplus> (\<Oplus> k \<in> {.. n}. ?choose ?f_b k)"
    using assms m_assoc m_comm by auto
  also have " ... =
    ((a (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {..<n}.     ?choose ?f_a k)) \<oplus>
    ((b (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {Suc 0..n}. ?choose ?f_b k))"
    using add.finprod_Suc3[of "\<lambda>k. ?choose ?f_a k" n]
          add.finprod_0'[of   "\<lambda>k. ?choose ?f_b k" n] assms by simp
  also have " ... =
    ((a (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {..< n}. [(n choose k)] \<cdot> (a (^) (Suc k) \<otimes> b (^) Suc (n - (Suc k))))) \<oplus>
    ((b (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {Suc 0..n}. [(n choose k)] \<cdot> (a (^) k \<otimes> (b (^) (Suc (n - k))))))"
    using Suc_diff_Suc lessThan_iff add.finprod_cong[of "{..< n}" "{..< n}"
           "\<lambda>k. [(n choose k)] \<cdot> (a (^) (Suc k) \<otimes> b (^) Suc (n - (Suc k)))"
           "\<lambda>k. [(n choose k)] \<cdot> (a (^) (Suc k) \<otimes> b (^) (n - k))"] assms by auto
  also have " ... =
    ((a (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {Suc 0..< Suc n}. [(n choose (k - Suc 0))] \<cdot> (a (^) k \<otimes> b (^) (Suc (n - k))))) \<oplus>
    ((b (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {Suc 0..n}. [(n choose k)] \<cdot> (a (^) k \<otimes> (b (^) (Suc (n - k))))))"
    using add.finprod_reindex[of "\<lambda>k. [(n choose (k - Suc 0))] \<cdot> (a (^) k \<otimes> b (^) (Suc (n - k)))"
                                 "\<lambda>i. Suc i" "{..< n}"] assms lessThan_atLeast0 atMost_atLeast0 by simp
  finally have term1: "(a \<oplus> b) (^) Suc n =
    ((a (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {Suc 0..n}. [(n choose (k - Suc 0))] \<cdot> (a (^) k \<otimes> b (^) (Suc (n - k))))) \<oplus>
    ((b (^) (Suc n)) \<oplus> (\<Oplus> k \<in> {Suc 0..n}. [(n choose k)] \<cdot> (a (^) k \<otimes> (b (^) (Suc (n - k))))))"
    using atLeastLessThanSuc_atLeastAtMost by auto

  let ?g = "\<lambda>k. a (^) k \<otimes> b (^) (Suc (n - k))"
  define sum_1 and sum_2
    where "sum_1 = (\<Oplus> k \<in> {Suc 0..n}. [(n choose (k - Suc 0))] \<cdot> ?g k)"
      and "sum_2 = (\<Oplus> k \<in> {Suc 0..n}. [(n choose k)] \<cdot> ?g k)"
  hence term2: "(a \<oplus> b) (^) Suc n = ((a (^) (Suc n)) \<oplus> sum_1) \<oplus> ((b (^) (Suc n)) \<oplus> sum_2)"
    using term1 by simp
  have sum_1_in_carrier: "sum_1 \<in> carrier R" and sum_2_in_carrier: "sum_2 \<in> carrier R"
    using assms unfolding sum_1_def sum_2_def by auto
  hence "(a \<oplus> b) (^) Suc n = (a (^) Suc n \<oplus> b (^) Suc n) \<oplus> (sum_1 \<oplus> sum_2)"
    using term2 add.m_comm add.m_assoc assms by (simp add: add.m_assoc)
  also have " ... = (a (^) Suc n \<oplus> b (^) Suc n) \<oplus>
    (\<Oplus> k \<in> {Suc 0..n}. [(n choose (k - Suc 0))] \<cdot> ?g k \<oplus> [(n choose k)] \<cdot> ?g k)"
    using add.finprod_multf[of "\<lambda>k. [(n choose (k - Suc 0))] \<cdot> ?g k" "{Suc 0..n}"
                               "\<lambda>k. [(n choose k)] \<cdot> ?g k" ] assms
    unfolding sum_1_def sum_2_def by auto
  also have "...  = (a (^) Suc n \<oplus> b (^) Suc n) \<oplus>
    (\<Oplus> k \<in> {Suc 0..n}. [((n choose (k - Suc 0)) + (n choose k))] \<cdot> ?g k)"
    using assms by (simp add: add.nat_pow_mult)
  also have " ... = (a (^) Suc n \<oplus> b (^) Suc n) \<oplus> (\<Oplus> k \<in> {Suc 0..n}. [(Suc n choose k)] \<cdot> ?g k)"
    using add.finprod_cong[of "{Suc 0..n}" "{Suc 0..n}"
                              "\<lambda>k. [((n choose (k - Suc 0)) + (n choose k))] \<cdot> ?g k"
                              "\<lambda>k. [(Suc n choose k)] \<cdot> ?g k"]
    using choose_reduce_nat assms by simp
  also have " ... = (a (^) Suc n) \<oplus> (\<Oplus> k \<in> {..n}. [(Suc n choose k)] \<cdot> ?g k)"
    using add.finprod_0'[of "\<lambda>k. [(Suc n choose k)] \<cdot> (?g k)" n] assms by (simp add: add.m_assoc)
  also have " ... = (a (^) Suc n) \<oplus> (\<Oplus> k \<in> {..n}. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) ((Suc n) - k)))"
    using add.finprod_cong[of "{..n}" "{..n}" "\<lambda>k. [(Suc n choose k)] \<cdot> ?g k"
                              "\<lambda>k. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) ((Suc n) - k))"]
          Suc_diff_le assms by auto
  also have " ... = (\<Oplus> k \<in> {..Suc n}. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) ((Suc n) - k)))"
    using add.finprod_Suc[of "\<lambda>k. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) ((Suc n) - k))" n] assms by auto 
  finally show ?case .
qed

corollary (in cring) binomial_simp:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "(a \<oplus> b) (^) (Suc n) = (a (^) Suc n) \<oplus> (b (^) Suc n) \<oplus>
           (\<Oplus> k \<in> {Suc 0.. n}. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) (Suc n - k)))" (is "_ = _ \<oplus> _ \<oplus> ?sum")
proof -
  have "(a \<oplus> b) (^) (Suc n) = (\<Oplus> k \<in> {..Suc n}. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) (Suc n - k)))"
    using binomial[OF assms, of "Suc n"] .
  also have " ... = (a (^) Suc n) \<oplus> (\<Oplus> k \<in> {..n}. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) (Suc n - k)))"
    using add.finprod_Suc assms by auto
  also have " ... = (a (^) Suc n) \<oplus> ((b (^) Suc n) \<oplus> ?sum)"
    using add.finprod_0'[of "\<lambda>k. [(Suc n choose k)] \<cdot> (a (^) k \<otimes> b (^) (Suc n - k))" n] assms by simp
  finally show ?thesis
    using add.m_assoc[of "a (^) Suc n" "b (^) Suc n"] assms by simp
qed


abbreviation prime' :: "int \<Rightarrow> bool"
  where "prime' \<equiv> Factorial_Ring.prime"

lemma prime_choose_k:
  assumes "Factorial_Ring.prime p" "k \<in> {Suc 0..< p}"
  shows "p dvd (p choose k)"
proof -
  have "fact k * fact (p - k) * (p choose k) = fact p"
    using binomial_fact_lemma assms by simp
  hence "p dvd  (fact k * fact (p - k) * (p choose k))"
    using assms(2) dvd_fact by auto
  moreover have "\<not> p dvd (fact k)" "\<not> p dvd (fact (p - k))"
    using prime_dvd_fact_iff[of p k]
          prime_dvd_fact_iff[of p "p - k"] assms by auto
  ultimately show ?thesis
    using assms(1) prime_dvd_multD by blast
qed



subsection \<open>The Morphism\<close>

definition frobenius :: " _ \<Rightarrow> 'a \<Rightarrow> 'a"
  where "frobenius R a = a (^)\<^bsub>R\<^esub> (char R)"

lemma (in cring) freshman_dream:
  assumes "Factorial_Ring.prime (char R)"
    and "a \<in> carrier R" "b \<in> carrier R"
  shows "(a \<oplus> b) (^) (char R) = (a (^) (char R)) \<oplus> (b (^) (char R))"
proof -
  obtain n :: nat where n: "char R = Suc n"
    using prime_gt_Suc_0_nat[OF assms(1)] Suc_lessE by auto
  hence "(a \<oplus> b) (^) (char R) = (a (^) (char R)) \<oplus> (b (^) (char R)) \<oplus>
           (\<Oplus> k \<in> {Suc 0.. n}. [((char R) choose k)] \<cdot> (a (^) k \<otimes> b (^) ((char R) - k)))"
    using binomial_simp[OF assms(2-3)] by simp

  moreover
  let ?f = "\<lambda>k. a (^) k \<otimes> b (^) ((char R) - k)"
  have "\<And>k. k \<in> {Suc 0.. n} \<Longrightarrow> [((char R) choose k)] \<cdot> ?f k = \<zero>"
  proof -
    fix k assume "k \<in> {Suc 0.. n}"
    hence "int (char R) dvd int ((char R) choose k)"
      using n prime_choose_k[OF assms(1)] zdvd_int by auto
    hence "\<lbrakk> (char R) choose k \<rbrakk> = \<zero>"
      using add_pow_eq_zero_iff[of "(char R) choose k"] by simp
    moreover have "[ int ((char R) choose k)] \<cdot> ?f k = \<lbrakk> (char R) choose k \<rbrakk> \<otimes> ?f k"
      using elt_of_int_def'[of "a (^) k \<otimes> b (^) ((char R) - k)"] assms(2-3) by simp
    hence "[((char R) choose k)] \<cdot> ?f k = \<lbrakk> (char R) choose k \<rbrakk> \<otimes> ?f k"
      using add.int_pow_def2 by simp
    ultimately show "[((char R) choose k)] \<cdot> ?f k = \<zero>"
      using assms(2-3) by simp
  qed
  hence "(\<Oplus> k \<in> {Suc 0.. n}. [((char R) choose k)] \<cdot> (a (^) k \<otimes> b (^) ((char R) - k))) = \<zero>"
    using add.finprod_one[of "{Suc 0.. n}"] by auto

  ultimately show ?thesis
    using assms(2-3) by simp
qed

lemma (in cring) frobenius_hom:
  assumes "Factorial_Ring.prime (char R)"
  shows "frobenius R \<in> ring_hom R R"
  unfolding frobenius_def ring_hom_def
  using freshman_dream[OF assms] nat_pow_distr by auto

end