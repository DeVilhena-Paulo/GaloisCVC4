(*  Title:      HOL/Algebra/Finite_Extensions.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Finite_Extensions
  imports Embedded_Algebras More_Polynomials Polynomial_Divisibility
    
begin

section \<open>Finite Extensions\<close>

subsection \<open>Definitions\<close>

definition (in ring) transcendental :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "transcendental K x \<longleftrightarrow> inj_on (\<lambda>p. eval p x) (carrier (K[X]))"

abbreviation (in ring) algebraic :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "algebraic K x \<equiv> \<not> transcendental K x"

definition (in ring) Irr :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "Irr K x = (THE p. p \<in> carrier (K[X]) \<and> pirreducible K p \<and> eval p x = \<zero> \<and> lead_coeff p = \<one>)"

inductive_set (in ring) simple_extension :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  for K and x where
    zero: "\<zero> \<in> simple_extension K x" |
    lin:  "\<lbrakk> k1 \<in> K; k2 \<in> K \<rbrakk> \<Longrightarrow> (k1 \<otimes> x) \<oplus> k2 \<in> simple_extension K x"

fun (in ring) finite_extension :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a set"
  where "finite_extension K xs = foldr (\<lambda>x K'. simple_extension K' x) xs K"


subsection \<open>Basic Properties\<close>

lemma (in ring) eval_transcendental:
  assumes "(transcendental over K) x" "p \<in> carrier (K[X])" "eval p x = \<zero>" shows "p = []"
proof -
  have "[] \<in> carrier (K[X])" and "eval [] x = \<zero>"
    by (auto simp add: univ_poly_def)
  thus ?thesis
    using assms unfolding over_def transcendental_def inj_on_def by auto
qed

lemma (in ring) transcendental_imp_trivial_ker:
  shows "(transcendental over K) x \<Longrightarrow> a_kernel (K[X]) R (\<lambda>p. eval p x) = { [] }"
  using eval_transcendental unfolding a_kernel_def' by (auto simp add: univ_poly_def)

lemma (in ring) non_trivial_ker_imp_algebraic:
  shows "a_kernel (K[X]) R (\<lambda>p. eval p x) \<noteq> { [] } \<Longrightarrow> (algebraic over K) x"
  using transcendental_imp_trivial_ker unfolding over_def by auto

lemma (in domain) trivial_ker_imp_transcendental:
  assumes "subring K R" and "x \<in> carrier R"
  shows "a_kernel (K[X]) R (\<lambda>p. eval p x) = { [] } \<Longrightarrow> (transcendental over K) x"
  using ring_hom_ring.trivial_ker_imp_inj[OF eval_ring_hom[OF assms]]
  unfolding transcendental_def over_def by (simp add: univ_poly_zero)

lemma (in domain) algebraic_imp_non_trivial_ker:
  assumes "subring K R" and "x \<in> carrier R"
  shows "(algebraic over K) x \<Longrightarrow> a_kernel (K[X]) R (\<lambda>p. eval p x) \<noteq> { [] }"
  using trivial_ker_imp_transcendental[OF assms] unfolding over_def by auto

lemma (in domain) zero_is_algebraic:
  assumes "subring K R" shows "(algebraic over K) \<zero>"
proof -
  have non_trivial_eval: "[ \<one>, \<zero> ] \<in> carrier (K[X])" "eval [ \<one>, \<zero> ] \<zero> = \<zero>"
    by (auto simp add: univ_poly_def polynomial_def subringE(2-3)[OF assms])
  show ?thesis
    using eval_transcendental[OF _ non_trivial_eval] unfolding over_def by auto
qed

lemma (in domain) ker_diff_carrier:
  assumes "subring K R" and "x \<in> carrier R"
  shows "a_kernel (K[X]) R (\<lambda>p. eval p x) \<noteq> carrier (K[X])"
proof (rule ccontr)

(*
lemma (in ring) transcendental_imp_trivial_ker:
  assumes "x \<in> carrier R"
  shows "(transcendental over K) x \<Longrightarrow> (\<And>p. \<lbrakk> polynomial R p; set p \<subseteq> K \<rbrakk> \<Longrightarrow> eval p x = \<zero> \<Longrightarrow> p = [])"
proof -
  fix p assume "(transcendental over K) x" "polynomial R p" "eval p x = \<zero>" "set p \<subseteq> K"
  moreover have "eval [] x = \<zero>" and "polynomial R []"
    using assms zero_is_polynomial by auto
  ultimately show "p = []"
    unfolding over_def transcendental_def inj_on_def by auto
qed

lemma (in domain) trivial_ker_imp_transcendental:
  assumes "subring K R" and "x \<in> carrier R"
  shows "(\<And>p. \<lbrakk> polynomial R p; set p \<subseteq> K \<rbrakk> \<Longrightarrow> eval p x = \<zero> \<Longrightarrow> p = []) \<Longrightarrow> (transcendental over K) x"
proof -
  assume "\<And>p. \<lbrakk> polynomial R p; set p \<subseteq> K \<rbrakk> \<Longrightarrow> eval p x = \<zero> \<Longrightarrow> p = []"
  hence "a_kernel (univ_poly (R \<lparr> carrier := K \<rparr>)) R (\<lambda>p. local.eval p x) = { [] }"
    unfolding a_kernel_def' univ_poly_subring_def'[OF assms(1)] by auto
  moreover have "[] = \<zero>\<^bsub>(univ_poly (R \<lparr> carrier := K \<rparr>))\<^esub>"
    unfolding univ_poly_def by auto
  ultimately have "inj_on (\<lambda>p. local.eval p x) (carrier (univ_poly (R \<lparr> carrier := K \<rparr>)))"
    using ring_hom_ring.trivial_ker_imp_inj[OF eval_ring_hom[OF assms]] by auto
  thus "(transcendental over K) x"
    unfolding over_def transcendental_def univ_poly_subring_def'[OF assms(1)] by simp
qed

lemma (in ring) non_trivial_ker_imp_algebraic:
  assumes "x \<in> carrier R"
    and "p \<noteq> []" "polynomial R p" "set p \<subseteq> K" "eval p x = \<zero>"
  shows "(algebraic over K) x"
  using transcendental_imp_trivial_ker[OF assms(1) _ assms(3-5)] assms(2)
  unfolding over_def algebraic_def by auto

lemma (in domain) algebraic_imp_non_trivial_ker:
  assumes "subring K R" "x \<in> carrier R"
  shows "(algebraic over K) x \<Longrightarrow> (\<exists>p \<noteq> []. polynomial R p \<and> set p \<subseteq> K \<and> eval p x = \<zero>)"
  using trivial_ker_imp_transcendental[OF assms]
  unfolding over_def algebraic_def by auto

lemma (in domain) algebraic_iff:
  assumes "subring K R" "x \<in> carrier R"
  shows "(algebraic over K) x \<longleftrightarrow> (\<exists>p \<noteq> []. polynomial R p \<and> set p \<subseteq> K \<and> eval p x = \<zero>)"
  using non_trivial_ker_imp_algebraic[OF assms(2)] algebraic_imp_non_trivial_ker[OF assms] by auto
*)

(*
proof -
  define P :: "'a list \<Rightarrow> bool"
    where "P = (\<lambda>p. p \<noteq> [] \<and> pirreducible K p \<and>
                    set p \<subseteq> K \<and> eval p x = \<zero> \<and> lead_coeff p = \<one>)"

  obtain q
    where "polynomial (R \<lparr> carrier := K \<rparr>) q"
    and "pirreducible K q"
    and "a_kernel (univ_poly (R \<lparr> carrier := K \<rparr>)) (R \<lparr> carrier := K \<rparr>) (\<lambda>p. eval p x) =
         PIdl\<^bsub>(univ_poly (R \<lparr> carrier := K \<rparr>))\<^esub> q"
    using field.exists_ker_generator_pirreducible[OF subfield_iff(2)[OF assms(1)]]

  hence "Irr K x = (THE p. P p)"
    unfolding Irr_def P_def by auto
  moreover have p: "P p" sorry
  moreover have "\<And>q. P q \<Longrightarrow> p = q" sorry
*)
(*
  ultimately have "Irr K x = p"
    by (metis the_equality)
  thus "Irr K x \<noteq> []"
    and "pirreducible (R \<lparr> carrier := K \<rparr>) (Irr K x)"
    and "set (Irr K x) \<subseteq> K"
    and "eval (Irr K x) x = \<zero>"
    and "lead_coeff (Irr K x) = \<one>"
    using p unfolding P_def by auto
*)


(*
lemma (in domain) Irr_exists:
  assumes "subring K R" "x \<in> carrier R"
*)

lemma (in domain) Irr_is_polynomial:
  assumes "subring K R" "x \<in> carrier R"
  shows "polynomial R (Irr K x)"
  sorry
(*
lemma (in field)
  assumes "subfield K R"
  shows "subfield (simple_extension K x) R \<longleftrightarrow> (algebraic over K) x"
  sorry

*)
end