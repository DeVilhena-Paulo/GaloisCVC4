(* ************************************************************************** *)
(* Title:      Field_Extensions.thy                                           *)
(* Author:     Martin Baillon                                                 *)
(* ************************************************************************** *)

theory Field_Extensions
  imports Embedded_Algebras Polynomials Generated_Fields "HOL-Library.Multiset" Finite_Extensions

begin

definition (in ring) pdivides ::"'a list \<Rightarrow>'a list \<Rightarrow> bool" (infixl "pdivides" 50)
  where "p pdivides q \<equiv> (\<exists> r. r \<noteq> [] \<and> polynomial R r \<and> p = poly_mult q r)"

definition (in ring) irreductible :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "irreductible K p \<equiv> polynomial R p \<and> p \<noteq> []"

lemma (in ring) irreductibleE :
  assumes "irreductible K p"
  shows "p \<noteq> []" "polynomial R p" "degree p \<ge> 1" "set p \<subseteq> K"
        "\<And> q r. \<lbrakk>polyomial R q ; set q \<subseteq> K; polynomial R r ; set r \<subseteq> K ; p = poly_mult q r\<rbrakk> \<Longrightarrow>
                 q \<in> Units(univ_poly (R\<lparr>carrier := K\<rparr>)) \<or> r \<in> Units (univ_poly (R\<lparr>carrier := K\<rparr>))"
  sorry

lemma (in ring) Irr_exists :
  assumes "subfield K R"
    and "(algebraic over K) x"
  shows "\<exists>! p. (irreductible K p \<and> eval p x = \<zero>)"
  sorry


lemma (in ring) algebraic_self :
  assumes "subring k R"
    and "x \<in> k"
  shows "(algebraic over k) x"
  sorry


definition (in ring) Irr :: "'a set => 'a => 'a list"
  where "Irr K x \<equiv> THE p. (irreductible K p \<and> eval p x = \<zero>)"

lemma (in ring) Irr_self :
  assumes "subfield K R"
    and "x \<in> K"
  shows "Irr K x = [\<one>,x]"
  sorry

lemma (in ring) IrrE :
  assumes "subfield K R"
    and "(algebraic over K) x"
  shows "irreductible K (Irr K x)" "eval (Irr K x) x = \<zero>"
  using theI'[OF Irr_exists[OF assms]] unfolding Irr_def
  by blast+

definition (in ring) multiplicity :: "'a \<Rightarrow> nat \<Rightarrow>'a list \<Rightarrow> bool"
  where "multiplicity x n p \<equiv> ([\<one>,x][^]\<^bsub>univ_poly R\<^esub> n) pdivides p
                            \<and>\<not>(([\<one>,x][^]\<^bsub>univ_poly R\<^esub> (Suc n)) pdivides p)"

definition (in ring) roots :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a multiset"
  where "roots K p \<equiv> Abs_multiset (\<lambda>x \<in> K. (THE n. multiplicity x n p))"

lemma (in ring) roots_number_inf_degree :
  assumes "subfield K R"
    and "polynomial R p"
  shows "size (roots K p) \<le> degree p"
  sorry

definition (in ring) split :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "split K p \<equiv> polynomial R p \<and> (size (roots K p)) = degree p"

locale field_extension = 
  R?: field R
  for K :: "'a set" and k :: "'a set" and p :: "'a list" and R :: "('a, 'b) ring_scheme" (structure)
 + assumes split : "split (carrier R) p"
     and K : "subfield K R"
     and k : "subfield k R"



lemma (in ring) IrrE :
  assumes "(algebraic over K) x"
    and "x \<in> carrier R"
    and "subfield K R"
  shows "pirreductible (R\<lparr>carrier := K\<rparr>) Irr K x""eval (Irr K x)x =\<zero>""(Irr K x) \<noteq> []"
        "set (Irr K x) \<subseteq> K" "lead_coeff (Irr K x) = \<one>"
  sorry

definition (in ring) galoisian :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "galoisian K k \<equiv> (subfield K R) \<and> (\<forall> x \<in> K. (algebraic over k) x \<and> (split K (Irr k x)))"

lemma (in ring) galoisian_self :
  assumes "subfield k R"
  shows "galoisian k k" unfolding galoisian_def split_def apply (simp add : assms, auto)
proof-
  fix x assume hyp : "x \<in> k"
  thus alg : "(algebraic over k) x" using algebraic_self[OF subfieldE(1)[OF assms]] by auto
  have deg : "Irr k x = [\<one>,x]" using Irr_self[OF assms hyp].
  thus poly : "polynomial R (Irr k x)"
    using subfieldE(3,6)[OF assms] hyp one_closed 
    unfolding polynomial_def by auto
  have "size (roots k (Irr k x)) \<ge> 1"
    unfolding roots_def multiplicity_def
    using \<open>polynomial R (Irr k x)\<close> deg irreductibleE(4) irreductible_def by fastforce
  moreover have "length (Irr k x) - Suc 0 = 1" using deg by simp
  moreover have "size (roots k (Irr k x)) \<le>  length (Irr k x) - Suc 0"
    using roots_number_inf_degree[OF assms, of "Irr k x"] IrrE[OF assms alg] irreductibleE(2)
    by auto
  ultimately show "size (roots k (Irr k x)) = length (Irr k x) - Suc 0" by auto
qed


lemma (in field_extension) galoisian_finite_extension :
  assumes "K = finite_extension k xs"
    and "\<And> x. x \<in> set (xs) \<Longrightarrow>  (algebraic over k) x \<and> (split K (Irr k x)) "
  shows "galoisian K k" using assms(1) 
proof(induction xs)
  case Nil
  then have "K = k"
    by simp
  then show ?case sorry
next
  case (Cons a xs)
  then show ?case sorry
qed


end