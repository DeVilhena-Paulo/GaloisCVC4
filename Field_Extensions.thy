(* ************************************************************************** *)
(* Title:      Field_Extensions.thy                                           *)
(* Author:     Martin Baillon                                                 *)
(* ************************************************************************** *)

theory Field_Extensions
  imports Embedded_Algebras Polynomials Generated_Fields "HOL-Library.Multiset" Finite_Extensions Signature

begin

locale field_extension = 
  field for K and k and p and Sp and Sx (structure)
 + assumes K : "subfield K R"
     and k : "subfield k R"
     and Sp : "\<And>x. x \<in> Sp \<Longrightarrow> split (carrier R) x"
     and Sx : "Sx \<subseteq> carrier R""\<And>x. x \<in> Sx \<Longrightarrow> (algebraic over k) x""\<And> x. x \<in> Sx \<Longrightarrow> Irr k x \<in> Sp"

lemma (in field_extension) Sp_in_univ_poly :
  shows "Sp \<subseteq> carrier (univ_poly R)" using Sp
  by (simp add: local.split_def subsetI univ_poly_def)

definition (in ring) galoisian :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "galoisian K k \<equiv> (subfield K R) \<and> (\<forall> x \<in> K. (algebraic over k) x \<and> (split K (Irr k x)))"

lemma (in ring) galoisian_self :
  assumes "subfield k R"
  shows "galoisian k k" unfolding galoisian_def split_def apply (simp add : assms, auto)
proof-
  fix x assume hyp : "x \<in> k"
  hence xR : "x \<in> carrier R" using subfieldE(3) assms by auto
  show alg : "(algebraic over k) x" using hyp algebraic_self[OF subfieldE(1)[OF assms]] by auto
  have deg : "Irr k x = [\<one>,x]" using Irr_self[OF assms hyp].
  thus poly : "polynomial R (Irr k x)"
    using subfieldE(3,6)[OF assms] hyp one_closed 
    unfolding polynomial_def by auto
  have "size (roots k (Irr k x)) \<ge> 1"
    unfolding roots_def multiplicity_def
    using \<open>polynomial R (Irr k x)\<close> deg pirreductibleE(4) pirreductible_def by fastforce
  moreover have "length (Irr k x) - Suc 0 = 1" using deg by simp
  moreover have "size (roots k (Irr k x)) \<le>  length (Irr k x) - Suc 0"
    using roots_number_inf_degree[OF assms, of "Irr k x"] IrrE'(2)[OF assms alg xR]
    by auto
  ultimately show "size (roots k (Irr k x)) = length (Irr k x) - Suc 0" by auto
qed


lemma (in field_extension) galoisian_simple_extension :
  assumes "K = simple_extension k x"
    and "(algebraic over k) x"
    and "x \<in> carrier R"
    and "split K (Irr k x) "
  shows "galoisian K k" unfolding galoisian_def split_def apply (auto simp add : K)
proof-
  fix y assume hyp : "y \<in> K"
  hence yR : "y \<in> carrier R" using subfieldE(3)[OF K] by auto
  show alg :  "(algebraic over k) y"
    using algebraic_simple_extension k assms hyp by auto
  show "polynomial R (Irr k y)" using IrrE'(2)[OF k alg] yR by auto
  show "size (roots K (Irr k y)) = length (Irr k y) - Suc 0"
  proof (cases "y = \<zero>")
    case True
    hence "y \<in> k" using k subfieldE(1) subringE(3) by auto
    then show ?thesis
      using galoisian_self[OF k] Irr_self K galoisian_def galoisian_self hyp split_def
      by force 
  next
    case False
    from hyp this simple_extension.simps[of y k x] assms(1) obtain k1 k2 
      where k1k2 : "y = k1 \<otimes> x \<oplus> k2" "k1 \<in> k" "k2 \<in> k" by auto
    then show ?thesis sorry
  qed
  from hyp


lemma (in field_extension) galoisian_finite_extension :
  assumes "K = finite_extension k xs"
    and "\<And> x. x \<in> set (xs) \<Longrightarrow>  (algebraic over k) x \<and> (split K (Irr k x)) "
  shows "galoisian K k" using assms(1) 
proof(induction xs arbitrary : K)
  case Nil
  then have "K = k"
    by simp
  then show ?case using galoisian_self k K by auto
next
  case (Cons a xs)
  hence "K = simple_extension (finite_extension k xs) a"
    by simp
    
    
  then show ?case sorry
qed


end