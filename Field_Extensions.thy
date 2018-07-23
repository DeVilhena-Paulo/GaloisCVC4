(* ************************************************************************** *)
(* Title:      Field_Extensions.thy                                           *)
(* Author:     Martin Baillon                                                 *)
(* ************************************************************************** *)

theory Field_Extensions
  imports Embedded_Algebras Polynomials Generated_Fields "HOL-Library.Multiset" Finite_Extensions Signature

begin

locale field_extension = 
  field for K and k and p and Sx (structure)
 + assumes K : "subfield K R"
     and k : "subfield k R"
     and Sx : "Sx \<subseteq> carrier R""\<And>x. x \<in> Sx \<Longrightarrow> (algebraic over k) x"
              "\<And> x. x \<in> Sx \<Longrightarrow> split (carrier R) (Irr k x)"

definition (in ring) galoisian :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "galoisian K k \<equiv> (subfield K R) \<and> (\<forall> x \<in> K. (algebraic over k) x \<and> (split K (Irr k x)))"

lemma (in ring) galoisian_self :
  assumes "subfield k R"
  shows "galoisian k k" unfolding galoisian_def split_def apply (simp add : assms, auto)
proof-
  fix x assume hyp : "x \<in> k"
  hence xR : "x \<in> carrier R" using subfieldE(3) assms by auto
  show alg : "(algebraic over k) x" using hyp algebraic_self[OF subfieldE(1)[OF assms]] by auto
  have deg : "Irr k x = [\<one>, \<ominus> x]" using Irr_self[OF assms hyp].
  thus poly : "polynomial k (Irr k x)"
    using subfieldE(3,6)[OF assms] hyp one_closed
    unfolding polynomial_def by (simp add: assms)
  hence poly2 : "polynomial\<^bsub>R\<lparr>carrier := k\<rparr>\<^esub> k (Irr k x)""Irr k x \<noteq> []""set (Irr k x ) \<subseteq> k"
    using univ_poly_carrier[of _ k "Irr k x"] univ_poly_consistent[OF subfieldE(1)[OF assms]]
      apply (simp add: \<open>\<And>R. polynomial\<^bsub>R\<^esub> k (Irr k x)=(Irr k x\<in>carrier (k [X]\<^bsub>R\<^esub>))\<close>)
    using subringE(3,5)[OF subfieldE(1)[OF assms]] hyp by (auto simp add : deg)
  have sub :"subfield k (R\<lparr>carrier := k\<rparr>)"
    using field.carrier_is_subfield[OF subfield_iff(2)[OF assms]] by auto
  from field.roots_well_defined(2)[OF subfield_iff(2)[OF assms] this poly2(1,2)]
  have multi : "(\<lambda>xa \<in> k. (THE n. multiplicity k xa n (Irr k x))) \<in> multiset"
    using multiplicity_consistent[OF subfieldE(1)[OF assms] poly2(3) poly] by simp
  have "subring k (R\<lparr>carrier := k\<rparr>)"
    using ring.carrier_is_subring[of "(R\<lparr>carrier := k\<rparr>)"] subfield_iff(2)[OF assms] fieldE(1)
    unfolding cring_def by auto
  hence mon : "monoid (k[X])"
    using domain.univ_poly_is_monoid[of "(R\<lparr>carrier := k\<rparr>)"k] subfield_iff(2)[OF assms]
    unfolding field_def using univ_poly_consistent[OF subfieldE(1)[OF assms]] by auto
  hence div : "[\<one>, \<ominus> x]divides\<^bsub>k [X]\<^esub> Irr k x"
    using  monoid.divides_refl[of "k[X]" "Irr k x"] poly deg univ_poly_carrier[of R k]
    by simp
  moreover have "([\<one>, \<ominus> x] \<in> carrier (k [X]))"
    using poly deg univ_poly_carrier[of R k "Irr k x"] by auto 
  from monoid.l_one[OF mon this] have pow : "[\<one>, \<ominus> x][^]\<^bsub>k [X]\<^esub> (1 :: nat) = [\<one>, \<ominus> x]"
    using monoid.nat_pow_0[OF mon, of "[\<one>, \<ominus> x]"]
    by (simp add : monoid.nat_pow_Suc[OF mon, of "[\<one>, \<ominus> x]" 0])
  have "size (roots k (Irr k x)) \<ge> 1"
  proof (rule ccontr)
    assume hyp2 : "\<not> 1 \<le> size (roots k (Irr k x))"
    hence "0 = size (roots k (Irr k x))" by linarith
    hence "(roots k (Irr k x)) = {#} " by simp
    hence "count (roots k (Irr k x)) x = 0" by simp
    moreover have "count (roots k (Irr k x)) =  (\<lambda>xa\<in>k. THE n. multiplicity k xa n (Irr k x))"
      using multi Abs_multiset_inverse unfolding roots_def  by blast
    ultimately have " (\<lambda>xa\<in>k. THE n. multiplicity k xa n (Irr k x)) x = 0"
      unfolding roots_def by auto
    hence "(THE n. multiplicity k x n (Irr k x)) =(0 :: nat)"
      unfolding multiplicity_def using hyp by auto
    hence "multiplicity k x 0 (Irr k x)"
      using field.roots_well_defined(1)[OF subfield_iff(2)[OF assms]sub poly2(1,2)hyp] theI'
      multiplicity_consistent[OF subfieldE(1)[OF assms] poly2(3) poly, of x] by metis
    hence "\<not> [\<one>, \<ominus> x] [^]\<^bsub>k [X]\<^esub> Suc 0 divides\<^bsub>k [X]\<^esub> Irr k x"
      unfolding multiplicity_def by auto
    thus False using div One_nat_def pow by metis
  qed
  moreover have "length (Irr k x) - Suc 0 = 1" using deg by simp
  moreover have "size (roots k (Irr k x)) \<le>  length (Irr k x) - Suc 0"
    using roots_number_inf_degree[OF assms, of "Irr k x"] IrrE'(2)[OF assms alg xR] deg
    by auto
  ultimately show "size (roots k (Irr k x)) = length (Irr k x) - Suc 0" by auto
qed

lemma (in field_extension) galoisian_trans :
  assumes "galoisian I k"
    and "galoisian K I"
  shows "galoisian K k"
  sorry

lemma (in field_extension) galoisian_simple_extension :
  assumes "K = simple_extension k x"
    and "x \<in> Sx"
    and "split K (Irr k x)"
  shows "galoisian K k" unfolding galoisian_def split_def apply (auto simp add : K)
proof-
  fix y assume hyp : "y \<in> K"
  hence yR : "y \<in> carrier R" using subfieldE(3)[OF K] by auto
  show alg :  "(algebraic over k) y"
    using algebraic_simple_extension[OF k Sx(2)[OF assms(2)]] k assms hyp Sx(1)
    by auto
  show "polynomial K (Irr k y)"
    using IrrE'(2)[OF k alg yR] simple_extension_incl[OF k, of x] assms Sx(1)
    unfolding polynomial_def by auto
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
      where k1k2 : "y = k1 \<otimes> x \<oplus> k2" "k1 \<in> K" "k2 \<in> k" by auto
    hence k1k2K : "k1 \<in> K" "k2 \<in> K"
      using simple_extension_incl[OF k, of x] assms Sx by auto
    hence "split K (Irr K (k1 \<otimes> x))"
      using split_mult_trans[OF K _ k1k2K(1)] assms Sx simple_extension_incl[OF k]
            split_Irr_incl_trans[OF K, of _ k] by auto
    hence "split K (Irr K (k1 \<otimes> x \<oplus> k2))"
      using split_add_trans[OF K _ k1k2K(2), of "k1 \<otimes> x"] k1k2(2) subfieldE(3)[OF k] assms Sx         
      by (meson simple_extension_in_carrier subsetCE m_closed)
    hence "split K (Irr k (k1 \<otimes> x \<oplus> k2))"
      using split_Irr_incl_trans[OF K, of "k1 \<otimes> x \<oplus> k2"] assms(1,2) Sx simple_extension_incl[OF k]
      using alg k1k2(1) yR by blast
    thus ?thesis unfolding split_def using k1k2 by auto
  qed
qed

lemma (in field_extension) galoisian_finite_extension :
  assumes "K = finite_extension k xs"
    and "set xs \<subseteq> Sx"
  shows "galoisian K k" using assms(1,2) K
proof(induction xs arbitrary : K)
  case Nil
  then have "K = k"
    by simp
  then show ?case using galoisian_self k K by auto
next
  case (Cons a xs)
  hence "K = simple_extension (finite_extension k xs) a"
    by simp
  moreover have "galoisian (finite_extension k xs) k"
    using Cons finite_extension_field[OF k, of xs] Sx(1,2)
    by (smt insert_subset list.simps(15) set_mp subset_code(1))
  moreover have "field_extension R K (finite_extension k xs) Sx"
    unfolding field_extension_def field_extension_axioms_def
    apply (auto simp del : finite_extension.simps simp add :field_axioms Cons(4) Sx(1))
  proof-
    show sub : "subfield (finite_extension k xs) R"
      using calculation(2) galoisian_def by auto
    fix x assume hyp : "x \<in> Sx"
    show alg : "(algebraic over finite_extension k xs) x"
      using algebraic_finite_extension_trans[OF k, of xs x] hyp Cons(3) Sx(1,2)
      by (simp add: subset_iff)
    have "split (carrier R) (Irr (carrier R) x)"
      using split_Irr_incl_trans[of "carrier R" x k] hyp Sx carrier_is_subfield subfieldE(3)[OF k]
      by auto
    thus "split (carrier R) (Irr (finite_extension k xs) x)"
      using split_Irr_incl_trans[OF carrier_is_subfield,of x] hyp Sx Cons(3) alg sub by auto
  qed
  ultimately show "galoisian K k"
    using field_extension.galoisian_simple_extension[of R K "finite_extension k xs" Sx a] Cons
          galoisian_trans[of "finite_extension k xs"]
    
    
  then show ?case sorry
qed


end