(*  Title:      HOL/Algebra/Polynomial_Divisibility.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Polynomial_Divisibility
  imports Polynomials "HOL-Library.Multiset"
    
begin

section \<open>Divisibility of Polynomials\<close>

subsection \<open>Definitions\<close>

abbreviation poly_ring :: "_ \<Rightarrow> ('a  list) ring"
  where "poly_ring R \<equiv> univ_poly R (carrier R)"

abbreviation pirreducible :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" ("pirreducible\<index>")
  where "pirreducible\<^bsub>R\<^esub> K p \<equiv> ring_irreducible\<^bsub>(univ_poly R K)\<^esub> p"

abbreviation pprime :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" ("pprime\<index>")
  where "pprime\<^bsub>R\<^esub> K p \<equiv> ring_prime\<^bsub>(univ_poly R K)\<^esub> p"

definition pdivides :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "pdivides\<index>" 65)
  where "p pdivides\<^bsub>R\<^esub> q = p divides\<^bsub>(univ_poly R (carrier R))\<^esub> q"

definition rupture :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> (('a list) set) ring" ("Rupt\<index>")
  where "Rupt\<^bsub>R\<^esub> K p = (K[X]\<^bsub>R\<^esub>) Quot (PIdl\<^bsub>K[X]\<^bsub>R\<^esub>\<^esub> p)"

abbreviation (in ring) rupture_surj :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a list) set"
  where "rupture_surj K p \<equiv> (\<lambda>q. (PIdl\<^bsub>K[X]\<^esub> p) +>\<^bsub>K[X]\<^esub> q)"


subsection \<open>Basic Properties\<close>

lemma (in ring) carrier_polynomial_shell [intro]:
  assumes "subring K R" and "p \<in> carrier (K[X])" shows "p \<in> carrier (poly_ring R)"
  using carrier_polynomial[OF assms(1), of p] assms(2) unfolding sym[OF univ_poly_carrier] by simp

lemma (in domain) pdivides_zero:
  assumes "subring K R" and "p \<in> carrier (K[X])" shows "p pdivides []"
  using ring.divides_zero[OF univ_poly_is_ring[OF carrier_is_subring]
         carrier_polynomial_shell[OF assms]]
  unfolding univ_poly_zero pdivides_def .

lemma (in domain) zero_pdivides_zero: "[] pdivides []"
  using pdivides_zero[OF carrier_is_subring] by auto

lemma (in domain) zero_pdivides:
  shows "[] pdivides p \<longleftrightarrow> p = []"
  using ring.zero_divides[OF univ_poly_is_ring[OF carrier_is_subring]]
  unfolding univ_poly_zero pdivides_def .

lemma (in domain) pprime_iff_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])"
  shows "pprime K p \<longleftrightarrow> pirreducible K p"
  using principal_domain.primeness_condition[OF univ_poly_is_principal] assms by simp

lemma (in domain) pirreducibleE:
  assumes "subring K R" "p \<in> carrier (K[X])" "pirreducible K p"
  shows "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p = q \<otimes>\<^bsub>K[X]\<^esub> r \<Longrightarrow> q \<in> Units (K[X]) \<or> r \<in> Units (K[X])"
  using domain.ring_irreducibleE[OF univ_poly_is_domain[OF assms(1)] _ assms(3)] assms(2)
  by (auto simp add: univ_poly_zero)

lemma (in domain) pirreducibleI:
  assumes "subring K R" "p \<in> carrier (K[X])" "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p = q \<otimes>\<^bsub>K[X]\<^esub> r \<Longrightarrow> q \<in> Units (K[X]) \<or> r \<in> Units (K[X])"
  shows "pirreducible K p"
  using domain.ring_irreducibleI[OF univ_poly_is_domain[OF assms(1)] _ assms(4)] assms(2-3,5)
  by (auto simp add: univ_poly_zero)

lemma (in domain) univ_poly_carrier_units_incl:
  shows "Units ((carrier R) [X]) \<subseteq> { [ k ] | k. k \<in> carrier R - { \<zero> } }"
proof
  fix p assume "p \<in> Units ((carrier R) [X])"
  then obtain q
    where p: "polynomial (carrier R) p" and q: "polynomial (carrier R) q" and pq: "poly_mult p q = [ \<one> ]"
    unfolding Units_def univ_poly_def by auto
  hence not_nil: "p \<noteq> []" and "q \<noteq> []"
    using poly_mult_integral[OF carrier_is_subring p q] poly_mult_zero[OF polynomial_incl[OF p]] by auto
  hence "degree p = 0"
    using poly_mult_degree_eq[OF carrier_is_subring p q] unfolding pq by simp
  hence "length p = 1"
    using not_nil by (metis One_nat_def Suc_pred length_greater_0_conv)
  then obtain k where k: "p = [ k ]"
    by (metis One_nat_def length_0_conv length_Suc_conv)
  hence "k \<in> carrier R - { \<zero> }"
    using p unfolding polynomial_def by auto 
  thus "p \<in> { [ k ] | k. k \<in> carrier R - { \<zero> } }"
    unfolding k by blast
qed

lemma (in field) univ_poly_carrier_units:
  "Units ((carrier R) [X]) = { [ k ] | k. k \<in> carrier R - { \<zero> } }"
proof
  show "Units ((carrier R) [X]) \<subseteq> { [ k ] | k. k \<in> carrier R - { \<zero> } }"
    using univ_poly_carrier_units_incl by simp
next
  show "{ [ k ] | k. k \<in> carrier R - { \<zero> } } \<subseteq> Units ((carrier R) [X])"
  proof (auto)
    fix k assume k: "k \<in> carrier R" "k \<noteq> \<zero>"
    hence inv_k: "inv k \<in> carrier R" "inv k \<noteq> \<zero>" and "k \<otimes> inv k = \<one>" "inv k \<otimes> k = \<one>"
      using subfield_m_inv[OF carrier_is_subfield, of k] by auto
    hence "poly_mult [ k ] [ inv k ] = [ \<one> ]" and "poly_mult [ inv k ] [ k ] = [ \<one> ]"
      by (auto simp add: k)
    moreover have "polynomial (carrier R) [ k ]" and "polynomial (carrier R) [ inv k ]"
      using const_is_polynomial k inv_k by auto
    ultimately show "[ k ] \<in> Units ((carrier R) [X])"
      unfolding Units_def univ_poly_def by (auto simp del: poly_mult.simps)
  qed
qed

lemma (in domain) univ_poly_units_incl:
  assumes "subring K R" shows "Units (K[X]) \<subseteq> { [ k ] | k. k \<in> K - { \<zero> } }"
  using domain.univ_poly_carrier_units_incl[OF subring_is_domain[OF assms]]
        univ_poly_consistent[OF assms] by auto

lemma (in ring) univ_poly_units:
  assumes "subfield K R" shows "Units (K[X]) = { [ k ] | k. k \<in> K - { \<zero> } }"
  using field.univ_poly_carrier_units[OF subfield_iff(2)[OF assms]]
        univ_poly_consistent[OF subfieldE(1)[OF assms]] by auto

corollary (in ring) pirreducible_degree:
  assumes "subfield K R" "p \<in> carrier (K[X])" "pirreducible K p"
  shows "degree p \<ge> 1"
proof (rule ccontr)
  assume "\<not> degree p \<ge> 1" then have "length p \<le> 1"
    by simp
  moreover have "p \<noteq> []" and "p \<notin> Units (K[X])"
    using assms(3) by (auto simp add: ring_irreducible_def irreducible_def univ_poly_zero)
  ultimately obtain k where k: "p = [ k ]"
    by (metis append_butlast_last_id butlast_take diff_is_0_eq le_refl self_append_conv2 take0 take_all)
  hence "k \<in> K" and "k \<noteq> \<zero>"
    using assms(2) by (auto simp add: polynomial_def univ_poly_def)
  hence "p \<in> Units (K[X])"
    using univ_poly_units[OF assms(1)] unfolding k by auto
  from \<open>p \<in> Units (K[X])\<close> and \<open>p \<notin> Units (K[X])\<close> show False by simp
qed

corollary (in domain) univ_poly_not_field:
  assumes "subring K R" shows "\<not> field (K[X])"
proof -
  have "X \<in> carrier (K[X]) - { \<zero>\<^bsub>(K[X])\<^esub> }" and "X \<notin> { [ k ] | k. k \<in> K - { \<zero> } }"
    using var_closed(1)[OF assms] unfolding univ_poly_zero var_def by auto 
  thus ?thesis
    using field.field_Units[of "K[X]"] univ_poly_units_incl[OF assms] by blast 
qed

lemma (in domain) rupture_is_field_iff_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])"
  shows "field (Rupt K p) \<longleftrightarrow> pirreducible K p"
proof
  assume "pirreducible K p" thus "field (Rupt K p)"
    using principal_domain.field_iff_prime[OF univ_poly_is_principal[OF assms(1)]] assms(2)
          pprime_iff_pirreducible[OF assms] pirreducibleE(1)[OF subfieldE(1)[OF assms(1)]]
    by (simp add: univ_poly_zero rupture_def)
next
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  assume field: "field (Rupt K p)"
  have "p \<noteq> []"
  proof (rule ccontr)
    assume "\<not> p \<noteq> []" then have p: "p = []"
      by simp
    hence "Rupt K p \<simeq> (K[X])"
      using UP.FactRing_zeroideal(1) UP.genideal_zero
            UP.cgenideal_eq_genideal[OF UP.zero_closed]
      by (simp add: rupture_def univ_poly_zero)
    then obtain h where h: "h \<in> ring_iso (Rupt K p) (K[X])"
      unfolding is_ring_iso_def by blast
    moreover have "ring (Rupt K p)"
      using field by (simp add: cring_def domain_def field_def) 
    ultimately interpret R: ring_hom_ring "Rupt K p" "K[X]" h
      unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_iso_def
      using UP.ring_axioms by simp
    have "field (K[X])"
      using field.ring_iso_imp_img_field[OF field h] by simp
    thus False
      using univ_poly_not_field[OF subfieldE(1)[OF assms(1)]] by simp
  qed
  thus "pirreducible K p"
    using UP.field_iff_prime pprime_iff_pirreducible[OF assms] assms(2) field
    by (simp add: univ_poly_zero rupture_def)
qed

lemma (in domain) rupture_surj_hom:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "(rupture_surj K p) \<in> ring_hom (K[X]) (Rupt K p)"
    and "ring_hom_ring (K[X]) (Rupt K p) (rupture_surj K p)"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .
  interpret I: ideal "PIdl\<^bsub>K[X]\<^esub> p" "K[X]"
    using UP.cgenideal_ideal[OF assms(2)] .
  show "(rupture_surj K p) \<in> ring_hom (K[X]) (Rupt K p)"
   and "ring_hom_ring (K[X]) (Rupt K p) (rupture_surj K p)"
    using ring_hom_ring.intro[OF UP.ring_axioms I.quotient_is_ring] I.rcos_ring_hom
    unfolding symmetric[OF ring_hom_ring_axioms_def] rupture_def by auto
qed

corollary (in domain) rupture_surj_norm_is_hom:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "((rupture_surj K p) \<circ> (\<lambda>a. normalize [ a ])) \<in> ring_hom (R \<lparr> carrier := K \<rparr>) (Rupt K p)"
  using ring_hom_trans[OF canonical_embedding_is_hom[OF assms(1)] rupture_surj_hom(1)[OF assms]] .

lemma (in domain) norm_map_in_poly_ring_carrier:
  assumes "p \<in> carrier (poly_ring R)" and "\<And>a. a \<in> carrier R \<Longrightarrow> f a \<in> carrier (poly_ring R)"
  shows "ring.normalize (poly_ring R) (map f p) \<in> carrier (poly_ring (poly_ring R))"
proof -
  have "set p \<subseteq> carrier R"
    using assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence "set (map f p) \<subseteq> carrier (poly_ring R)"
    using assms(2) by auto
  thus ?thesis
    using ring.normalize_gives_polynomial[OF univ_poly_is_ring[OF carrier_is_subring]]
    unfolding univ_poly_carrier by simp
qed

lemma (in domain) map_in_poly_ring_carrier:
  assumes "p \<in> carrier (poly_ring R)" and "\<And>a. a \<in> carrier R \<Longrightarrow> f a \<in> carrier (poly_ring R)"
    and "\<And>a. a \<noteq> \<zero> \<Longrightarrow> f a \<noteq> []"
  shows "map f p \<in> carrier (poly_ring (poly_ring R))"
proof -
  interpret UP: ring "poly_ring R"
    using univ_poly_is_ring[OF carrier_is_subring] .
  have "lead_coeff p \<noteq> \<zero>" if "p \<noteq> []"
    using that assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence "ring.normalize (poly_ring R) (map f p) = map f p"
    by (cases p) (simp_all add: assms(3) univ_poly_zero)
  thus ?thesis
    using norm_map_in_poly_ring_carrier[of p f] assms(1-2) by simp
qed

lemma (in domain) map_norm_in_poly_ring_carrier:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "map (\<lambda>a. normalize [ a ]) p \<in> carrier (poly_ring (K[X]))"
  using domain.map_in_poly_ring_carrier[OF subring_is_domain[OF assms(1)]]
proof -
  have "\<And>a. a \<in> K \<Longrightarrow> normalize [ a ] \<in> carrier (K[X])"
   and "\<And>a. a \<noteq> \<zero> \<Longrightarrow> normalize [ a ] \<noteq> []"
    using ring_hom_memE(1)[OF canonical_embedding_is_hom[OF assms(1)]] by auto
  thus ?thesis
    using domain.map_in_poly_ring_carrier[OF subring_is_domain[OF assms(1)]] assms(2)
    unfolding univ_poly_consistent[OF assms(1)] by simp
qed

lemma (in domain) polynomial_rupture:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "(ring.eval (Rupt K p)) (map ((rupture_surj K p) \<circ> (\<lambda>a. normalize [ a ])) p) (rupture_surj K p X) = \<zero>\<^bsub>Rupt K p\<^esub>"
proof -
  let ?norm = "\<lambda>a. normalize [ a ]"
  let ?surj = "rupture_surj K p"

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .
  interpret Hom: ring_hom_ring "K[X]" "Rupt K p" ?surj
    using rupture_surj_hom(2)[OF assms] .

  have "(Hom.S.eval) (map (?surj \<circ> ?norm) p) (?surj X) = ?surj ((UP.eval) (map ?norm p) X)"
    using Hom.eval_hom[OF UP.carrier_is_subring var_closed(1)[OF assms(1)]
          map_norm_in_poly_ring_carrier[OF assms]] by simp
  also have " ... = ?surj p"
    unfolding sym[OF eval_rewrite[OF assms]] ..
  also have " ... = \<zero>\<^bsub>Rupt K p\<^esub>"
    using UP.a_rcos_zero[OF UP.cgenideal_ideal[OF assms(2)] UP.cgenideal_self[OF assms(2)]]
    unfolding rupture_def FactRing_def by simp
  finally show ?thesis .
qed


subsection \<open>Division\<close>

definition (in ring) long_divides :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) \<Rightarrow> bool"
  where "long_divides p q t \<longleftrightarrow>
           \<comment> \<open>i\<close>   (t \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)) \<and>
           \<comment> \<open>ii\<close>  (p = (q \<otimes>\<^bsub>poly_ring R\<^esub> (fst t)) \<oplus>\<^bsub>poly_ring R\<^esub> (snd t)) \<and>
           \<comment> \<open>iii\<close> (snd t = [] \<or> degree (snd t) < degree q)"

definition (in ring) long_division :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)"
  where "long_division p q = (THE t. long_divides p q t)"

definition (in ring) pdiv :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "pdiv" 65)
  where "p pdiv q = (if q = [] then [] else fst (long_division p q))"

definition (in ring) pmod :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "pmod" 65)
  where "p pmod q = (if q = [] then p else snd (long_division p q))"


lemma (in domain) exists_long_division:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  obtains b r where "b \<in> carrier (K[X])" and "r \<in> carrier (K[X])" and "long_divides p q (b, r)"
  using subfield_long_division_theorem_shell[OF assms(1-3)] assms(4)
        carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]]
  unfolding long_divides_def univ_poly_zero univ_poly_add univ_poly_mult by auto

lemma (in domain) exists_unique_long_division:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "\<exists>!t. long_divides p q t"
proof -
  let ?padd   = "\<lambda>a b. a \<oplus>\<^bsub>poly_ring R\<^esub> b"
  let ?pmult  = "\<lambda>a b. a \<otimes>\<^bsub>poly_ring R\<^esub> b"
  let ?pminus = "\<lambda>a b. a \<ominus>\<^bsub>poly_ring R\<^esub> b"

  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  obtain b r where ldiv: "long_divides p q (b, r)"
    using exists_long_division[OF assms] by metis

  moreover have "(b, r) = (b', r')" if "long_divides p q (b', r')" for b' r'
  proof -
    have q: "q \<in> carrier (poly_ring R)" "q \<noteq> []"
      using assms(3-4) carrier_polynomial[OF subfieldE(1)[OF assms(1)]]
      unfolding univ_poly_carrier by auto 
    hence in_carrier: "q \<in> carrier (poly_ring R)"
      "b  \<in> carrier (poly_ring R)" "r  \<in> carrier (poly_ring R)"
      "b' \<in> carrier (poly_ring R)" "r' \<in> carrier (poly_ring R)" 
      using assms(3) that ldiv unfolding long_divides_def by auto
    have "?pminus (?padd (?pmult q b) r) r' = ?pminus (?padd (?pmult q b') r') r'"
      using ldiv and that unfolding long_divides_def by auto
    hence eq: "?padd (?pmult q (?pminus b b')) (?pminus r r') = \<zero>\<^bsub>poly_ring R\<^esub>"
      using in_carrier by algebra
    have "b = b'"
    proof (rule ccontr)
      assume "b \<noteq> b'"
      hence pminus: "?pminus b b' \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>" "?pminus b b' \<in> carrier (poly_ring R)"
        using in_carrier(2,4) by (metis UP.add.inv_closed UP.l_neg UP.minus_eq UP.minus_unique, algebra)
      hence degree_ge: "degree (?pmult q (?pminus b b')) \<ge> degree q"
        using poly_mult_degree_eq[OF carrier_is_subring, of q "?pminus b b'"] q
        unfolding univ_poly_zero univ_poly_carrier univ_poly_mult by simp

      have "?pminus b b' = \<zero>\<^bsub>poly_ring R\<^esub>" if "?pminus r r' = \<zero>\<^bsub>poly_ring R\<^esub>"
        using eq pminus(2) q UP.integral univ_poly_zero unfolding that by auto 
      hence "?pminus r r' \<noteq> []"
        using pminus(1) unfolding univ_poly_zero by blast
      moreover have "?pminus r r' = []" if "r = []" and "r' = []"
        using univ_poly_a_inv_def'[OF carrier_is_subring UP.zero_closed] that
        unfolding a_minus_def univ_poly_add univ_poly_zero by auto
      ultimately have "r \<noteq> [] \<or> r' \<noteq> []"
        by blast
      hence "max (degree r) (degree r') < degree q"
        using ldiv and that unfolding long_divides_def by auto
      moreover have "degree (?pminus r r') \<le> max (degree r) (degree r')"
        using poly_add_degree[of r "map (a_inv R) r'"]
        unfolding a_minus_def univ_poly_add univ_poly_a_inv_def'[OF carrier_is_subring in_carrier(5)]
        by auto
      ultimately have degree_lt: "degree (?pminus r r') < degree q"
        by linarith
      have is_poly: "polynomial (carrier R) (?pmult q (?pminus b b'))" "polynomial (carrier R) (?pminus r r')"
        using in_carrier pminus(2) unfolding univ_poly_carrier by algebra+
      
      have "degree (?padd (?pmult q (?pminus b b')) (?pminus r r')) = degree (?pmult q (?pminus b b'))"
        using poly_add_degree_eq[OF carrier_is_subring is_poly] degree_ge degree_lt
        unfolding univ_poly_carrier sym[OF univ_poly_add[of R "carrier R"]] max_def by simp
      hence "degree (?padd (?pmult q (?pminus b b')) (?pminus r r')) > 0"
        using degree_ge degree_lt by simp
      moreover have "degree (?padd (?pmult q (?pminus b b')) (?pminus r r')) = 0"
        using eq unfolding univ_poly_zero by simp
      ultimately show False by simp
    qed
    hence "?pminus r r' = \<zero>\<^bsub>poly_ring R\<^esub>"
      using in_carrier eq by algebra
    hence "r = r'"
      using in_carrier by (metis UP.add.inv_closed UP.add.right_cancel UP.minus_eq UP.r_neg)
    with \<open>b = b'\<close> show ?thesis
      by simp
  qed

  ultimately show ?thesis
    by auto
qed

lemma (in domain) long_divisionE:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "long_divides p q (p pdiv q, p pmod q)"
  using theI'[OF exists_unique_long_division[OF assms]] assms(4)
  unfolding pmod_def pdiv_def long_division_def by auto

lemma (in domain) long_divisionI:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "long_divides p q (b, r) \<Longrightarrow> (b, r) = (p pdiv q, p pmod q)"
  using exists_unique_long_division[OF assms] long_divisionE[OF assms] by metis

lemma (in domain) long_division_closed:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p pdiv q \<in> carrier (K[X])" and "p pmod q \<in> carrier (K[X])"
proof -
  have "p pdiv q \<in> carrier (K[X]) \<and> p pmod q \<in> carrier (K[X])"
    using assms univ_poly_zero_closed[of R] long_divisionI[of K] exists_long_division[OF assms]
    by (cases "q = []") (simp add: pdiv_def pmod_def, metis Pair_inject)+
  thus "p pdiv q \<in> carrier (K[X])" and "p pmod q \<in> carrier (K[X])"
    by auto
qed

lemma (in domain) pdiv_pmod:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p = (q \<otimes>\<^bsub>K[X]\<^esub> (p pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (p pmod q)"
proof (cases)
  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .
  assume "q = []" thus ?thesis
    using assms(2) unfolding pdiv_def pmod_def sym[OF univ_poly_zero[of R K]] by simp
next
  assume "q \<noteq> []" thus ?thesis
    using long_divisionE[OF assms] unfolding long_divides_def univ_poly_mult univ_poly_add by simp
qed

lemma (in domain) pmod_degree:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "p pmod q = [] \<or> degree (p pmod q) < degree q"
  using long_divisionE[OF assms] unfolding long_divides_def by auto

lemma (in domain) pmod_const:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])" and "degree q > degree p" 
  shows "p pdiv q = []" and "p pmod q = p"
proof -
  have "p pdiv q = [] \<and> p pmod q = p"
  proof (cases)
    interpret UP: ring "K[X]"
      using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .

    assume "q \<noteq> []"
    have "p = (q \<otimes>\<^bsub>K[X]\<^esub> []) \<oplus>\<^bsub>K[X]\<^esub> p"
      using assms(2-3) unfolding sym[OF univ_poly_zero[of R K]] by simp
    moreover have "([], p) \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)"
      using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)] assms(2)] by auto
    ultimately have "long_divides p q ([], p)"
      using assms(4) unfolding long_divides_def univ_poly_mult univ_poly_add by auto
    with \<open>q \<noteq> []\<close> show ?thesis
      using long_divisionI[OF assms(1-3)] by auto
  qed (simp add: pmod_def pdiv_def)
  thus "p pdiv q = []" and "p pmod q = p"
    by auto
qed

lemma (in domain) long_division_zero:
  assumes "subfield K R" and "q \<in> carrier (K[X])" shows "[] pdiv q = []" and "[] pmod q = []"
proof -
  interpret UP: ring "poly_ring R"
    using univ_poly_is_ring[OF carrier_is_subring] .

  have "[] pdiv q = [] \<and> [] pmod q = []"
  proof (cases)
    assume "q \<noteq> []"
    have "q \<in> carrier (poly_ring R)"
      using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)] assms(2)] .
    hence "long_divides [] q ([], [])"
      unfolding long_divides_def sym[OF univ_poly_zero[of R "carrier R"]] by auto
    with \<open>q \<noteq> []\<close> show ?thesis
      using long_divisionI[OF assms(1) univ_poly_zero_closed assms(2)] by simp
  qed (simp add: pmod_def pdiv_def)
  thus "[] pdiv q = []" and "[] pmod q = []"
    by auto
qed

lemma (in domain) long_division_a_inv:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "((\<ominus>\<^bsub>K[X]\<^esub> p) pdiv q) = \<ominus>\<^bsub>K[X]\<^esub> (p pdiv q)" (is "?pdiv")
    and "((\<ominus>\<^bsub>K[X]\<^esub> p) pmod q) = \<ominus>\<^bsub>K[X]\<^esub> (p pmod q)" (is "?pmod")
proof -
  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .

  have "?pdiv \<and> ?pmod"
  proof (cases)
    assume "q = []" thus ?thesis
      unfolding pmod_def pdiv_def sym[OF univ_poly_zero[of R K]] by simp
  next
    assume not_nil: "q \<noteq> []"
    have "\<ominus>\<^bsub>K[X]\<^esub> p = \<ominus>\<^bsub>K[X]\<^esub> ((q \<otimes>\<^bsub>K[X]\<^esub> (p pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (p pmod q))"
      using pdiv_pmod[OF assms] by simp
    hence "\<ominus>\<^bsub>K[X]\<^esub> p = (q \<otimes>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q))) \<oplus>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> (p pmod q))"
      using assms(2-3) long_division_closed[OF assms] by algebra
    moreover have "\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q) \<in> carrier (K[X])" "\<ominus>\<^bsub>K[X]\<^esub> (p pmod q) \<in> carrier (K[X])"
      using long_division_closed[OF assms] by algebra+
    hence "(\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q), \<ominus>\<^bsub>K[X]\<^esub> (p pmod q)) \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)"
      using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]] by auto
    moreover have "\<ominus>\<^bsub>K[X]\<^esub> (p pmod q) = [] \<or> degree (\<ominus>\<^bsub>K[X]\<^esub> (p pmod q)) < degree q"
      using univ_poly_a_inv_length[OF subfieldE(1)[OF assms(1)]
            long_division_closed(2)[OF assms]] pmod_degree[OF assms not_nil]
      by auto
    ultimately have "long_divides (\<ominus>\<^bsub>K[X]\<^esub> p) q (\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q), \<ominus>\<^bsub>K[X]\<^esub> (p pmod q))"
      unfolding long_divides_def univ_poly_mult univ_poly_add by simp
    thus ?thesis
      using long_divisionI[OF assms(1) UP.a_inv_closed[OF assms(2)] assms(3) not_nil] by simp
  qed
  thus ?pdiv and ?pmod
    by auto
qed

lemma (in domain) long_division_add:
  assumes "subfield K R" and "a \<in> carrier (K[X])" "b \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "(a \<oplus>\<^bsub>K[X]\<^esub> b) pdiv q = (a pdiv q) \<oplus>\<^bsub>K[X]\<^esub> (b pdiv q)" (is "?pdiv")
    and "(a \<oplus>\<^bsub>K[X]\<^esub> b) pmod q = (a pmod q) \<oplus>\<^bsub>K[X]\<^esub> (b pmod q)" (is "?pmod")
proof -
  let ?pdiv_add = "(a pdiv q) \<oplus>\<^bsub>K[X]\<^esub> (b pdiv q)"
  let ?pmod_add = "(a pmod q) \<oplus>\<^bsub>K[X]\<^esub> (b pmod q)"

  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .

  have "?pdiv \<and> ?pmod"
  proof (cases)
    assume "q = []" thus ?thesis
      using assms(2-3) unfolding pmod_def pdiv_def sym[OF univ_poly_zero[of R K]] by simp
  next
    note in_carrier = long_division_closed[OF assms(1,2,4)]
                      long_division_closed[OF assms(1,3,4)]

    assume "q \<noteq> []"
    have "a \<oplus>\<^bsub>K[X]\<^esub> b = ((q \<otimes>\<^bsub>K[X]\<^esub> (a pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (a pmod q)) \<oplus>\<^bsub>K[X]\<^esub>
                         ((q \<otimes>\<^bsub>K[X]\<^esub> (b pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (b pmod q))"
      using assms(2-3)[THEN pdiv_pmod[OF assms(1) _ assms(4)]] by simp
    hence "a \<oplus>\<^bsub>K[X]\<^esub> b = (q \<otimes>\<^bsub>K[X]\<^esub> ?pdiv_add) \<oplus>\<^bsub>K[X]\<^esub> ?pmod_add"
      using assms(4) in_carrier by algebra
    moreover have "(?pdiv_add, ?pmod_add) \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)"
      using in_carrier carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]] by auto
    moreover have "?pmod_add = [] \<or> degree ?pmod_add < degree q"
    proof (cases)
      assume "?pmod_add \<noteq> []"
      hence "a pmod q \<noteq> [] \<or> b pmod q \<noteq> []"
        using in_carrier(2,4) unfolding sym[OF univ_poly_zero[of R K]] by auto
      moreover from \<open>q \<noteq> []\<close>
      have "a pmod q = [] \<or> degree (a pmod q) < degree q" and "b pmod q = [] \<or> degree (b pmod q) < degree q"
        using assms(2-3)[THEN pmod_degree[OF assms(1) _ assms(4)]] by auto
      ultimately have "max (degree (a pmod q)) (degree (b pmod q)) < degree q"
        by auto
      thus ?thesis
        using poly_add_degree le_less_trans unfolding univ_poly_add by blast
    qed simp
    ultimately have "long_divides (a \<oplus>\<^bsub>K[X]\<^esub> b) q (?pdiv_add, ?pmod_add)"
      unfolding long_divides_def univ_poly_mult univ_poly_add by simp
    with \<open>q \<noteq> []\<close> show ?thesis
      using long_divisionI[OF assms(1) UP.a_closed[OF assms(2-3)] assms(4)] by simp
  qed
  thus ?pdiv and ?pmod
    by auto
qed

lemma (in domain) long_division_add_iff:
  assumes "subfield K R"
    and "a \<in> carrier (K[X])" "b \<in> carrier (K[X])" "c \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "a pmod q = b pmod q \<longleftrightarrow> (a \<oplus>\<^bsub>K[X]\<^esub> c) pmod q = (b \<oplus>\<^bsub>K[X]\<^esub> c) pmod q"
proof -
  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .
  show ?thesis
    using assms(2-4)[THEN long_division_closed(2)[OF assms(1) _ assms(5)]]
    unfolding assms(2-3)[THEN long_division_add(2)[OF assms(1) _ assms(4-5)]] by auto
qed

lemma (in domain) pdivides_iff:
  assumes "subfield K R" and "polynomial K p" "polynomial K q"
  shows "p pdivides q \<longleftrightarrow> p divides\<^bsub>K[X]\<^esub> q"
proof
  show "p divides\<^bsub>K [X]\<^esub> q \<Longrightarrow> p pdivides q"
    using carrier_polynomial[OF subfieldE(1)[OF assms(1)]]
    unfolding pdivides_def factor_def univ_poly_mult univ_poly_carrier by auto
next
  interpret UP: ring "poly_ring R"
    using univ_poly_is_ring[OF carrier_is_subring] .
  
  have in_carrier: "p \<in> carrier (poly_ring R)" "q \<in> carrier (poly_ring R)"
    using carrier_polynomial[OF subfieldE(1)[OF assms(1)]] assms
    unfolding univ_poly_carrier by auto

  assume "p pdivides q"
  then obtain b where "b \<in> carrier (poly_ring R)" and "q = p \<otimes>\<^bsub>poly_ring R\<^esub> b"
      unfolding pdivides_def factor_def by blast
  show "p divides\<^bsub>K[X]\<^esub> q"
  proof (cases)
    assume "p = []"
    with \<open>b \<in> carrier (poly_ring R)\<close> and \<open>q = p \<otimes>\<^bsub>poly_ring R\<^esub> b\<close> have "q = []"
      unfolding univ_poly_mult sym[OF univ_poly_carrier]
      using poly_mult_zero(1)[OF polynomial_incl] by simp
    with \<open>p = []\<close> show ?thesis
      using poly_mult_zero(2)[of "[]"]
      unfolding factor_def univ_poly_mult by auto 
  next
    interpret UP: ring "poly_ring R"
      using univ_poly_is_ring[OF carrier_is_subring] .

    assume "p \<noteq> []"
    from \<open>p pdivides q\<close> obtain b where "b \<in> carrier (poly_ring R)" and "q = p \<otimes>\<^bsub>poly_ring R\<^esub> b"
      unfolding pdivides_def factor_def by blast
    moreover have "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)"
      using assms carrier_polynomial[OF subfieldE(1)[OF assms(1)]] unfolding univ_poly_carrier by auto
    ultimately have "q = (p \<otimes>\<^bsub>poly_ring R\<^esub> b) \<oplus>\<^bsub>poly_ring R\<^esub> \<zero>\<^bsub>poly_ring R\<^esub>"
      by algebra
    with \<open>b \<in> carrier (poly_ring R)\<close> have "long_divides q p (b, [])"
      unfolding long_divides_def univ_poly_zero by auto
    with \<open>p \<noteq> []\<close> have "b \<in> carrier (K[X])"
      using long_divisionI[of K q p b] long_division_closed[of K q p] assms
      unfolding univ_poly_carrier by auto
    with \<open>q = p \<otimes>\<^bsub>poly_ring R\<^esub> b\<close> show ?thesis
      unfolding factor_def univ_poly_mult by blast
  qed
qed

lemma (in domain) pdivides_iff_shell:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p pdivides q \<longleftrightarrow> p divides\<^bsub>K[X]\<^esub> q"
  using pdivides_iff assms by (simp add: univ_poly_carrier)

lemma (in domain) pmod_zero_iff_pdivides:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p pmod q = [] \<longleftrightarrow> q pdivides p"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms(1)]] .

  show ?thesis
  proof
    assume pmod: "p pmod q = []"
    have "p pdiv q \<in> carrier (K[X])" and "p pmod q \<in> carrier (K[X])"
      using long_division_closed[OF assms] by auto
    hence "p = q \<otimes>\<^bsub>K[X]\<^esub> (p pdiv q)"
      using pdiv_pmod[OF assms] assms(3) unfolding pmod sym[OF univ_poly_zero[of R K]] by algebra
    with \<open>p pdiv q \<in> carrier (K[X])\<close> show "q pdivides p"
      unfolding pdivides_iff_shell[OF assms(1,3,2)] factor_def by blast
  next
    assume "q pdivides p" show "p pmod q = []"
    proof (cases)
      assume "q = []" with \<open>q pdivides p\<close> show ?thesis
        using zero_pdivides unfolding pmod_def by simp
    next
      assume "q \<noteq> []"
      from \<open>q pdivides p\<close> obtain r where "r \<in> carrier (K[X])" and "p = q \<otimes>\<^bsub>K[X]\<^esub> r"
        unfolding pdivides_iff_shell[OF assms(1,3,2)] factor_def by blast
      hence "p = (q \<otimes>\<^bsub>K[X]\<^esub> r) \<oplus>\<^bsub>K[X]\<^esub> []"
        using assms(2) unfolding sym[OF univ_poly_zero[of R K]] by simp
      moreover from \<open>r \<in> carrier (K[X])\<close> have "r \<in> carrier (poly_ring R)"
        using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]] by auto
      ultimately have "long_divides p q (r, [])"
        unfolding long_divides_def univ_poly_mult univ_poly_add by auto
      with \<open>q \<noteq> []\<close> show ?thesis
        using long_divisionI[OF assms] by simp
    qed
  qed
qed

lemma (in domain) same_pmod_iff_pdivides:
  assumes "subfield K R" and "a \<in> carrier (K[X])" "b \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "a pmod q = b pmod q \<longleftrightarrow> q pdivides (a \<ominus>\<^bsub>K[X]\<^esub> b)"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms(1)]] .

  have "a pmod q = b pmod q \<longleftrightarrow> (a \<oplus>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> b)) pmod q = (b \<oplus>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> b)) pmod q"
    using long_division_add_iff[OF assms(1-3) UP.a_inv_closed[OF assms(3)] assms(4)] .
  also have " ... \<longleftrightarrow> (a \<ominus>\<^bsub>K[X]\<^esub> b) pmod q = \<zero>\<^bsub>K[X]\<^esub> pmod q"
    using assms(2-3) by algebra
  also have " ... \<longleftrightarrow> q pdivides (a \<ominus>\<^bsub>K[X]\<^esub> b)"
    using pmod_zero_iff_pdivides[OF assms(1) UP.minus_closed[OF assms(2-3)] assms(4)]
    unfolding univ_poly_zero long_division_zero(2)[OF assms(1,4)] .
  finally show ?thesis .
qed

lemma (in domain) pdivides_imp_degree_le:
  assumes "subring K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "p pdivides q \<Longrightarrow> degree p \<le> degree q"
proof -
  assume "p pdivides q"
  then obtain r where r: "polynomial (carrier R) r" "q = poly_mult p r"
    unfolding pdivides_def factor_def univ_poly_mult univ_poly_carrier by blast
  moreover have p: "polynomial (carrier R) p"
    using assms(2) carrier_polynomial[OF assms(1)] unfolding univ_poly_carrier by auto
  moreover have "p \<noteq> []" and "r \<noteq> []"
    using poly_mult_zero(2)[OF polynomial_incl[OF p]] r(2) assms(4) by auto 
  ultimately show "degree p \<le> degree q"
    using poly_mult_degree_eq[OF carrier_is_subring, of p r] by auto
qed

lemma (in domain) pprimeE:
  assumes "subfield K R" "p \<in> carrier (K[X])" "pprime K p"
  shows "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p pdivides (q \<otimes>\<^bsub>K[X]\<^esub> r) \<Longrightarrow> p pdivides q \<or> p pdivides r"
  using assms(2-3) poly_mult_closed[OF subfieldE(1)[OF assms(1)]] pdivides_iff[OF assms(1)]
  unfolding ring_prime_def prime_def 
  by (auto simp add: univ_poly_mult univ_poly_carrier univ_poly_zero)

lemma (in domain) pprimeI:
  assumes "subfield K R" "p \<in> carrier (K[X])" "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p pdivides (q \<otimes>\<^bsub>K[X]\<^esub> r) \<Longrightarrow> p pdivides q \<or> p pdivides r"
  shows "pprime K p"
  using assms(2-5) poly_mult_closed[OF subfieldE(1)[OF assms(1)]] pdivides_iff[OF assms(1)]
  unfolding ring_prime_def prime_def
  by (auto simp add: univ_poly_mult univ_poly_carrier univ_poly_zero)

lemma (in domain) associated_polynomials_iff:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p \<sim>\<^bsub>K[X]\<^esub> q \<longleftrightarrow> (\<exists>k \<in> K - { \<zero> }. p = [ k ] \<otimes>\<^bsub>K[X]\<^esub> q)"
  using domain.ring_associated_iff[OF univ_poly_is_domain[OF subfieldE(1)[OF assms(1)]] assms(2-3)]
  unfolding univ_poly_units[OF assms(1)] by auto

corollary (in domain) associated_polynomials_imp_same_length: (* stronger than "imp_same_degree" *)
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p \<sim>\<^bsub>K[X]\<^esub> q \<Longrightarrow> length p = length q"
  unfolding associated_polynomials_iff[OF assms]
  using poly_mult_const(1)[OF subfieldE(1)[OF assms(1)],of q] assms(3)
  by (auto simp add: univ_poly_carrier univ_poly_mult simp del: poly_mult.simps)


subsection \<open>Ideals\<close>

lemma (in domain) exists_unique_gen:
  assumes "subfield K R" "ideal I (K[X])" "I \<noteq> { [] }"
  shows "\<exists>!p \<in> carrier (K[X]). lead_coeff p = \<one> \<and> I = PIdl\<^bsub>K[X]\<^esub> p"
    (is "\<exists>!p. ?generator p")
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .
  obtain q where q: "q \<in> carrier (K[X])" "I = PIdl\<^bsub>K[X]\<^esub> q"
    using UP.exists_gen[OF assms(2)] by blast
  hence not_nil: "q \<noteq> []"
    using UP.genideal_zero UP.cgenideal_eq_genideal[OF UP.zero_closed] assms(3)
    by (auto simp add: univ_poly_zero)
  hence "lead_coeff q \<in> K - { \<zero> }"
    using q(1) unfolding univ_poly_def polynomial_def by auto
  hence inv_lc_q: "inv (lead_coeff q) \<in> K - { \<zero> }" "inv (lead_coeff q) \<otimes> lead_coeff q = \<one>"
    using subfield_m_inv[OF assms(1)] by auto 

  define p where "p = [ inv (lead_coeff q) ] \<otimes>\<^bsub>K[X]\<^esub> q"
  have is_poly: "polynomial K [ inv (lead_coeff q) ]" "polynomial K q"
    using inv_lc_q(1) q(1) unfolding univ_poly_def polynomial_def by auto
  hence in_carrier: "p \<in> carrier (K[X])"
    using UP.m_closed unfolding univ_poly_carrier p_def by simp
  have lc_p: "lead_coeff p = \<one>"
    using poly_mult_lead_coeff[OF subfieldE(1)[OF assms(1)] is_poly _ not_nil] inv_lc_q(2)
    unfolding p_def univ_poly_mult[of R K] by simp
  moreover have PIdl_p: "I = PIdl\<^bsub>K[X]\<^esub> p"
    using UP.associated_iff_same_ideal[OF in_carrier q(1)] q(2) inv_lc_q(1) p_def
          associated_polynomials_iff[OF assms(1) in_carrier q(1)]
    by auto
  ultimately have "?generator p"
    using in_carrier by simp

  moreover
  have "\<And>r. \<lbrakk> r \<in> carrier (K[X]); lead_coeff r = \<one>; I = PIdl\<^bsub>K[X]\<^esub> r \<rbrakk> \<Longrightarrow> r = p"
  proof -
    fix r assume r: "r \<in> carrier (K[X])" "lead_coeff r = \<one>" "I = PIdl\<^bsub>K[X]\<^esub> r"
    obtain k where k: "k \<in> K - { \<zero> }" "r = [ k ] \<otimes>\<^bsub>K[X]\<^esub> p"
      using UP.associated_iff_same_ideal[OF r(1) in_carrier] PIdl_p r(3)
            associated_polynomials_iff[OF assms(1) r(1) in_carrier]
      by auto
    hence "polynomial K [ k ]"
      unfolding polynomial_def by simp
    moreover have "p \<noteq> []"
      using not_nil UP.associated_iff_same_ideal[OF in_carrier q(1)] q(2) PIdl_p
            associated_polynomials_imp_same_length[OF assms(1) in_carrier q(1)] by auto
    ultimately have "lead_coeff r = k \<otimes> (lead_coeff p)"
      using poly_mult_lead_coeff[OF subfieldE(1)[OF assms(1)]] in_carrier k(2)
      unfolding univ_poly_def by (auto simp del: poly_mult.simps)
    hence "k = \<one>"
      using lc_p r(2) k(1) subfieldE(3)[OF assms(1)] by auto
    hence "r = map ((\<otimes>) \<one>) p"
      using poly_mult_const(1)[OF subfieldE(1)[OF assms(1)] _ k(1), of p] in_carrier
      unfolding k(2) univ_poly_carrier[of R K] univ_poly_mult[of R K] by auto
    moreover have "set p \<subseteq> carrier R"
      using polynomial_in_carrier[OF subfieldE(1)[OF assms(1)]]
            in_carrier univ_poly_carrier[of R K] by auto
    hence "map ((\<otimes>) \<one>) p = p"
      by (induct p) (auto)
    ultimately show "r = p" by simp
  qed

  ultimately show ?thesis by blast
qed

proposition (in domain) exists_unique_pirreducible_gen:
  assumes "subfield K R" "ring_hom_ring (K[X]) R h"
    and "a_kernel (K[X]) R h \<noteq> { [] }" "a_kernel (K[X]) R h \<noteq> carrier (K[X])"
  shows "\<exists>!p \<in> carrier (K[X]). pirreducible K p \<and> lead_coeff p = \<one> \<and> a_kernel (K[X]) R h = PIdl\<^bsub>K[X]\<^esub> p"
    (is "\<exists>!p. ?generator p")
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  have "ideal (a_kernel (K[X]) R h) (K[X])"
    using ring_hom_ring.kernel_is_ideal[OF assms(2)] .
  then obtain p
    where p: "p \<in> carrier (K[X])" "lead_coeff p = \<one>" "a_kernel (K[X]) R h = PIdl\<^bsub>K[X]\<^esub> p"
      and unique:
      "\<And>q. \<lbrakk> q \<in> carrier (K[X]); lead_coeff q = \<one>; a_kernel (K[X]) R h = PIdl\<^bsub>K[X]\<^esub> q \<rbrakk> \<Longrightarrow> q = p"
    using exists_unique_gen[OF assms(1) _ assms(3)] by metis

  have "pprime K p"
  proof (rule pprimeI[OF assms(1) p(1)])
    show "p \<noteq> []"
      using UP.genideal_zero UP.cgenideal_eq_genideal[OF UP.zero_closed] assms(3) p(3)
      by (auto simp add: univ_poly_zero)
  next
    show "p \<notin> Units (K [X])"
      using UP.ideal_eq_carrier_iff[OF p(1)] assms(4) p(3) by auto
  next
    note ring_hom_props = ring_hom_memE[OF ring_hom_ring.homh[OF assms(2)]]

    fix q r
    assume q: "q \<in> carrier (K[X])" and r: "r \<in> carrier (K[X])" and pdvd: "p pdivides (q \<otimes>\<^bsub>K [X]\<^esub> r)"
    obtain s where s: "s \<in> carrier (K[X])" "q \<otimes>\<^bsub>K [X]\<^esub> r = p \<otimes>\<^bsub>K [X]\<^esub> s"
      using pdivides_iff[OF assms(1)] p(1) UP.m_closed[OF q r] pdvd
      unfolding univ_poly_carrier[of R K] by auto
    hence "h (q \<otimes>\<^bsub>K [X]\<^esub> r) = h (p \<otimes>\<^bsub>K [X]\<^esub> s)" by simp
    hence "h q \<otimes> h r = h p \<otimes> h s"
      using ring_hom_props(2) q r p(1) s(1) by auto
    moreover have "p \<in> a_kernel (K[X]) R h"
      by (simp add: UP.cgenideal_self p(1) p(3))
    hence "h p = \<zero>"
      unfolding a_kernel_def' by simp
    ultimately have "h q \<otimes> h r = \<zero>"
      using ring_hom_props(1)[OF s(1)] by simp
    hence "h q = \<zero> \<or> h r = \<zero>"
      using integral ring_hom_props(1) q r by auto

    moreover have "\<And>a. \<lbrakk> a \<in> carrier (K[X]); h a = \<zero> \<rbrakk> \<Longrightarrow> p pdivides a"
    proof -
      fix a assume a: "a \<in> carrier (K[X])" "h a = \<zero>"
      hence "a \<in> a_kernel (K[X]) R h"
        unfolding a_kernel_def' by simp
      hence "p divides\<^bsub>K [X]\<^esub> a"
        using UP.to_contain_is_to_divide[OF p(1) a(1)] p(1) a(1) p(3)
              UP.cgenideal_ideal UP.cgenideal_minimal by blast
      thus "p pdivides a"
        using pdivides_iff_shell[OF assms(1) p(1) a(1)] by simp
    qed

    ultimately show "p pdivides q \<or> p pdivides r"
      using q r by auto
  qed
  hence "pirreducible K p"
    using pprime_iff_pirreducible[OF assms(1) p(1)] by simp
  thus ?thesis
    using p unique by metis 
qed

lemma (in domain) cgenideal_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "pirreducible K p" 
  shows "\<lbrakk> pirreducible K q; q \<in> PIdl\<^bsub>K[X]\<^esub> p \<rbrakk> \<Longrightarrow> p \<sim>\<^bsub>K[X]\<^esub> q"
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  assume q: "pirreducible K q" "q \<in> PIdl\<^bsub>K[X]\<^esub> p"
  hence in_carrier: "q \<in> carrier (K[X])"
    using additive_subgroup.a_subset[OF ideal.axioms(1)[OF UP.cgenideal_ideal[OF assms(2)]]] by auto
  hence "p divides\<^bsub>K[X]\<^esub> q"
    by (meson q assms(2) UP.cgenideal_ideal UP.cgenideal_minimal UP.to_contain_is_to_divide)
  then obtain r where r: "r \<in> carrier (K[X])" "q = p \<otimes>\<^bsub>K[X]\<^esub> r"
    by auto
  hence "r \<in> Units (K[X])"
    using pirreducibleE(3)[OF _ in_carrier q(1) assms(2) r(1)] subfieldE(1)[OF assms(1)]
          pirreducibleE(2)[OF _ assms(2-3)] by auto
  thus "p \<sim>\<^bsub>K[X]\<^esub> q"
    using UP.ring_associated_iff[OF in_carrier assms(2)] r(2) UP.associated_sym
    unfolding UP.m_comm[OF assms(2) r(1)] by auto
qed


subsection \<open>Roots and Multiplicity\<close>

lemma (in domain) pdivides_imp_root_sharing:
  assumes "p \<in> carrier (poly_ring R)" "p pdivides q" and "a \<in> carrier R"
  shows "eval p a = \<zero> \<Longrightarrow> eval q a = \<zero>"
proof - 
  from \<open>p pdivides q\<close> obtain r where r: "q = p \<otimes>\<^bsub>poly_ring R\<^esub> r" "r \<in> carrier (poly_ring R)"
    unfolding pdivides_def factor_def by auto
  hence "eval q a = (eval p a) \<otimes> (eval r a)"
    using ring_hom_memE(2)[OF eval_is_hom[OF carrier_is_subring assms(3)] assms(1) r(2)] by simp
  thus "eval p a = \<zero> \<Longrightarrow> eval q a = \<zero>"
    using ring_hom_memE(1)[OF eval_is_hom[OF carrier_is_subring assms(3)] r(2)] by auto
qed

lemma (in domain) degree_one_root:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p = 1"
  shows "eval p (\<ominus> (inv (lead_coeff p) \<otimes> (const_term p))) = \<zero>"
    and "inv (lead_coeff p) \<otimes> (const_term p) \<in> K" 
proof -
  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where p: "p = [ a, b ]"
    by (metis (no_types, hide_lams) Suc_length_conv length_0_conv)
  hence "a \<in> K - { \<zero> }" "b \<in> K"  and in_carrier: "a \<in> carrier R" "b \<in> carrier R"
    using assms(2) subfieldE(3)[OF assms(1)] unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence inv_a: "inv a \<in> carrier R" "a \<otimes> inv a = \<one>" and "inv a \<in> K"
    using subfield_m_inv(1-2)[OF assms(1), of a] subfieldE(3)[OF assms(1)] by auto 
  hence "eval p (\<ominus> (inv a \<otimes> b)) = a \<otimes> (\<ominus> (inv a \<otimes> b)) \<oplus> b"
    using in_carrier unfolding p by simp
  also have " ... = \<ominus> (a \<otimes> (inv a \<otimes> b)) \<oplus> b"
    using inv_a in_carrier by (simp add: r_minus)
  also have " ... = \<zero>"
    using in_carrier(2) unfolding sym[OF m_assoc[OF in_carrier(1) inv_a(1) in_carrier(2)]] inv_a(2) by algebra
  finally have "eval p (\<ominus> (inv a \<otimes> b)) = \<zero>" .
  moreover have ct: "const_term p = b"
    using in_carrier unfolding p const_term_def by auto
  ultimately show "eval p (\<ominus> (inv (lead_coeff p) \<otimes> (const_term p))) = \<zero>"
    unfolding p by simp
  from \<open>inv a \<in> K\<close> and \<open>b \<in> K\<close>
  show "inv (lead_coeff p) \<otimes> (const_term p) \<in> K"
    using p subringE(6)[OF subfieldE(1)[OF assms(1)]] unfolding ct by auto
qed
(*

subsection \<open>Roots and Multiplicity\<close>

definition (in ring) roots :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a set"
  where "roots K p = { x \<in> K. eval p x = \<zero> }"

inductive (in ring) pdecomposition :: "'a set \<Rightarrow> 'a multiset \<Rightarrow> 'a list \<Rightarrow> bool"
  where
    const: "a \<in> K - { \<zero> } \<Longrightarrow> pdecomposition K {#} [ a ]"
  | root:  "a \<in> K \<Longrightarrow> pdecomposition K fs p \<Longrightarrow> pdecomposition K (add_mset a fs) ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>K[X]\<^esub> p)"
  | irr:  "\<lbrakk> q \<in> carrier (K[X]); pirreducible K q; lead_coeff q = \<one>; degree q \<ge> 2 \<rbrakk> \<Longrightarrow>
             pdecomposition K fs p \<Longrightarrow> pdecomposition K fs (q \<otimes>\<^bsub>K[X]\<^esub> p)"

*)

end