(*  Title:      HOL/Algebra/Polynomial_Divisibility.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Polynomial_Divisibility
  imports Polynomials
    
begin

section \<open>Divisibility of Polynomials\<close>

subsection \<open>Definitions\<close>

abbreviation pirreducible :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" ("pirreducible\<index>")
  where "pirreducible\<^bsub>R\<^esub> K p \<equiv> ring_irreducible\<^bsub>(univ_poly R K)\<^esub> p"

abbreviation pprime :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" ("pprime\<index>")
  where "pprime\<^bsub>R\<^esub> K p \<equiv> ring_prime\<^bsub>(univ_poly R K)\<^esub> p"

definition pdivides :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "pdivides\<index>" 65)
  where "p pdivides\<^bsub>R\<^esub> q \<equiv> p divides\<^bsub>(univ_poly R (carrier R))\<^esub> q"

definition rupture :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> (('a list) set) ring" ("Rupt\<index>")
  where "Rupt\<^bsub>R\<^esub> K p = (K[X]\<^bsub>R\<^esub>) Quot (PIdl\<^bsub>K[X]\<^bsub>R\<^esub>\<^esub> p)"


subsection \<open>Basic Properties\<close>

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
  assumes "subfield K R" "p \<in> carrier (K[X])"
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
      using UP.is_ring by simp
    have "field (K[X])"
      using field.ring_iso_imp_img_field[OF field h] by simp
    thus False
      using univ_poly_not_field[OF subfieldE(1)[OF assms(1)]] by simp
  qed
  thus "pirreducible K p"
    using UP.field_iff_prime pprime_iff_pirreducible[OF assms] assms(2) field
    by (simp add: univ_poly_zero rupture_def)
qed


subsection \<open>Division\<close>

text \<open>Now, we prove that there's only need for one notion of polynomial division.
      The proof is long, but its structure is simple:
      if Q(X) = P(X).R(X) for Q, P \<in> K[X] - {0} and R(X) \<in> (carrier R)[X],
      we show that R \<in> K[X] by induction on deg P + deg R. The main idea for the
      induction step is to look at the constant term of each polynomial.\<close>

lemma (in domain) pdivides_iff:
  assumes "subfield K R" and "polynomial K p" "polynomial K q"
  shows "p pdivides q \<longleftrightarrow> p divides\<^bsub>K[X]\<^esub> q"
proof
  show "p divides\<^bsub>K [X]\<^esub> q \<Longrightarrow> p pdivides q"
    unfolding pdivides_def factor_def univ_poly_def
    using carrier_polynomial[OF subfieldE(1)[OF assms(1)]] by auto
next
  note K = subfieldE(1)[OF assms(1)]

  assume "p pdivides q"
  then obtain r where r: "polynomial (carrier R) r" "q = poly_mult p r"
    unfolding pdivides_def factor_def univ_poly_def by auto
  
  consider
    (p) "p = []" | (q) "q = []" | (not_nil) "p \<noteq> []" "q \<noteq> []" by auto
  thus "p divides\<^bsub>K[X]\<^esub> q"
  proof cases
    case p then have q: "q = []"
      using poly_mult_zero(1)[OF polynomial_incl[OF r(1)]] r(2) by simp
    thus ?thesis
      using poly_mult_zero(1)[OF polynomial_in_carrier[OF K]] r(2)
      unfolding factor_def univ_poly_def p q by auto
  next
    case q thus ?thesis
      using poly_mult_zero(2)[OF polynomial_in_carrier[OF K assms(2)]]
      unfolding factor_def univ_poly_def by auto
  next
    case not_nil then have "r \<noteq> []"
      using poly_mult_zero(2)[OF polynomial_in_carrier[OF K assms(2)]] r(2) by auto

    from not_nil this assms(2-3) r have "set r \<subseteq> K"
    proof (induct "length p + length r" arbitrary: p q r)
      case 0 thus ?case by auto
    next
      case (Suc n)
      have in_carrier:
        "set q \<subseteq> carrier R" "set p \<subseteq> carrier R" "set r \<subseteq> carrier R"
        using Suc(6-7)[THEN polynomial_in_carrier[OF K]] polynomial_incl[OF Suc(8)] by auto 

      consider
        (c0_p) "const_term p = \<zero>" | (c0_r) "const_term r = \<zero>" |
        (c0_not_zero) "const_term p \<noteq> \<zero>"  "const_term r \<noteq> \<zero>" by auto
      thus ?case
      proof cases
        case c0_p then have c0_q: "const_term q = \<zero>"
          using const_term_simprules(1-2) in_carrier(2-3) Suc(9) by auto
        obtain p' q'
          where p': "polynomial K p'" "p' \<noteq> []" "p = p' @ [ \<zero> ]"
            and q': "polynomial K q'" "q' \<noteq> []" "q = q' @ [ \<zero> ]"
          using const_term_zero[OF K] Suc(3-7) c0_p c0_q by metis
        have "q' = poly_mult p' r"
          using poly_mult_append_zero_lcancel[OF carrier_is_subring _ Suc(8), of p' q']
                carrier_polynomial[OF K p'(1)] Suc(9)
          unfolding p'(3) q'(3) by auto
        thus ?thesis
          using Suc(1)[OF _ p'(2) q'(2) Suc(5) p'(1) q'(1) Suc(8)] Suc(2) p'(3) by auto
      next
        case c0_r then have c0_q: "const_term q = \<zero>"
          using const_term_simprules(1-2) in_carrier(2-3) Suc(9) by auto
        obtain r' q'
          where r': "polynomial (carrier R) r'" "r' \<noteq> []" "r = r' @ [ \<zero> ]"
            and q': "polynomial K q'" "q' \<noteq> []" "q = q' @ [ \<zero> ]"
          using const_term_zero[OF carrier_is_subring Suc(8,5) c0_r]
                const_term_zero[OF K Suc(7,4) c0_q] by metis
        have "q' = poly_mult p r'"
          using poly_mult_append_zero_rcancel[OF carrier_is_subring _ r'(1), of p q']
                carrier_polynomial[OF K Suc(6)] Suc(9)
          unfolding r'(3) q'(3) by auto
        hence "set r' \<subseteq> K"
          using Suc(1)[OF _ Suc(3) q'(2) r'(2) Suc(6) q'(1) r'(1)] Suc(2) r'(3) by auto
        thus ?thesis
          using subringE(2)[OF K] unfolding r'(3) by auto
      next
        case c0_not_zero note c0_p = c0_not_zero(1) and c0_r = c0_not_zero(2)
        obtain r' r0 where r: "r = r' @ [ r0 ]"
          using Suc(5) rev_exhaust by blast
        hence set_r': "set r' \<subseteq> carrier R" and r0: "r0 \<in> carrier R" "r0 \<noteq> \<zero>"
          using polynomial_incl[OF Suc(8)] const_term_eq_last[of r' r0] c0_r by auto
        have "const_term q = const_term p \<otimes> r0"
          using const_term_simprules(2) in_carrier(2-3) Suc(9) r const_term_eq_last[of r' r0]
          unfolding r by auto
        moreover have "const_term p \<in> K - { \<zero> }" and "const_term q \<in> K"
          using const_term_simprules_shell(1)[OF K] Suc(6-7) c0_p
          by (auto simp add: univ_poly_def)
        ultimately have r0_in_K: "r0 \<in> K"
          using subfield_m_inv_simprule[OF assms(1) _ r0(1)] by auto
        show ?thesis
        proof (cases "r' = []")
          assume "r' = []" thus ?thesis
            using r0_in_K unfolding r by auto
        next
          interpret UP: domain "(carrier R)[X]"
            using univ_poly_is_domain[OF carrier_is_subring] .
          define s where "s = q \<ominus>\<^bsub>(carrier R)[X]\<^esub> (p \<otimes>\<^bsub>(carrier R)[X]\<^esub> [ r0 ])"
                
          assume r': "r' \<noteq> []"
          hence "polynomial (carrier R) (r' @ [ \<zero> ])" and "polynomial (carrier R) [ r0 ]"
            using Suc(8) r0 unfolding r polynomial_def by auto
          hence in_carrier:
            "r' @ [ \<zero> ] \<in> carrier ((carrier R)[X])" "[ r0 ] \<in> carrier ((carrier R)[X])"
                     "p \<in> carrier ((carrier R)[X])"      "q \<in> carrier ((carrier R)[X])"
            using Suc(6-7)[THEN carrier_polynomial[OF K]] by (auto simp add: univ_poly_def)
          
          have "poly_add (r' @ [ \<zero> ]) [ r0 ] = r"
            using r0 poly_add_append_replicate[OF set_r', of "[ r0 ]"]
                  normalize_polynomial[OF Suc(8)] unfolding r by auto
          hence "q = p \<otimes>\<^bsub>(carrier R)[X]\<^esub> ((r' @ [ \<zero> ]) \<oplus>\<^bsub>(carrier R)[X]\<^esub> [ r0 ])"
            using Suc(9) by (auto simp add: univ_poly_def simp del: poly_add.simps poly_mult.simps)
          hence "s = (p \<otimes>\<^bsub>(carrier R)[X]\<^esub> ((r' @ [ \<zero> ]) \<oplus>\<^bsub>(carrier R)[X]\<^esub> [ r0 ]))
                        \<ominus>\<^bsub>(carrier R)[X]\<^esub> (p \<otimes>\<^bsub>(carrier R)[X]\<^esub> [r0])"
            by (simp add: s_def)
          hence s_def': "s = p \<otimes>\<^bsub>(carrier R)[X]\<^esub> (r' @ [ \<zero> ])"
            using in_carrier unfolding s_def by algebra
          hence c0_s: "const_term s = \<zero>"
            using const_term_simprules_shell(1,2)[OF carrier_is_subring] in_carrier(3,1)
                  const_term_eq_last[OF set_r' zero_closed] by auto

          have "p \<noteq> \<zero>\<^bsub>(carrier R)[X]\<^esub>" and "r' @ [ \<zero> ] \<noteq> \<zero>\<^bsub>(carrier R)[X]\<^esub>"
            using Suc(3) by (auto simp add: univ_poly_def)
          hence "s \<noteq> \<zero>\<^bsub>(carrier R)[X]\<^esub>"
            using s_def' UP.integral[OF _ in_carrier(3,1)] by auto
          hence s: "s \<noteq> []"
            by (simp add: univ_poly_def)

          have "polynomial K [ r0 ]"
            using r0_in_K r0(2) unfolding polynomial_def by auto
          hence "q \<in> carrier (K[X])" "p \<in> carrier (K[X])" "[ r0 ] \<in> carrier (K[X])"
            using Suc(6-7) by (auto simp add: univ_poly_def)
          hence "q \<ominus>\<^bsub>K[X]\<^esub> (p \<otimes>\<^bsub>K[X]\<^esub> [ r0 ]) \<in> carrier (K[X])"
            and aux_exp: "p \<otimes>\<^bsub>K[X]\<^esub> [ r0 ] \<in> carrier (K[X])"
            using ring.ring_simprules(4,5)[OF univ_poly_is_ring[OF K]] by auto
          moreover have "s = q \<ominus>\<^bsub>(carrier R)[X]\<^esub> (p \<otimes>\<^bsub>K[X]\<^esub> [ r0 ])"
            unfolding s_def univ_poly_def by auto
          hence "s = q \<ominus>\<^bsub>K[X]\<^esub> (p \<otimes>\<^bsub>K[X]\<^esub> [ r0 ])"
            using univ_poly_a_minus_consistent[OF K aux_exp] by simp
          ultimately have "s \<in> carrier (K[X])" by simp
          hence "polynomial K s"
            by (simp add: univ_poly_def)
          then obtain s' where s': "polynomial K s'" "s' \<noteq> []" "s = s' @ [ \<zero> ]"
            using const_term_zero[OF K _ s c0_s] by blast

          have is_poly: "polynomial (carrier R) r'"
            using in_carrier(1) by (auto simp add: univ_poly_def polynomial_def)
          moreover have "poly_mult p (r' @ [ \<zero> ]) = s' @ [ \<zero> ]"
            using s_def' by (auto simp add: s'(3) univ_poly_def)
          ultimately have "s' = poly_mult p r'"
            using poly_mult_append_zero_rcancel[OF carrier_is_subring
                  carrier_polynomial[OF K Suc(6)], of r' s'] by simp
          hence "set r' \<subseteq> K"
            using Suc(1)[OF _ Suc(3) s'(2) r' Suc(6) s'(1) is_poly] Suc(2) r by auto
          thus ?thesis
            using r0_in_K unfolding r by auto
        qed
      qed
    qed
    thus ?thesis
      using r by (auto simp add: factor_def univ_poly_def polynomial_def)
  qed
qed

lemma (in domain) pdivides_iff_shell:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p pdivides q \<longleftrightarrow> p divides\<^bsub>K[X]\<^esub> q"
  using pdivides_iff assms by (simp add: univ_poly_carrier)

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

end