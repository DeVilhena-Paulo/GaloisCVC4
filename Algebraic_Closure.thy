theory Algebraic_Closure
  imports Indexed_Polynomials Polynomial_Divisibility Pred_Zorn

begin

section \<open>Algebraic Closure\<close>

subsection \<open>Definitions\<close>

inductive iso_incl :: "'a ring \<Rightarrow> 'a ring \<Rightarrow> bool" (infixl "\<lesssim>" 65) for A B
  where iso_inclI [intro]: "id \<in> ring_hom A B \<Longrightarrow> iso_incl A B"

definition law_restrict :: "('a, 'b) ring_scheme \<Rightarrow> 'a ring"
  where "law_restrict R \<equiv> (ring.truncate R)
           \<lparr> mult := (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<otimes>\<^bsub>R\<^esub> b),
              add := (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<oplus>\<^bsub>R\<^esub> b) \<rparr>"

definition (in ring) \<sigma> :: "'a list \<Rightarrow> (('a list multiset) \<Rightarrow> 'a) list"
  where "\<sigma> P = map indexed_const P"

abbreviation (in ring) extensions :: "(('a list multiset) \<Rightarrow> 'a) ring set"
  where "extensions \<equiv> { L \<comment> \<open>such that\<close>.
           \<comment> \<open>i\<close>   (field L) \<and>
           \<comment> \<open>ii\<close>  (indexed_const \<in> ring_hom R L) \<and>
           \<comment> \<open>iii\<close> (\<forall>\<P> \<in> carrier L. carrier_coeff \<P>) \<and>
           \<comment> \<open>iv\<close>  (\<forall>\<P> \<in> carrier L. \<forall>P \<in> carrier (poly_ring R).
                       \<not> index_free \<P> P \<longrightarrow> \<X>\<^bsub>P\<^esub> \<in> carrier L \<and> (ring.eval L) (\<sigma> P) \<X>\<^bsub>P\<^esub> = \<zero>\<^bsub>L\<^esub>) }"

definition (in ring) range_extensions :: "(('a list multiset) \<Rightarrow> 'a) ring set" ("\<S>")
  where "\<S> = law_restrict ` extensions"


subsection \<open>Basic Properties\<close>

lemma (in ring) law_restrict_is_ring: "ring (law_restrict R)"
  by (unfold_locales) (auto simp add: law_restrict_def Units_def ring.defs,
      simp_all add: a_assoc a_comm m_assoc l_distr r_distr a_lcomm)

lemma (in field) law_restrict_is_field: "field (law_restrict R)"
proof -
  interpret L: ring "law_restrict R"
    using law_restrict_is_ring .
  have "inv a \<in> carrier R" and "a \<otimes> (inv a) = \<one>" if "a \<noteq> \<zero>" and "a \<in> carrier R" for a
    using that field_Units by auto
  thus ?thesis
    by (unfold_locales) (auto simp add: law_restrict_def Units_def ring.defs,
        simp_all add: m_comm integral_iff, blast)
qed

lemma law_restrict_iso_imp_eq:
  assumes "id \<in> ring_iso (law_restrict A) (law_restrict B)" and "ring A" and "ring B"
  shows "law_restrict A = law_restrict B"
proof -
  have "carrier A = carrier B"
    using ring_iso_memE(5)[OF assms(1)] unfolding bij_betw_def law_restrict_def by (simp add: ring.defs)
  hence mult: "a \<otimes>\<^bsub>law_restrict A\<^esub> b = a \<otimes>\<^bsub>law_restrict B\<^esub> b"
    and add:  "a \<oplus>\<^bsub>law_restrict A\<^esub> b = a \<oplus>\<^bsub>law_restrict B\<^esub> b" for a b
    using ring_iso_memE(2-3)[OF assms(1)] unfolding law_restrict_def by (auto simp add: ring.defs)
  have "monoid.mult (law_restrict A) = monoid.mult (law_restrict B)"
    using mult by auto
  moreover have "add (law_restrict A) = add (law_restrict B)"
    using add by auto
  moreover from \<open>carrier A = carrier B\<close> have "carrier (law_restrict A) = carrier (law_restrict B)"
    unfolding law_restrict_def by (simp add: ring.defs)
  moreover have "\<zero>\<^bsub>law_restrict A\<^esub> = \<zero>\<^bsub>law_restrict B\<^esub>"
    using ring_hom_zero[OF _ assms(2-3)[THEN ring.law_restrict_is_ring]] assms(1)
    unfolding ring_iso_def by auto
  moreover have "\<one>\<^bsub>law_restrict A\<^esub> = \<one>\<^bsub>law_restrict B\<^esub>"
    using ring_iso_memE(4)[OF assms(1)] by simp
  ultimately show ?thesis by simp
qed

lemma law_restrict_hom: "h \<in> ring_hom A B \<longleftrightarrow> h \<in> ring_hom (law_restrict A) (law_restrict B)"
proof
  assume "h \<in> ring_hom A B" thus "h \<in> ring_hom (law_restrict A) (law_restrict B)"
    by (auto intro!: ring_hom_memI dest: ring_hom_memE simp: law_restrict_def ring.defs)
next
  assume h: "h \<in> ring_hom (law_restrict A) (law_restrict B)" show "h \<in> ring_hom A B"
    using ring_hom_memE[OF h] by (auto intro!: ring_hom_memI simp: law_restrict_def ring.defs)
qed

lemma iso_incl_hom: "A \<lesssim> B \<longleftrightarrow> (law_restrict A) \<lesssim> (law_restrict B)"
  using law_restrict_hom iso_incl.simps by blast


subsection \<open>Partial Order\<close>

lemma iso_incl_backwards:
  assumes "A \<lesssim> B" shows "id \<in> ring_hom A B"
  using assms by cases

lemma iso_incl_antisym_aux:
  assumes "A \<lesssim> B" and "B \<lesssim> A" shows "id \<in> ring_iso A B"
proof -
  have hom: "id \<in> ring_hom A B" "id \<in> ring_hom B A"
    using assms(1-2)[THEN iso_incl_backwards] by auto
  thus ?thesis
    using hom[THEN ring_hom_memE(1)] by (auto simp add: ring_iso_def bij_betw_def inj_on_def)
qed

lemma iso_incl_refl: "A \<lesssim> A"
  by (rule iso_inclI[OF ring_hom_memI], auto)

lemma iso_incl_trans:
  assumes "A \<lesssim> B" and "B \<lesssim> C" shows "A \<lesssim> C"
  using ring_hom_trans[OF assms[THEN iso_incl_backwards]] by auto

lemma (in ring) iso_incl_antisym:
  assumes "A \<in> \<S>" "B \<in> \<S>" and "A \<lesssim> B" "B \<lesssim> A" shows "A = B"
proof -
  obtain A' B' :: "('a list multiset \<Rightarrow> 'a) ring"
    where A: "A = law_restrict A'" "ring A'" and B: "B = law_restrict B'" "ring B'"
    using assms(1-2) cring.axioms(1)[OF fieldE(1)] by (auto simp add: range_extensions_def)
  thus ?thesis
    using law_restrict_iso_imp_eq iso_incl_antisym_aux[OF assms(3-4)] by simp
qed

lemma (in ring) iso_incl_partial_order: "partial_order_on \<S> (rel_of (\<lesssim>) \<S>)"
  using iso_incl_refl iso_incl_trans iso_incl_antisym by (rule partial_order_on_rel_ofI)


subsection \<open>Extensions Non Empty\<close>

lemma (in ring) indexed_const_is_inj: "inj indexed_const"
  unfolding indexed_const_def by (rule inj_onI, metis)

lemma (in ring) indexed_const_inj_on: "inj_on indexed_const (carrier R)"
  unfolding indexed_const_def by (rule inj_onI, metis)

lemma (in field) extensions_non_empty: "\<S> \<noteq> {}"
proof -
  have "image_ring indexed_const R \<in> extensions"
  proof (auto)
    show "field (image_ring indexed_const R)"
      using inj_imp_image_ring_is_field[OF indexed_const_inj_on] .
  next
    show "indexed_const \<in> ring_hom R (image_ring indexed_const R)"
      using inj_imp_image_ring_iso[OF indexed_const_inj_on] unfolding ring_iso_def by auto
  next
    fix \<P> :: "('a list multiset) \<Rightarrow> 'a" and P
    assume "\<P> \<in> carrier (image_ring indexed_const R)"
    then obtain k where "k \<in> carrier R" and "\<P> = indexed_const k"
      unfolding image_ring_carrier by blast
    hence "index_free \<P> P" for P
      unfolding index_free_def indexed_const_def by auto
    thus "\<not> index_free \<P> P \<Longrightarrow> \<X>\<^bsub>P\<^esub> \<in> carrier (image_ring indexed_const R)"
     and "\<not> index_free \<P> P \<Longrightarrow> ring.eval (image_ring indexed_const R) (\<sigma> P) \<X>\<^bsub>P\<^esub> = \<zero>\<^bsub>image_ring indexed_const R\<^esub>"
      by auto
    from \<open>k \<in> carrier R\<close> and \<open>\<P> = indexed_const k\<close> show "carrier_coeff \<P>"
      unfolding indexed_const_def carrier_coeff_def by auto
  qed
  thus ?thesis
    unfolding range_extensions_def by blast
qed


subsection \<open>Chains\<close>

definition union_ring :: "(('a, 'c) ring_scheme) set \<Rightarrow> 'a ring"
  where "union_ring C = 
           \<lparr> carrier = (\<Union>(carrier ` C)),
         monoid.mult = (\<lambda>a b. (monoid.mult (SOME R. R \<in> C \<and> a \<in> carrier R \<and> b \<in> carrier R) a b)),
                 one = one (SOME R. R \<in> C),
                zero = zero (SOME R. R \<in> C),
                 add = (\<lambda>a b. (add (SOME R. R \<in> C \<and> a \<in> carrier R \<and> b \<in> carrier R) a b)) \<rparr>"


lemma union_ring_someI :
  assumes "\<And> R1 R2. R1 \<in> C \<Longrightarrow> R2 \<in> C \<Longrightarrow> R1 \<lesssim> R2 \<or> R2 \<lesssim> R1"
    and "x \<in> carrier (union_ring C)"
    and "y \<in> carrier (union_ring C)"
  shows "\<exists>R \<in> C.  x \<in> carrier R \<and> y \<in> carrier R"
proof-
  from assms obtain R1 R2 where hyp : "R1 \<in> C" "R2 \<in> C" "x \<in> carrier R1" "y \<in> carrier R2"
    unfolding union_ring_def by auto
  show ?thesis
  proof (cases " R1 \<lesssim> R2")
    case True
    hence "id \<in> ring_hom R1 R2"
      using iso_incl.cases by blast
    hence "x \<in> carrier R2" using ring_hom_memE(1) hyp(3) by fastforce
    then show ?thesis using hyp by auto
  next
    case False
    hence "R2 \<lesssim> R1" using hyp(1,2) assms(1) by auto
    hence "id \<in> ring_hom R2 R1"
      using iso_incl.cases by blast
    hence "y \<in> carrier R1" using ring_hom_memE(1) hyp(4) by fastforce
    then show ?thesis using hyp by auto
  qed
qed


corollary union_ring_same_laws :
  assumes "\<And> R1 R2. R1 \<in> C \<Longrightarrow> R2 \<in> C \<Longrightarrow> R1 \<lesssim> R2 \<or> R2 \<lesssim> R1"
    and "R1 \<in> C"
  shows "\<And> x y.  x \<in> carrier R1 \<Longrightarrow> y \<in> carrier R1 
     \<Longrightarrow> x \<otimes>\<^bsub>R1\<^esub> y = x \<otimes>\<^bsub>union_ring C\<^esub> y \<and> x \<oplus>\<^bsub>R1\<^esub> y = x \<oplus>\<^bsub>union_ring C\<^esub> y"
proof-
  fix x y assume hyp : "x \<in> carrier R1" "y \<in> carrier R1"
  obtain R2 where R2 : "R2 \<in> C""x \<in> carrier R2" "y \<in> carrier R2" "x \<oplus>\<^bsub>R2\<^esub> y = x \<oplus>\<^bsub>union_ring C\<^esub> y"
    using someI hyp assms(2) unfolding union_ring_def
    by (metis (full_types, lifting) ring_record_simps(12))
  obtain R3 where R3 : "R3 \<in> C" "x \<in> carrier R3" "y \<in> carrier R3" "x \<otimes>\<^bsub>R3\<^esub> y = x \<otimes>\<^bsub>union_ring C\<^esub> y"
    using someI_ex[of "\<lambda>R. R\<in>C \<and> x \<in> carrier R \<and> y \<in> carrier R"] union_ring_someI[OF assms(1)]
         hyp assms(2) unfolding union_ring_def by auto
  have "x \<oplus>\<^bsub>R1\<^esub> y = x \<oplus>\<^bsub>union_ring C\<^esub> y"
  proof (cases "R1 \<lesssim> R2")
    case True
    hence "id \<in> ring_hom R1 R2"
      using iso_incl.cases by blast
    then show ?thesis using hyp ring_hom_memE R2 by fastforce
  next
    case False
    hence "R2 \<lesssim> R1" using R2 assms(1,2) by auto
    hence "id \<in> ring_hom R2 R1"
      using iso_incl.cases by blast
    then show ?thesis using hyp R2 ring_hom_memE by fastforce
  qed
  moreover have "x \<otimes>\<^bsub>R1\<^esub> y = x \<otimes>\<^bsub>union_ring C\<^esub> y"
  proof  (cases "R1 \<lesssim> R3")
    case True
    hence "id \<in> ring_hom R1 R3"
      using iso_incl.cases by blast
    then show ?thesis using hyp ring_hom_memE R3 by fastforce
  next
    case False
    hence "R3 \<lesssim> R1" using R3 assms(1,2) by auto
    hence "id \<in> ring_hom R3 R1"
      using iso_incl.cases by blast
    then show ?thesis using hyp R3 ring_hom_memE by fastforce
  qed
  ultimately show "x \<otimes>\<^bsub>R1\<^esub> y = x \<otimes>\<^bsub>union_ring C\<^esub> y \<and> x \<oplus>\<^bsub>R1\<^esub> y = x \<oplus>\<^bsub>union_ring C\<^esub> y"
    by auto
qed

lemma union_ring_member_contains_all :
  assumes "\<forall> R \<in> C. field R"
    and "\<And> R1 R2. R1 \<in> C \<Longrightarrow> R2 \<in> C \<Longrightarrow> R1 \<lesssim> R2 \<or> R2 \<lesssim> R1"
    and "C \<noteq> {}"
    and "x \<in> carrier (union_ring C)"
    and "y \<in> carrier (union_ring C)"
    and "z \<in> carrier (union_ring C)"
  shows "\<exists> R \<in> C. x \<in> carrier R \<and> y \<in> carrier R \<and> z \<in> carrier R 
      \<and> \<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R\<^esub>  \<and> \<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R\<^esub>"
proof-
  from assms(3) have "\<exists> R. R \<in> C" by auto
  from this obtain Rzero Rone
      where hyp1 : "Rzero \<in> C""Rone \<in> C" "\<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>Rone\<^esub>" "\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>Rzero\<^esub>"
    using someI_ex[of "\<lambda>x. x \<in> C"] unfolding union_ring_def by auto
  hence "\<exists> R01 \<in> C. \<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R01\<^esub> \<and> \<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R01\<^esub>"
  proof (cases "Rzero \<lesssim> Rone ")
    case True
    hence "id \<in> ring_hom Rzero Rone"
      using iso_incl.cases by blast
    then show ?thesis using hyp1 
      by (metis eq_id_iff ring_hom_one)
  next
    case False
    hence "Rone \<lesssim> Rzero" using hyp1 assms(1,2) by auto
    hence "id \<in> ring_hom Rone Rzero"
      using iso_incl.cases by blast
    then show ?thesis using hyp1 ring_hom_memE by fastforce
  qed
  from this obtain R01 where R01 : "R01 \<in> C" "\<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R01\<^esub>" "\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R01\<^esub>"
    by auto
  from union_ring_someI[OF assms(2,4,5)] union_ring_someI[OF assms(2,5,6)] obtain R1 R2 
    where hyp2 :"R1 \<in> C""R2 \<in> C""x \<in> carrier R1""y \<in> carrier R1""y \<in> carrier R2""z \<in> carrier R2"
    by auto
  have "\<exists> Rxyz \<in> C. x \<in> carrier Rxyz \<and> y \<in> carrier Rxyz \<and> z \<in> carrier Rxyz"
  proof (cases "R1 \<lesssim> R2 ")
    case True
    hence "id \<in> ring_hom R1 R2"
      using iso_incl.cases by blast
    then show ?thesis using hyp2 ring_hom_memE(1) by fastforce
  next
    case False
    hence "R2 \<lesssim> R1" using hyp2(1,2) assms(2) by auto
    hence "id \<in> ring_hom R2 R1"
      using iso_incl.cases by blast
    then show ?thesis using hyp2 ring_hom_memE(1) by fastforce
  qed
  from this obtain Rxyz
    where Rxyz : "Rxyz \<in> C" "x \<in> carrier Rxyz" "y \<in> carrier Rxyz" "z \<in> carrier Rxyz" by auto
  show ?thesis
  proof (cases "R01 \<lesssim> Rxyz ")
    case True
    hence "id \<in> ring_hom R01 Rxyz"
      using iso_incl.cases by blast
    then show ?thesis using R01 Rxyz ring_hom_one ring_hom_zero assms(1)
      by (metis cring_def fieldE(1) id_apply) 
  next
    case False
    hence "Rxyz \<lesssim> R01" using Rxyz(1) R01(1) assms(2) by auto
    hence "id \<in> ring_hom Rxyz R01"
      using iso_incl.cases by blast
    then show ?thesis using R01 Rxyz ring_hom_memE(1)
      by (metis id_apply)
  qed
qed



lemma union_ring_is_ab_group :
  assumes "\<forall> R \<in> C. field R"
    and "\<And> R1 R2. R1 \<in> C \<Longrightarrow> R2 \<in> C \<Longrightarrow> R1 \<lesssim> R2 \<or> R2 \<lesssim> R1"
    and "C \<noteq> {}"
  shows "abelian_group (union_ring C)" 
proof (intro abelian_groupI)
  obtain R0 where R0 : "R0 \<in> C" "\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R0\<^esub>"
    using someI_ex[of "\<lambda>x. x \<in> C"] assms(3) unfolding union_ring_def by auto
  thus "\<zero>\<^bsub>union_ring C\<^esub> \<in> carrier (union_ring C)"
    using fieldE(1) assms(1)cring.cring_simprules(2) unfolding union_ring_def by (simp,blast)
  fix x y z assume hyp :  "x \<in> carrier (union_ring C)"
                          "y \<in> carrier (union_ring C)"
                          "z \<in> carrier (union_ring C)"
  from union_ring_member_contains_all[OF assms hyp] obtain R
    where R : "R \<in> C" "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R""\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R\<^esub>"
    by auto
  {fix a b assume hyp : "a \<in> carrier R" "b \<in> carrier R"
    have "a \<oplus>\<^bsub> R\<^esub> b = a \<oplus>\<^bsub>(union_ring C)\<^esub> b"
      using union_ring_same_laws[OF assms(2) R(1) hyp] by auto
  }
   note laws = this
  hence "x \<oplus>\<^bsub>(union_ring C)\<^esub> y \<in> carrier (R)"
    using assms(1) R(1-3) cring.cring_simprules(1) fieldE(1) by fastforce
  thus "x \<oplus>\<^bsub>(union_ring C)\<^esub> y \<in> carrier (union_ring C)" 
    using R(1) unfolding union_ring_def by auto
  from laws[OF R(3,2)] laws[OF R(2,3)] show "x \<oplus>\<^bsub>union_ring C\<^esub> y = y \<oplus>\<^bsub>union_ring C\<^esub> x"
    using cring.cring_simprules(10) R(1-3) fieldE(1) assms(1) by fastforce
  from R laws[of "\<zero>\<^bsub>R\<^esub>", OF _ R(2)] show "\<zero>\<^bsub>union_ring C\<^esub> \<oplus>\<^bsub>union_ring C\<^esub> x = x"
    using assms(1) by (simp add: cring.cring_simprules(2,8) fieldE(1))
  from laws[OF _ R(2)] have "\<exists>y\<in>carrier R. y \<oplus>\<^bsub>union_ring C\<^esub> x = \<zero>\<^bsub>union_ring C\<^esub>"
    using fieldE(1) assms(1) by (smt R(1,2,5) cring.cring_simprules(3,9))
  thus "\<exists>y\<in>carrier (union_ring C). y \<oplus>\<^bsub>union_ring C\<^esub> x = \<zero>\<^bsub>union_ring C\<^esub>"
    using laws[OF _ R(2)] R(1) unfolding union_ring_def by (simp,blast)
  show "x \<oplus>\<^bsub>union_ring C\<^esub> y \<oplus>\<^bsub>union_ring C\<^esub> z = x \<oplus>\<^bsub>union_ring C\<^esub> (y \<oplus>\<^bsub>union_ring C\<^esub> z)"
    using cring.cring_simprules(1,7) R assms(1)
    by (metis fieldE(1) laws)
qed

lemma union_ring_is_comm_monoid :
  assumes "\<forall> R \<in> C. field R"
    and "\<And> R1 R2. R1 \<in> C \<Longrightarrow> R2 \<in> C \<Longrightarrow> R1 \<lesssim> R2 \<or> R2 \<lesssim> R1"
    and "C \<noteq> {}"
  shows "comm_monoid (union_ring C)"
proof(intro comm_monoidI)
  obtain R0 where R0 : "R0 \<in> C" "\<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R0\<^esub>"
    using someI_ex[of "\<lambda>x. x \<in> C"] assms(3) unfolding union_ring_def by auto
  thus "\<one>\<^bsub>union_ring C\<^esub> \<in> carrier (union_ring C)"
    using fieldE(1) assms(1)cring.cring_simprules(6) unfolding union_ring_def by (simp,blast)
  fix x y z assume hyp :  "x \<in> carrier (union_ring C)"
                          "y \<in> carrier (union_ring C)"
                          "z \<in> carrier (union_ring C)"
  from union_ring_member_contains_all[OF assms hyp] obtain R
    where R : "R \<in> C" "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R""\<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R\<^esub>"
    by auto
  {fix a b assume hyp : "a \<in> carrier R" "b \<in> carrier R"
    have "a \<otimes>\<^bsub> R\<^esub> b = a \<otimes>\<^bsub>(union_ring C)\<^esub> b"
      using union_ring_same_laws[OF assms(2) R(1) hyp] by auto
  }
   note laws = this
  hence "x \<otimes>\<^bsub>(union_ring C)\<^esub> y \<in> carrier (R)"
    using assms(1) R(1-3) cring.cring_simprules(5) fieldE(1) by fastforce
  thus "x \<otimes>\<^bsub>(union_ring C)\<^esub> y \<in> carrier (union_ring C)" 
    using R(1) unfolding union_ring_def by auto
  from R laws[of "\<one>\<^bsub>R\<^esub>", OF _ R(2)] show "\<one>\<^bsub>union_ring C\<^esub> \<otimes>\<^bsub>union_ring C\<^esub> x = x"
    using assms(1) by (simp add : cring.cring_simprules(6,12) fieldE(1))
  show "x \<otimes>\<^bsub>union_ring C\<^esub> y \<otimes>\<^bsub>union_ring C\<^esub> z = x \<otimes>\<^bsub>union_ring C\<^esub> (y \<otimes>\<^bsub>union_ring C\<^esub> z)"
    using laws cring.cring_simprules(5,11) fieldE(1) assms(1) R(1-4) by (metis fieldE(1) laws)
  show "x \<otimes>\<^bsub>union_ring C\<^esub> y = y \<otimes>\<^bsub>union_ring C\<^esub> x"
    using cring.cring_simprules(14) fieldE(1) R assms(1) laws by fastforce
qed

lemma union_ring_is_cring :
  assumes "\<forall> R \<in> C. field R"
    and "\<And> R1 R2. R1 \<in> C \<Longrightarrow> R2 \<in> C \<Longrightarrow> R1 \<lesssim> R2 \<or> R2 \<lesssim> R1"
    and "C \<noteq> {}"
  shows "cring (union_ring C)" unfolding cring_def ring_def ring_axioms_def apply auto
proof-
  show "abelian_group (union_ring C)" using union_ring_is_ab_group assms by auto
  show "comm_monoid (union_ring C)" using union_ring_is_comm_monoid assms by auto
  thus "monoid (union_ring C)"unfolding comm_monoid_def by auto
  fix x y z assume hyp :  "x \<in> carrier (union_ring C)"
                          "y \<in> carrier (union_ring C)"
                          "z \<in> carrier (union_ring C)"
  from union_ring_member_contains_all[OF assms hyp] obtain R
    where R : "R \<in> C" "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R"
              "\<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R\<^esub>" "\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R\<^esub>"
    by auto
  {fix a b assume hyp : "a \<in> carrier R" "b \<in> carrier R"
    have "a \<otimes>\<^bsub> R\<^esub> b = a \<otimes>\<^bsub>(union_ring C)\<^esub> b" "a \<oplus>\<^bsub> R\<^esub> b = a \<oplus>\<^bsub>(union_ring C)\<^esub> b"
      using union_ring_same_laws[OF assms(2) R(1) hyp] by auto
  }
  note laws = this
  show "(x \<oplus>\<^bsub>union_ring C\<^esub> y) \<otimes>\<^bsub>union_ring C\<^esub> z = x \<otimes>\<^bsub>union_ring C\<^esub> z \<oplus>\<^bsub>union_ring C\<^esub> y \<otimes>\<^bsub>union_ring C\<^esub> z"
    using R assms(1) fieldE(1) laws by (metis cring.cring_simprules(1,5,13))
  show "z \<otimes>\<^bsub>union_ring C\<^esub> (x \<oplus>\<^bsub>union_ring C\<^esub> y) = z \<otimes>\<^bsub>union_ring C\<^esub> x \<oplus>\<^bsub>union_ring C\<^esub> z \<otimes>\<^bsub>union_ring C\<^esub> y"
    using R assms(1) fieldE(1) laws by (metis cring.cring_simprules(1,5,25))
qed

lemma union_ring_is_field :
  assumes "\<forall> R \<in> C. field R"
    and "\<And> R1 R2. R1 \<in> C \<Longrightarrow> R2 \<in> C \<Longrightarrow> R1 \<lesssim> R2 \<or> R2 \<lesssim> R1"
    and "C \<noteq> {}"
  shows "field (union_ring C)"
proof (intro cring.cring_fieldI)
  show cring : "cring (union_ring C)" using union_ring_is_cring assms by auto
  {fix x assume x : "x \<in> carrier (union_ring C) - {\<zero>\<^bsub>union_ring C\<^esub>}"
    have "x \<in> Units (union_ring C)" unfolding Units_def apply simp
    proof
      show "x \<in> carrier (union_ring C)" using x by auto
      from union_ring_member_contains_all[OF assms(1-3)this, of "\<one>\<^bsub>union_ring C\<^esub>" "\<one>\<^bsub>union_ring C\<^esub>"]
      obtain R where R : "R \<in> C" "x \<in> carrier R" "\<one>\<^bsub>R\<^esub> = \<one>\<^bsub>union_ring C\<^esub>" "\<zero>\<^bsub>R\<^esub> = \<zero>\<^bsub>union_ring C\<^esub>" 
        using cring.cring_simprules(6)[OF cring] assms x by fastforce
      {fix a b assume hyp : "a \<in> carrier R" "b \<in> carrier R"
        have "a \<otimes>\<^bsub> R\<^esub> b = a \<otimes>\<^bsub>(union_ring C)\<^esub> b"
          using union_ring_same_laws[OF assms(2) R(1) hyp ] by auto
      }
      note laws = this
      have "x \<in> carrier R - {\<zero>\<^bsub>R\<^esub>}" using x R by auto
      hence "x \<in> Units R" using fieldE(4) assms(1) R(1) by auto
      hence "\<exists>xa\<in>carrier R. xa \<otimes>\<^bsub>R\<^esub> x = \<one>\<^bsub>R\<^esub> \<and> x \<otimes>\<^bsub>R\<^esub> xa = \<one>\<^bsub>R\<^esub>"
        by (simp add: Units_def)
      thus "\<exists>xa\<in>carrier (union_ring C). xa \<otimes>\<^bsub>union_ring C\<^esub> x = \<one>\<^bsub>union_ring C\<^esub> \<and> x \<otimes>\<^bsub>union_ring C\<^esub> xa = \<one>\<^bsub>union_ring C\<^esub>"
        using laws R(1,2,3) fieldE(1) unfolding union_ring_def apply simp
        by blast
    qed
  }
  moreover have "\<zero>\<^bsub>union_ring C\<^esub> \<notin> Units (union_ring C)"
  proof
    assume hyp : "\<zero>\<^bsub>union_ring C\<^esub> \<in> Units (union_ring C)"
    obtain R0 where R0 : "R0 \<in> C" "\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R0\<^esub>"
      using someI_ex[of "\<lambda>x. x \<in> C"] assms(3) unfolding union_ring_def by auto
    thus False using fieldE(1,2) assms(1,3) cring hyp unfolding Units_def
      by (simp,smt cring.cring_simprules(27) monoid.simps(2) one_not_zero ring.simps(1)
         some_in_eq union_ring_def)
  qed
  hence "Units (union_ring C) \<subseteq> carrier (union_ring C) - {\<zero>\<^bsub>union_ring C\<^esub>}"
    unfolding Units_def by auto
  ultimately show "Units (union_ring C) = carrier (union_ring C) - {\<zero>\<^bsub>union_ring C\<^esub>}" by auto
qed

end