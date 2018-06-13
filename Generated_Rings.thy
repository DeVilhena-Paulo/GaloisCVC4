theory Generated_Rings
  imports Ring
begin

section\<open>Generated Groups\<close>

inductive_set
  generate_r :: "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for R and H where
    one:  "\<one>\<^bsub>R\<^esub> \<in> generate_r R H"
  | incl: "h \<in> H \<Longrightarrow> h \<in> generate_r R H"
  | a_inv:  "h \<in> generate_r R H \<Longrightarrow> a_inv R h \<in> generate_r R H"
  | eng_add : "h1 \<in> generate_r R H \<Longrightarrow> h2 \<in> generate_r R H \<Longrightarrow> h1 \<oplus>\<^bsub>R\<^esub> h2 \<in> generate_r R H"
  | eng_mult:  "h1 \<in> generate_r R H \<Longrightarrow> h2 \<in> generate_r R H \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 \<in> generate_r R H"

subsection\<open>Basic Properties of Generated Rings - First Part\<close>

lemma (in ring) generate_r_in_carrier:
  assumes "H \<subseteq> carrier R"
  shows "h \<in> generate_r R H \<Longrightarrow> h \<in> carrier R"
  apply (induction rule: generate_r.induct) using assms 
  by blast+

lemma (in ring) zero_in_generate :
"\<zero>\<^bsub>R\<^esub> \<in> generate_r R H"
  using one a_inv
  by (metis generate_r.eng_add one_closed r_neg)

lemma (in ring) generate_r_is_ring :
  assumes "H \<subseteq> carrier R"
  shows "ring (R\<lparr>carrier := generate_r R H\<rparr>)"
  apply (unfold_locales)
  using  generate_r_in_carrier ringE[OF ring_axioms] assms abelian_groupE[OF abelian_group_axioms]
  using a_inv m_inv_def[of "add_monoid R"] a_inv_def[of R]
  unfolding Units_def
  apply (auto simp add : eng_add a_inv eng_mult zero_in_generate one incl m_assoc)
  by (smt r_neg a_inv)

subsection \<open>Subrings\<close>

locale subring = subgroup H "add_monoid R" + submonoid H R for H and R (structure)

lemma (in ring) subringI :
  assumes subset: "H \<subseteq> carrier R"
    and one: "\<one> \<in> H"
    and a_inv: "!!a. a \<in> H \<Longrightarrow> \<ominus> a \<in> H"
    and mult: "!!a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
    and add : "\<And> a b. \<lbrakk>a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> a \<oplus> b \<in> H"
  shows "subring H R"
  apply unfold_locales using assms  apply (simp_all add : a_inv_def)
  by fastforce

lemma (in subring) subringE :
  shows "H \<subseteq> carrier R"
    and "H \<noteq> {}"
    and "\<And>a. a \<in> H \<Longrightarrow> \<ominus> a \<in> H"
    and "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
    and "\<And> a b. \<lbrakk>a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> a \<oplus> b \<in> H"
  apply (auto simp add : a_inv_def)
  using  one_closed subgroup_is_submonoid submonoid.m_closed a_inv_def 
  by force+ 

lemma (in ring) carrier_is_subring :
"subring (carrier R) R"
  by (simp add: subringI)

lemma (in subring) subring_is_ring :
  assumes "ring R"
  shows "ring (R\<lparr>carrier := H\<rparr>)"
  apply unfold_locales
  using assms subring_axioms submonoid.one_closed[OF subgroup_is_submonoid] subgroup_is_group
  by (simp_all add: subringE  ring.ring_simprules abelian_group.a_group group.Units_eq ring_def)

lemma (in ring) ring_incl_imp_subring :
  assumes "H \<subseteq> carrier R"
    and "ring (R\<lparr>carrier := H\<rparr>)"
  shows "subring H R"
  apply (intro subring.intro)
  using group.group_incl_imp_subgroup[of "add_monoid R" H] assms ring_axioms monoid_incl_imp_submonoid
  unfolding ring_def abelian_group_def abelian_group_axioms_def comm_group_def by force+

lemma (in ring) generate_r_is_subring :
  assumes "H \<subseteq> (carrier R)"
  shows "subring (generate_r R H) R"
  apply (intro ring_incl_imp_subring)
  using  generate_r_in_carrier assms generate_r_is_ring by auto

lemma (in ring) generate_r_min_subring1:
  assumes "H \<subseteq> carrier R"
    and "subring E R" "H \<subseteq> E"
  shows "generate_r R H \<subseteq> E"
proof
  fix h show "h \<in> generate_r R H \<Longrightarrow> h \<in> E"
  proof (induct rule: generate_r.induct)
    case one  thus ?case
      using assms(2) submonoid.one_closed subring.axioms(2) by blast
  next
    case incl thus ?case using assms(3) by blast
  next
    case a_inv thus ?case using assms(2) by (simp add: subring.subringE(3))
  next
    case eng_add thus ?case
      using subring.subringE(5)[OF assms(2)] by auto
  next
    case (eng_mult h1 h2) thus ?case
      using subring.subringE(4)[OF assms(2)] by auto
  qed
qed

lemma (in ring) generate_rI:
  assumes "H \<subseteq> carrier R"
    and "subring E R" "H \<subseteq> E"
    and "\<And>K. \<lbrakk> subring K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = generate_r R H"
proof
  show "E \<subseteq> generate_r R H"
    using assms generate_r_is_subring generate_r.incl by (metis subset_iff)
  show "generate_r R H \<subseteq> E"
    using generate_r_min_subring1[OF assms(1-3)] by simp
qed

lemma (in ring) generate_rE:
  assumes "H \<subseteq> carrier R" and "E = generate_r R H"
  shows "subring E R" and "H \<subseteq> E" and "\<And>K. \<lbrakk> subring K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
proof -
  show "subring E R" using assms generate_r_is_subring by simp
  show "H \<subseteq> E" using assms(2) by (simp add: generate_r.incl subsetI)
  show "\<And>K. subring K R  \<Longrightarrow> H \<subseteq> K \<Longrightarrow> E \<subseteq> K"
    using assms generate_r_min_subring1 by auto
qed

lemma (in ring) generate_r_min_subring2:
  assumes "H \<subseteq> carrier R"
  shows "generate_r R H = \<Inter>{K. subring K R \<and> H \<subseteq> K}"
proof
  have "subring (generate_r R H) R \<and> H \<subseteq> generate_r R H"
    by (simp add: assms generate_rE(2) generate_r_is_subring)
  thus "\<Inter>{K. subring K R \<and> H \<subseteq> K} \<subseteq> generate_r R H" by blast
next
  have "\<And>K. subring K R \<and> H \<subseteq> K \<Longrightarrow> generate_r R H \<subseteq> K"
    by (simp add: assms generate_r_min_subring1)
  thus "generate_r R H \<subseteq> \<Inter>{K. subring K R \<and> H \<subseteq> K}" by blast
qed

lemma (in ring) mono_generate_r:
  assumes "I \<subseteq> J" and "J \<subseteq> carrier R"
  shows "generate_r R I \<subseteq> generate_r R J"
proof-
  have "I \<subseteq> generate_r R J "
    using assms generate_rE(2) by blast
  thus "generate_r R I \<subseteq> generate_r R J"
    using generate_r_min_subring1[of I "generate_r R J"] assms generate_r_is_subring[OF assms(2)]
    by blast
qed

lemma (in ring) subring_gen_incl :
  assumes "subring H R"
    and  "subring K R"
    and "I \<subseteq> H"
    and "I \<subseteq> K"
  shows "generate_r (R\<lparr>carrier := K\<rparr>) I \<subseteq> generate_r (R\<lparr>carrier := H\<rparr>) I"
proof
  {fix J assume J_def : "subring J R" "I \<subseteq> J"
    have "generate_r (R \<lparr> carrier := J \<rparr>) I \<subseteq> J"
      using ring.mono_generate_r[of "(R\<lparr>carrier := J\<rparr>)" I J ] subring.subring_is_ring[OF J_def(1)]
          ring.generate_r_in_carrier[of "R\<lparr>carrier := J\<rparr>"]  ring_axioms J_def(2)
      by auto}
  note incl_HK = this
  {fix x have "x \<in> generate_r (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_r (R\<lparr>carrier := H\<rparr>) I" 
    proof (induction  rule : generate_r.induct)
      case one
        have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>" by simp
        moreover have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub>" by simp
        ultimately show ?case using assms generate_r.one by metis
    next
      case (incl h) thus ?case using generate_r.incl by force
    next
      case (a_inv h)
      note hyp = this
      have "a_inv (R\<lparr>carrier := K\<rparr>) h = a_inv R h" 
        using assms group.m_inv_consistent[of "add_monoid R" K] a_comm_group incl_HK[of K] hyp
        unfolding subring_def comm_group_def a_inv_def by auto
      moreover have "a_inv (R\<lparr>carrier := H\<rparr>) h = a_inv R h"
        using assms group.m_inv_consistent[of "add_monoid R" H] a_comm_group incl_HK[of H] hyp
        unfolding subring_def comm_group_def a_inv_def by auto
      ultimately show ?case using generate_r.a_inv a_inv.IH by fastforce
    next
      case (eng_add h1 h2)
      thus ?case using incl_HK assms generate_r.eng_add by force
    next
      case (eng_mult h1 h2)
      thus ?case using generate_r.eng_mult by force
    qed}
  thus "\<And>x. x \<in> generate_r (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_r (R\<lparr>carrier := H\<rparr>) I"
    by auto
qed

lemma (in ring) subring_gen_equality:
  assumes "subring H R" "K \<subseteq> H"
  shows "generate_r R K = generate_r (R \<lparr> carrier := H \<rparr>) K"
  using subring_gen_incl[OF assms(1)carrier_is_subring assms(2)] assms subring.subringE(1)
        subring_gen_incl[OF carrier_is_subring assms(1) _ assms(2)]
  by force


