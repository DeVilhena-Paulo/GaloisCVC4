theory Generated_Fields

imports Multiplicative_Group Generated_Rings

begin


inductive_set
  generate_f :: "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for R and H where
    one:  "\<one>\<^bsub>R\<^esub> \<in> generate_f R H"
  | incl: "h \<in> H \<Longrightarrow> h \<in> generate_f R H"
  | a_inv: "h \<in> generate_f R H \<Longrightarrow> a_inv R h \<in> generate_f R H"
  | m_inv : "h \<in> (generate_f R H) \<and> (h \<noteq> \<zero>\<^bsub>R\<^esub>) \<Longrightarrow> m_inv R h \<in> generate_f R H"
  | eng_add : "h1 \<in> generate_f R H \<Longrightarrow> h2 \<in> generate_f R H \<Longrightarrow> h1 \<oplus>\<^bsub>R\<^esub> h2 \<in> generate_f R H"
  | eng_mult:  "h1 \<in> generate_f R H \<Longrightarrow> h2 \<in> generate_f R H \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 \<in> generate_f R H"

subsection\<open>Basic Properties of Generated Fields - First Part\<close>

lemma (in field) generate_f_in_carrier:
  assumes "H \<subseteq> carrier R"
  shows "h \<in> generate_f R H \<Longrightarrow> h \<in> carrier R"
  apply (induction rule: generate_f.induct)
  using assms field_Units group.inv_closed[OF field_mult_group]
  by blast+
       

lemma (in field) zero_in_generate :
"\<zero>\<^bsub>R\<^esub> \<in> generate_f R H"
  using one a_inv generate_f.eng_add one_closed r_neg
  by metis

lemma (in field) generate_f_is_add_subgroup :
  assumes "H \<subseteq> carrier R"
  shows "subgroup (generate_f R H) (add_monoid (R))"
  apply (unfold_locales)
  using generate_f_in_carrier[OF assms] a_inv unfolding a_inv_def
       apply (auto simp add : eng_add a_inv eng_mult zero_in_generate one incl)
  by fastforce


subsection \<open>Subfields\<close>

locale subfield = subring H R + subgroup "H - {\<zero>}" "mult_of R" for H and R (structure)


lemma (in field) subfieldI :
  assumes subset: "H \<subseteq> carrier R"
    and one: "\<one> \<in> H"
    and a_inv: "!!a. a \<in> H \<Longrightarrow> \<ominus> a \<in> H"
    and mult: "!!a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
    and add : "\<And> a b. \<lbrakk>a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> a \<oplus> b \<in> H"
    and m_inv_closed : "\<And> x. \<lbrakk>x \<in> H ; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> (inv x) \<in> H"
  shows "subfield H R"
proof (intro subfield.intro subgroup.intro)
  show "subring H R" using subringI assms by auto
  show H_mult_of : "H - {\<zero>} \<subseteq> carrier (mult_of R)" using subset by auto
  show "\<And>x y. x \<in> H - {\<zero>} \<Longrightarrow> y \<in> H - {\<zero>} \<Longrightarrow> x \<otimes>\<^bsub>mult_of R\<^esub> y \<in> H - {\<zero>}"
    using domain.integral_iff[OF domain_axioms] assms by auto
  show "\<one>\<^bsub>mult_of R\<^esub> \<in> H - {\<zero>}" using one by simp
  show "\<And>x. x \<in> H - {\<zero>} \<Longrightarrow> inv\<^bsub>mult_of R\<^esub> x \<in> H - {\<zero>}"
  proof-
    fix x assume x_def : "x \<in> H - {\<zero>}"
    from this have x_carrier : "x \<in> carrier (mult_of R)" using H_mult_of by auto
    hence "inv\<^bsub>mult_of R\<^esub> x \<in> carrier (mult_of R)"
      using group.inv_closed[OF field_mult_group] by auto
    moreover have "inv x \<in> H" using x_def m_inv_closed by auto
    hence "inv\<^bsub>mult_of R\<^esub> x \<in> H" unfolding mult_of_def  
      by (metis carrier_mult_of local.field_Units units_of_def units_of_inv x_carrier)
    ultimately show "inv\<^bsub>mult_of R\<^esub> x \<in> H - {\<zero>}" by auto
  qed
qed
     

lemma (in field)subfieldE :
  assumes "subfield H R"
  shows "H \<subseteq> carrier R"
    and "H \<noteq> {}"
    and "\<And>a. a \<in> H \<Longrightarrow> \<ominus> a \<in> H"
    and "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
    and "\<And> a b. \<lbrakk>a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> a \<oplus> b \<in> H"
    and "\<And> x. \<lbrakk>x \<in> H ; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> (inv x) \<in> H"
  using assms subring.subringE[of H R]
  unfolding subfield_def
       apply (auto simp add : a_inv_def subring.subringE[of H R] )
proof-
  fix x assume x_def : "x \<in> H"  "x \<noteq> \<zero>"
  show "inv x \<in> H"
    using x_def field_mult_group assms mult_of_is_Units units_of_inv subgroup.m_inv_closed subsetCE
    unfolding subfield_def
    by (smt Diff_empty Diff_insert0 \<open>subring H R\<Longrightarrow>H\<subseteq>carrier R\<close> insert_Diff insert_iff field_Units)
qed

lemma (in field) carrier_is_subfield :
"subfield (carrier R) R"
  apply (intro  subfieldI) using field_Units by simp_all

lemma (in subfield) subfield_is_field :
  assumes "field R"
  shows "field (R\<lparr>carrier := H\<rparr>)"
proof (intro fieldI cring.intro)
  show "ring (R\<lparr>carrier := H\<rparr>)" using subring_is_ring assms fieldE[OF assms] cring_def by auto
  show "Group.comm_monoid (R\<lparr>carrier := H\<rparr>)"
    using comm_monoid.submonoid_is_comm_monoid submonoid_axioms assms fieldE(1) cring.axioms(2)
    by blast
  show "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<noteq> \<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>" using assms fieldE(2) by auto
  show "\<And>a b. a \<otimes>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> b = \<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<Longrightarrow>a \<in> carrier (R\<lparr>carrier := H\<rparr>) \<Longrightarrow>
           b \<in> carrier (R\<lparr>carrier := H\<rparr>) \<Longrightarrow> a = \<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<or> b = \<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>"
    using fieldE[OF assms] by auto
  show "Units (R\<lparr>carrier := H\<rparr>) = carrier (R\<lparr>carrier := H\<rparr>) - {\<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>}"
  proof
    have "carrier (R\<lparr>carrier := H\<rparr>) - {\<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>} \<subseteq> Units (R\<lparr>carrier := H - {\<zero>}\<rparr>)"
      using group.Units[OF subgroup_is_group[OF field.field_mult_group[OF assms]]]
          field.mult_of_is_Units[OF assms] carrier_mult_of
      unfolding mult_of_def units_of_def Units_def  by simp
    also have "... \<subseteq> Units (R\<lparr>carrier := H\<rparr>)" unfolding Units_def by auto
    finally show "carrier (R\<lparr>carrier := H\<rparr>) - {\<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>} \<subseteq> Units (R\<lparr>carrier := H \<rparr>)".
    have "Units (R\<lparr>carrier := H\<rparr>) \<subseteq> carrier (R\<lparr>carrier := H\<rparr>)" unfolding Units_def by auto
    moreover have "\<zero> \<notin> Units (R\<lparr>carrier := H\<rparr>)"
      using one_not_zero[of R] assms semiring.l_null[of R] unfolding Units_def
      by (simp add: cring.cring_simprules(27) domain_def field_def)
    ultimately show "Units (R\<lparr>carrier := H\<rparr>) \<subseteq> carrier (R\<lparr>carrier := H\<rparr>) - {\<zero>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>}"
      by auto
  qed
qed
      
lemma (in field) field_incl_imp_subfield :
  assumes "H \<subseteq> carrier R"
    and "field (R\<lparr>carrier := H\<rparr>)"
  shows "subfield H R"
  apply (intro subfield.intro)
  using ring_incl_imp_subring assms ring_axioms fieldE(1) cring_def apply blast
proof( intro group.group_incl_imp_subgroup[OF field_mult_group, of "H - {\<zero>}" ])
  show "H - {\<zero>} \<subseteq> carrier (mult_of R)" using assms carrier_mult_of by auto
  have egal : "(mult_of R\<lparr>carrier := H - {\<zero>}\<rparr>)  = (mult_of (R\<lparr>carrier := H\<rparr>))"
    unfolding mult_of_def by simp
  thus "group (mult_of R\<lparr>carrier := H - {\<zero>}\<rparr>)"
    using field.field_mult_group[OF assms(2)]
    by (simp add : egal)
qed


lemma (in field) generate_f_is_subfield :
  assumes "H \<subseteq> (carrier R)"
  shows "subfield (generate_f R H) R"
proof (intro subfieldI)
  show "generate_f R H \<subseteq> carrier R" using generate_f_in_carrier assms by auto
  show "\<one> \<in> generate_f R H" using  one assms by auto
  show "\<And>a. a \<in> generate_f R H \<Longrightarrow> \<ominus> a \<in> generate_f R H" using a_inv[of _ R H] assms by auto 
  show "\<And>a b. a \<in> generate_f R H \<Longrightarrow> b \<in> generate_f R H \<Longrightarrow> a \<otimes> b \<in> generate_f R H"
    using eng_mult[of _ R H] assms by auto
  show "\<And>a b. a \<in> generate_f R H \<Longrightarrow> b \<in> generate_f R H \<Longrightarrow> a \<oplus> b \<in> generate_f R H"
    using eng_add[of _ R H] by auto
  show "\<And>x. x \<in> generate_f R H \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> inv x \<in> generate_f R H"
    using m_inv[of _ R H] by auto
qed

lemma (in field) generate_f_is_field :
  assumes "H \<subseteq> carrier R"
  shows "field (R\<lparr>carrier := generate_f R H\<rparr>)"
  by (intro subfield.subfield_is_field[OF generate_f_is_subfield[OF assms] field_axioms])


lemma (in field) generate_f_min_subfield1:
  assumes "H \<subseteq> carrier R"
    and "subfield E R" "H \<subseteq> E"
  shows "generate_f R H \<subseteq> E"
proof
  fix h show "h \<in> generate_f R H \<Longrightarrow> h \<in> E"
  proof (induct rule: generate_f.induct)
    case one  thus ?case
      using assms(2) submonoid.one_closed subfield.axioms(1) subring.axioms by blast
  next
    case incl thus ?case using assms(3) by blast
  next
    case a_inv thus ?case using assms(2)  subfieldE(3) by auto
  next
    case m_inv thus ?case using subfieldE(6)[OF assms(2)] by auto
  next
    case eng_add thus ?case
      using subfieldE(5)[OF assms(2)] by auto
  next
    case (eng_mult h1 h2) thus ?case
      using subfieldE(4)[OF assms(2)] by auto
  qed
qed

lemma (in field) generate_fI:
  assumes "H \<subseteq> carrier R"
    and "subfield E R" "H \<subseteq> E"
    and "\<And>K. \<lbrakk> subfield K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = generate_f R H"
proof
  show "E \<subseteq> generate_f R H"
    using assms generate_f_is_subfield generate_f.incl by (metis subset_iff)
  show "generate_f R H \<subseteq> E"
    using generate_f_min_subfield1[OF assms(1-3)] by simp
qed

lemma (in field) generate_fE:
  assumes "H \<subseteq> carrier R" and "E = generate_f R H"
  shows "subfield E R" and "H \<subseteq> E" and "\<And>K. \<lbrakk> subfield K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
proof -
  show "subfield E R" using assms generate_f_is_subfield by simp
  show "H \<subseteq> E" using assms(2) by (simp add: generate_f.incl subsetI)
  show "\<And>K. subfield K R  \<Longrightarrow> H \<subseteq> K \<Longrightarrow> E \<subseteq> K"
    using assms generate_f_min_subfield1 by auto
qed

lemma (in field) generate_f_min_subfield2:
  assumes "H \<subseteq> carrier R"
  shows "generate_f R H = \<Inter>{K. subfield K R \<and> H \<subseteq> K}"
proof
  have "subfield (generate_f R H) R \<and> H \<subseteq> generate_f R H"
    by (simp add: assms generate_fE(2) generate_f_is_subfield)
  thus "\<Inter>{K. subfield K R \<and> H \<subseteq> K} \<subseteq> generate_f R H" by blast
next
  have "\<And>K. subfield K R \<and> H \<subseteq> K \<Longrightarrow> generate_f R H \<subseteq> K"
    by (simp add: assms generate_f_min_subfield1)
  thus "generate_f R H \<subseteq> \<Inter>{K. subfield K R \<and> H \<subseteq> K}" by blast
qed

lemma (in field) mono_generate_f:
  assumes "I \<subseteq> J" and "J \<subseteq> carrier R"
  shows "generate_f R I \<subseteq> generate_f R J"
proof-
  have "I \<subseteq> generate_f R J "
    using assms generate_fE(2) by blast
  thus "generate_f R I \<subseteq> generate_f R J"
    using generate_f_min_subfield1[of I "generate_f R J"] assms generate_f_is_subfield[OF assms(2)]
    by blast
qed

lemma (in field) subfield_gen_incl :
  assumes "subfield H R"
    and  "subfield K R"
    and "I \<subseteq> H"
    and "I \<subseteq> K"
  shows "generate_f (R\<lparr>carrier := K\<rparr>) I \<subseteq> generate_f (R\<lparr>carrier := H\<rparr>) I"
proof
  {fix J assume J_def : "subfield J R" "I \<subseteq> J"
    have "generate_f (R \<lparr> carrier := J \<rparr>) I \<subseteq> J"
      using field.mono_generate_f[of "(R\<lparr>carrier := J\<rparr>)" I J ] subfield.subfield_is_field[OF J_def(1)]
          field.generate_f_in_carrier[of "R\<lparr>carrier := J\<rparr>"]  field_axioms J_def(2)
      by auto}
  note incl_HK = this
  {fix x have "x \<in> generate_f (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_f (R\<lparr>carrier := H\<rparr>) I" 
    proof (induction  rule : generate_f.induct)
      case one
        have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>" by simp
        moreover have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub>" by simp
        ultimately show ?case using assms generate_f.one by metis
    next
      case (incl h) thus ?case using generate_f.incl by force
    next
      case (a_inv h)
      note hyp = this
      have "a_inv (R\<lparr>carrier := K\<rparr>) h = a_inv R h" 
        using assms group.m_inv_consistent[of "add_monoid R" K] a_comm_group incl_HK[of K] hyp
        unfolding subfield_def comm_group_def a_inv_def subring_def by auto
      moreover have "a_inv (R\<lparr>carrier := H\<rparr>) h = a_inv R h"
        using assms group.m_inv_consistent[of "add_monoid R" H] a_comm_group incl_HK[of H] hyp
        unfolding subfield_def subring_def comm_group_def a_inv_def by auto
      ultimately show ?case using generate_f.a_inv a_inv.IH by fastforce
    next
      case (m_inv h) 
      note hyp = this
      have h_K : "h \<in> (K - {\<zero>})" using incl_HK[OF assms(2) assms(4)] hyp by auto
      hence "m_inv (R\<lparr>carrier := K\<rparr>) h = m_inv R h" 
        using  field.m_inv_mult_of[OF subfield.subfield_is_field[OF assms(2) field_axioms]]
               group.m_inv_consistent[of "mult_of R" "K - {\<zero>}"] field_mult_group 
        subfield.axioms(2)[OF assms(2)] unfolding mult_of_def apply simp
        by (metis h_K field_Units m_inv_mult_of mult_of_is_Units subgroup.mem_carrier units_of_def)
      moreover have h_H : "h \<in> (H - {\<zero>})" using incl_HK[OF assms(1) assms(3)] hyp by auto
      hence "m_inv (R\<lparr>carrier := H\<rparr>) h = m_inv R h"
        using  field.m_inv_mult_of[OF subfield.subfield_is_field[OF assms(1) field_axioms]]
               group.m_inv_consistent[of "mult_of R" "H - {\<zero>}"] field_mult_group 
        subfield.axioms(2)[OF assms(1)] unfolding mult_of_def apply simp
        by (metis h_H field_Units m_inv_mult_of mult_of_is_Units subgroup.mem_carrier units_of_def)
      ultimately show ?case using generate_f.m_inv m_inv.IH by fastforce
    next
      case (eng_add h1 h2)
      thus ?case using incl_HK assms generate_f.eng_add by force
    next
      case (eng_mult h1 h2)
      thus ?case using generate_f.eng_mult by force
    qed}
  thus "\<And>x. x \<in> generate_f (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_f (R\<lparr>carrier := H\<rparr>) I"
    by auto
qed

lemma (in field) subfield_gen_equality:
  assumes "subfield H R" "K \<subseteq> H"
  shows "generate_f R K = generate_f (R \<lparr> carrier := H \<rparr>) K"
  using subfield_gen_incl[OF assms(1)carrier_is_subfield assms(2)] assms subfieldE(1)
        subfield_gen_incl[OF carrier_is_subfield assms(1) _ assms(2)]
  by force

end


