theory Space_Vectors

imports Module
begin

inductive_set
  Span :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> 'c set"
  for R and M and H where
    zero:  "\<zero>\<^bsub>M\<^esub> \<in> Span R M H"
  | incl: "h \<in> H \<Longrightarrow> h \<in> Span R M H"
  | a_inv : "h \<in> (Span R M H) \<Longrightarrow> a_inv M h \<in> Span R M H"
  | eng_add : "h1 \<in> Span R M H \<Longrightarrow> h2 \<in> Span R M H \<Longrightarrow> h1 \<oplus>\<^bsub>M\<^esub> h2 \<in> Span R M H"
  | eng_smult:  "h1 \<in> carrier R \<Longrightarrow> h2 \<in> Span R M H \<Longrightarrow> h1 \<odot>\<^bsub>M\<^esub> h2 \<in> Span R M H"

subsection\<open>Basic Properties of Generated Fields - First Part\<close>

lemma (in module) Span_in_carrier:
  assumes "H \<subseteq> carrier M"
  shows "h \<in> Span R M H \<Longrightarrow> h \<in> carrier M"
proof (induction rule: Span.induct)
  case zero
  then show ?case
    using a_comm_group monoid.one_closed[of M] unfolding comm_group_def comm_monoid_def by auto 
  next
  case (incl h)
  then show ?case using assms by auto
  next
  case (a_inv h)
  then show ?case using a_comm_group group.inv_closed unfolding comm_group_def by auto
  next
  case (eng_add h1 h2)
  then show ?case using a_comm_group monoid.m_closed
    unfolding comm_group_def comm_monoid_def by auto
  next
  case (eng_smult h1 h2)
  then show ?case using module_axioms unfolding module_def module_axioms_def by auto
qed
 


lemma (in module) Span_is_add_subgroup :
  assumes "H \<subseteq> carrier M"
  shows "subgroup (Span R M H) (add_monoid (M))"
 using zero[of M R H] Span_in_carrier assms eng_add[of _ R M H] a_inv[of _ R M H] a_inv_def[of M]
  by (auto intro! : subgroup.intro) 

subsection \<open>Submodules\<close>

locale submodule = subgroup H "add_monoid M" for H and R :: "('a, 'b) ring_scheme" and M (structure)
+ assumes smult_closed [simp, intro]:
      "\<lbrakk>a \<in> carrier R; x \<in> H\<rbrakk> \<Longrightarrow> a \<odot>\<^bsub>M\<^esub> x \<in> H"


lemma (in module) submoduleI :
  assumes subset: "H \<subseteq> carrier M"
    and zero: "\<zero>\<^bsub>M\<^esub> \<in> H"
    and a_inv: "!!a. a \<in> H \<Longrightarrow> \<ominus>\<^bsub>M\<^esub> a \<in> H"
    and add : "\<And> a b. \<lbrakk>a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> a \<oplus>\<^bsub>M\<^esub> b \<in> H"
    and smult_closed : "\<And> a x. \<lbrakk>a \<in> carrier R; x \<in> H\<rbrakk> \<Longrightarrow> a \<odot>\<^bsub>M\<^esub> x \<in> H"
  shows "submodule H R M"
  apply (intro submodule.intro subgroup.intro)
  using assms unfolding submodule_axioms_def 
  by (simp_all add : a_inv_def)


lemma (in module) submoduleE :
  assumes "submodule H R M"
  shows "H \<subseteq> carrier M"
    and "H \<noteq> {}"
    and "\<And>a. a \<in> H \<Longrightarrow> \<ominus>\<^bsub>M\<^esub> a \<in> H"
    and "\<And>a b. \<lbrakk>a \<in> carrier R; b \<in> H\<rbrakk> \<Longrightarrow> a \<odot>\<^bsub>M\<^esub> b \<in> H"
    and "\<And> a b. \<lbrakk>a \<in> H ; b \<in> H\<rbrakk> \<Longrightarrow> a \<oplus>\<^bsub>M\<^esub> b \<in> H"
    and "\<And> x. x \<in> H \<Longrightarrow> (a_inv M x) \<in> H"
  using group.subgroupE[of "add_monoid M" H, OF _ submodule.axioms(1)[OF assms]] a_comm_group
        submodule.smult_closed[OF assms]
  unfolding comm_group_def a_inv_def
  by auto


lemma (in module) carrier_is_submodule :
"submodule (carrier M) R M"
  apply (intro  submoduleI)
  using a_comm_group group.inv_closed unfolding comm_group_def a_inv_def group_def monoid_def
  by auto

lemma (in submodule) submodule_is_module :
  assumes "module R M"
  shows "module R (M\<lparr>carrier := H\<rparr>)"
proof (auto intro! : moduleI abelian_group.intro)
  show "cring (R)" using assms unfolding module_def by auto
  show "abelian_monoid (M\<lparr>carrier := H\<rparr>)"
    using comm_monoid.submonoid_is_comm_monoid[OF _ subgroup_is_submonoid] assms
    unfolding abelian_monoid_def module_def abelian_group_def
    by auto
  thus "abelian_group_axioms (M\<lparr>carrier := H\<rparr>)"
    using subgroup_is_group assms 
    unfolding abelian_group_axioms_def comm_group_def abelian_monoid_def module_def abelian_group_def
    by auto
  show "\<And>z. z \<in> H \<Longrightarrow> \<one>\<^bsub>R\<^esub> \<odot> z = z"
    using subgroup_imp_subset[OF subgroup_axioms] module.smult_one[OF assms]
    by auto
  fix a b x y assume a : "a \<in> carrier R" and b : "b \<in> carrier R" and x : "x \<in> H" and y : "y \<in> H"
  show "(a \<oplus>\<^bsub>R\<^esub> b) \<odot> x = a \<odot> x \<oplus> b \<odot> x"
    using a b x module.smult_l_distr[OF assms] subgroup_imp_subset[OF subgroup_axioms]
    by auto
  show "a \<odot> (x \<oplus> y) = a \<odot> x \<oplus> a \<odot> y"
    using a x y module.smult_r_distr[OF assms] subgroup_imp_subset[OF subgroup_axioms]
    by auto
  show "a \<otimes>\<^bsub>R\<^esub> b \<odot> x = a \<odot> (b \<odot> x)"
    using a b x module.smult_assoc1[OF assms] subgroup_imp_subset[OF subgroup_axioms]
    by auto
qed

      
lemma (in module) module_incl_imp_submodule :
  assumes "H \<subseteq> carrier M"
    and "module R (M\<lparr>carrier := H\<rparr>)"
  shows "submodule H R M"
  apply (intro submodule.intro)
  using add.group_incl_imp_subgroup[OF assms(1)] assms module.axioms(2)[OF assms(2)]
        module.smult_closed[OF assms(2)]
  unfolding abelian_group_def abelian_group_axioms_def comm_group_def submodule_axioms_def
  by simp_all

lemma (in module) Span_is_submodule :
  assumes "H \<subseteq> (carrier M)"
  shows "submodule (Span R M H) R M"
proof (intro submoduleI)
  show "Span R M H \<subseteq> carrier M" using Span_in_carrier assms by auto
  show "\<zero>\<^bsub>M\<^esub> \<in> Span R M H" using zero assms by auto
  show "\<And>a. a \<in> Span R M H \<Longrightarrow> \<ominus>\<^bsub>M\<^esub> a \<in> Span R M H" using a_inv[of _ R M H] assms by auto 
  show "\<And>a b. a \<in> Span R M H \<Longrightarrow> b \<in> Span R M H \<Longrightarrow> a \<oplus>\<^bsub>M\<^esub> b \<in> Span R M H"
    using eng_add[of _ R M H] by auto
  show "\<And>a x. a \<in> carrier R \<Longrightarrow> x \<in> Span R M H \<Longrightarrow> a \<odot>\<^bsub>M\<^esub> x \<in> Span R M H"
    using eng_smult[of _ R _ M H]  by auto
qed

lemma (in module) Span_is_module :
  assumes "H \<subseteq> carrier M"
  shows "module R (M\<lparr>carrier := Span R M H\<rparr>)"
  by (intro submodule.submodule_is_module[OF Span_is_submodule[OF assms] module_axioms])


lemma (in module) Span_min_submodule1:
  assumes "H \<subseteq> carrier M"
    and "submodule E R M" "H \<subseteq> E"
  shows "Span R M H \<subseteq> E"
proof
  fix h show "h \<in> Span R M H \<Longrightarrow> h \<in> E"
  proof (induct rule: Span.induct)
    case zero thus ?case
      using assms(2) subgroup.one_closed[of E "add_monoid M"] submodule.axioms(1) by auto
  next
    case incl thus ?case using assms(3) by blast
  next
    case a_inv thus ?case using assms(2)  submoduleE(3) by auto
  next
    case eng_add thus ?case
      using submoduleE(5)[OF assms(2)] by auto
  next
    case (eng_smult h1 h2) thus ?case
      using submoduleE(4)[OF assms(2)] by auto
  qed
qed

lemma (in module) SpanI:
  assumes "H \<subseteq> carrier M"
    and "submodule E R M" "H \<subseteq> E"
    and "\<And>K. \<lbrakk> submodule K R M; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = Span R M H"
proof
  show "E \<subseteq> Span R M H"
    using assms Span_is_submodule Span.incl by (metis subset_iff)
  show "Span R M H \<subseteq> E"
    using Span_min_submodule1[OF assms(1-3)] by simp
qed

lemma (in module) SpanE:
  assumes "H \<subseteq> carrier M" and "E = Span R M H"
  shows "submodule E R M" and "H \<subseteq> E" and "\<And>K. \<lbrakk> submodule K R M; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
proof -
  show "submodule E R M" using assms Span_is_submodule by simp
  show "H \<subseteq> E" using assms(2) by (simp add: Span.incl subsetI)
  show "\<And>K. submodule K R M \<Longrightarrow> H \<subseteq> K \<Longrightarrow> E \<subseteq> K"
    using assms Span_min_submodule1 by auto
qed

lemma (in module) Span_min_submodule2:
  assumes "H \<subseteq> carrier M"
  shows "Span R M H = \<Inter>{K. submodule K R M \<and> H \<subseteq> K}"
proof
  have "submodule (Span R M H) R M \<and> H \<subseteq> Span R M H"
    by (simp add: assms SpanE(2) Span_is_submodule)
  thus "\<Inter>{K. submodule K R M \<and> H \<subseteq> K} \<subseteq> Span R M H" by blast
next
  have "\<And>K. submodule K R M \<and> H \<subseteq> K \<Longrightarrow> Span R M H \<subseteq> K"
    by (simp add: assms Span_min_submodule1)
  thus "Span R M H \<subseteq> \<Inter>{K. submodule K R M \<and> H \<subseteq> K}" by blast
qed

lemma (in module) Span_idem :
  assumes "I \<subseteq> carrier M"
  shows "Span R M (Span R M I) = Span R M I"
proof
  show "Span R M I \<subseteq> Span R M (Span R M I)" using Span.incl by auto
  show "Span R M (Span R M I) \<subseteq> Span R M I"
    using Span_min_submodule1[of "Span R M I" "Span R M I"] assms
            Span_in_carrier Span_is_submodule[OF assms] by blast
qed

lemma (in module) Span_mono:
  assumes "I \<subseteq> J" "J \<subseteq> carrier M"
  shows "Span R M I \<subseteq> Span R M J"
proof-
  have "I \<subseteq> Span R M J"
    using assms SpanE(2) by blast
  thus "Span R M I \<subseteq> Span R M J"
    using Span_min_submodule1[of I "Span R M J"] assms Span_is_submodule[OF assms(2)]
    by blast
qed

lemma (in module) Span_union :
  assumes "Span R M I = Span R M J"
    and "I \<subseteq> carrier M"
    and "J \<subseteq> carrier M"
    and "K \<subseteq> carrier M"
  shows "Span R M (I \<union> K) = Span R M (J \<union> K)"
proof-
  {fix H L assume HL : "H \<subseteq> carrier M" "L \<subseteq> carrier M" "Span R M H = Span R M L"
    have "Span R M (H \<union> K) \<subseteq> Span R M (L \<union> K)"
    proof-
      have "H \<subseteq> Span R M L" using HL Span.incl[of _ H R M] by auto
      also have "Span R M L \<subseteq> Span R M (L \<union> K)" using Span_mono HL assms(4) by auto
      finally have H : "H \<subseteq> Span R M (L \<union> K)" by simp
      have "K \<subseteq> Span R M K" using Span.incl by auto
      also have "Span R M K \<subseteq> Span R M (L \<union> K)" using Span_mono HL(2) assms(4) by auto
      finally have "K \<subseteq> Span R M (L \<union> K)" by simp
      hence "(H \<union> K) \<subseteq> Span R M (L \<union> K)"
        using Span.incl[of _ H R M] H by auto
      hence "Span R M (H \<union> K) \<subseteq> Span R M (Span R M (L \<union> K))"
        using Span_mono[of "H \<union> K" "Span R M (L \<union> K)"] Span_in_carrier HL(2) assms(4) by blast
      thus "Span R M (H \<union> K) \<subseteq> Span R M (L \<union> K)"
        using Span_idem[of "L \<union> K"] HL assms(4) by auto
    qed}
  thus "Span R M (I \<union> K) = Span R M (J \<union> K)" using assms by auto
qed

lemma (in module) submodule_gen_incl :
  assumes "submodule H R M"
    and  "submodule K R M"
    and "I \<subseteq> H"
    and "I \<subseteq> K"
  shows "Span R (M\<lparr>carrier := K\<rparr>) I \<subseteq> Span R (M\<lparr>carrier := H\<rparr>) I"
proof
  {fix J assume J_def : "submodule J R M" "I \<subseteq> J"
    have "Span R (M \<lparr>carrier := J\<rparr>) I \<subseteq> J"
      using module.Span_mono[of R "(M\<lparr>carrier := J\<rparr>)" I J ] submodule.submodule_is_module[OF J_def(1)]
          module.Span_in_carrier[of R "M\<lparr>carrier := J\<rparr>"]  module_axioms J_def(2)
      by auto}
  note incl_HK = this
  {fix x have "x \<in> Span R (M\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> Span R (M\<lparr>carrier := H\<rparr>) I" 
    proof (induction  rule : Span.induct)
      case zero
        have "\<zero>\<^bsub>M\<lparr>carrier := H\<rparr>\<^esub> \<oplus>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<lparr>carrier := K\<rparr>\<^esub> = \<zero>\<^bsub>M\<lparr>carrier := H\<rparr>\<^esub>" by simp
        moreover have "\<zero>\<^bsub>M\<lparr>carrier := H\<rparr>\<^esub> \<oplus>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<lparr>carrier := K\<rparr>\<^esub> = \<zero>\<^bsub>M\<lparr>carrier := K\<rparr>\<^esub>" by simp
        ultimately show ?case using assms Span.zero by metis
    next
      case (incl h) thus ?case using Span.incl by force
    next
      case (a_inv h)
      note hyp = this
      have "a_inv (M\<lparr>carrier := K\<rparr>) h = a_inv M h" 
        using assms group.m_inv_consistent[of "add_monoid M" K] a_comm_group incl_HK[of K] hyp
        unfolding submodule_def comm_group_def a_inv_def  by auto
      moreover have "a_inv (M\<lparr>carrier := H\<rparr>) h = a_inv M h"
        using assms group.m_inv_consistent[of "add_monoid M" H] a_comm_group incl_HK[of H] hyp
        unfolding submodule_def comm_group_def a_inv_def by auto
      ultimately show ?case using Span.a_inv a_inv.IH by fastforce
    next
      case (eng_add h1 h2)
      thus ?case using incl_HK assms Span.eng_add by force
    next
      case (eng_smult h1 h2)
      thus ?case using Span.eng_smult by force
    qed}
  thus "\<And>x. x \<in> Span R (M\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> Span R (M\<lparr>carrier := H\<rparr>) I"
    by auto
qed

lemma (in module) submodule_gen_equality:
  assumes "submodule H R M" "K \<subseteq> H"
  shows "Span R M K = Span R (M \<lparr> carrier := H \<rparr>) K"
  using submodule_gen_incl[OF assms(1)carrier_is_submodule assms(2)] assms submoduleE(1)
        submodule_gen_incl[OF carrier_is_submodule assms(1) _ assms(2)]
  by force

locale vector_space = module + field R


abbreviation
generator :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> 'c set \<Rightarrow> bool"
  where "generator R M K A \<equiv> A \<subseteq> K \<and> Span R M A = K"

abbreviation finite_dim :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> bool"
  where "finite_dim R M \<equiv> \<exists> A. finite A \<and> generator R M (carrier M) A"

abbreviation lin_dep :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "lin_dep R M A \<equiv> A \<subseteq> carrier M \<and> (\<exists> S. (S \<subset> A) \<and> Span R M S = Span R M A)" 

abbreviation lin_indep :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "lin_indep R M A \<equiv> A \<subseteq> carrier M \<and> (\<forall> S. (S \<subset> A) \<longrightarrow> Span R M S \<subset> Span R M A)"

abbreviation base :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "base R M A \<equiv> lin_indep R M A \<and> generator R M (carrier M) A"

definition (in vector_space) dim :: "'c set \<Rightarrow> nat"
  where "dim K \<equiv> LEAST n. (\<exists> A. card A = n  \<and>  generator R M K A)"

lemma (in vector_space) lin_indep_not_dep:
  assumes "A \<subseteq> carrier M"
  shows "lin_dep R M A \<longleftrightarrow> \<not>lin_indep R M A" 
proof
  assume "lin_dep R M A"
  hence "\<not> (\<forall> S. (S \<subset> A) \<longrightarrow> Span R M S \<subset> Span R M A)" using assms
    by blast
  thus "\<not>lin_indep R M A" by auto
next
  assume "\<not> lin_indep R M A"
  from this obtain S where S_def : "(S \<subset> A)" "\<not> (Span R M S \<subset> Span R M A)" using assms by blast
  moreover have "Span R M S \<subseteq> Span R M A" using S_def(1) Span_mono[of S A] assms by auto
  ultimately show "lin_dep R M A" using assms  by blast
qed

lemma (in module) finsum_smult_ldistr:
  "\<lbrakk> finite A; a \<in> carrier R; f: A \<rightarrow> carrier M \<rbrakk> \<Longrightarrow>
     a \<odot>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub> i \<in> A. (f i)) = (\<Oplus>\<^bsub>M\<^esub> i \<in> A. ( a \<odot>\<^bsub>M\<^esub> (f i)))"
proof (induct set: finite)
  case empty then show ?case
    by (metis M.finsum_empty M.zero_closed R.zero_closed r_null smult_assoc1 smult_zero)
next
  case (insert x F) then show ?case 
    by (simp add: Pi_def smult_r_distr)
qed


lemma (in vector_space) h_in_finite_span :
  assumes "A \<subseteq> carrier M" and "h \<in> Span R M A"
  shows "\<exists>S \<subseteq> A. finite S \<and> h \<in> Span R M S" using assms(2)
proof (induction rule : Span.induct)
  case zero
  then show ?case
    using Span.zero by auto 
next
  case (incl h)
  then show ?case using Span.incl[of h "{h}"]
    by auto
next
  case (a_inv h)
  then show ?case by (meson Span.a_inv)
next
  case (eng_add h1 h2)
  from this obtain S1 S2 where S1_def : "S1 \<subseteq>A \<and> finite S1 \<and> h1 \<in> Span R M S1"
                and S2_def : "S2 \<subseteq> A \<and> finite S2 \<and> h2 \<in> Span R M S2" by auto
  then show ?case
    using Span.eng_add[of _ R M "S1 \<union> S2"] Span_mono[of _ "S1 \<union> S2"]assms Span_mono[of _ "S1 \<union> S2"]
    by (smt finite_UnI le_supI subsetCE subset_trans sup_ge1 sup_ge2)
next
  case (eng_smult h1 h2)
  then show ?case using Span.eng_smult[of h1 R h2 M] by auto
qed

lemma (in vector_space) linear_combinations_finite_incl :
  assumes "finite A" and "A \<subseteq> carrier M" 
  shows "h \<in> Span R M A \<Longrightarrow> h \<in> { \<Oplus>\<^bsub>M\<^esub>s \<in> A. (f s) \<odot>\<^bsub>M\<^esub>  s | f. f: A \<rightarrow> carrier R }"
proof (induction rule : Span.induct)
  have "\<And>v. v \<in> A \<Longrightarrow> (\<lambda>v. \<zero>) v \<odot>\<^bsub>M\<^esub> v = \<zero>\<^bsub>M\<^esub>" using assms smult_zero by auto
  hence sum_zero : "(\<Oplus>\<^bsub>M\<^esub>i\<in>A. \<zero>\<^bsub>M\<^esub>) = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. ((\<lambda>v. \<zero>) v) \<odot>\<^bsub>M\<^esub> v) "
  proof (induct A rule: infinite_finite_induct)
    case (infinite A)
    then show ?case using assms by auto
  next
    case empty
    then show ?case by auto
  next
    case (insert x F)
    then show ?case by (metis M.finsum_cong' Pi_I M.zero_closed)
  qed
  case zero
  have "(\<lambda>v. \<zero>) \<in> A \<rightarrow> carrier R" by auto
  thus ?case
    using finsum_zero sum_zero by auto
next
  case (incl h)
  note hyp = this
  have "(\<lambda>x. ((\<lambda>v. if v = h then \<one> else \<zero>) x) \<odot>\<^bsub>M\<^esub> x) \<in> A \<rightarrow> carrier M"
    using smult_closed assms by auto
  moreover have "(if h = h then \<one> else \<zero>) \<odot>\<^bsub>M\<^esub> h \<in> carrier M"
    using assms smult_closed one_closed hyp by auto
  moreover have null : "\<And>x. x\<in> (A - {h}) \<Longrightarrow> (\<lambda>v. if v = h then \<one> else \<zero>) x = (\<lambda>v. \<zero>) x" by auto
  hence "\<And>x. x\<in> (A - {h}) \<Longrightarrow> (\<lambda>y. ((\<lambda>v. if v = h then \<one> else \<zero>) y) \<odot>\<^bsub>M\<^esub> y) x = (\<lambda>v. \<zero>\<^bsub>M\<^esub>) x"
    using smult_zero assms by auto
  hence "(\<Oplus>\<^bsub>M\<^esub>v\<in>(A - {h}). ((\<lambda>v. if v = h then \<one> else \<zero>) v) \<odot>\<^bsub>M\<^esub> v) = \<zero>\<^bsub>M\<^esub>"
    using  M.finsum_cong'[of "A - {h}" "A - {h}" "\<lambda>x. ((\<lambda>v. if v = h then \<one> else \<zero>) x) \<odot>\<^bsub>M\<^esub> x"
           "\<lambda>v. \<zero>\<^bsub>M\<^esub>"] finsum_zero[of "A - {h}"]
    by (metis (no_types, lifting) M.zero_closed Pi_I)
  ultimately  have "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. ((\<lambda>v. if v = h then \<one> else \<zero>) v) \<odot>\<^bsub>M\<^esub> v) = h"
    using finsum_insert[of "A - {h}" h "\<lambda>x. ((\<lambda>v. if v = h then \<one> else \<zero>) x) \<odot>\<^bsub>M\<^esub> x"]
    by (smt M.r_zero Pi_split_insert_domain assms finite_Diff incl.hyps insert_Diff null
        smult_one subsetCE zero_not_one)
  moreover have "(\<lambda>v. if v = h then \<one> else \<zero>) \<in> A \<rightarrow> carrier R" by auto
  ultimately have  "(\<lambda>v. if v = h then \<one> else \<zero>) \<in> A \<rightarrow> carrier R \<and>
                    h = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. (\<lambda>v. if v = h then \<one> else \<zero>) v \<odot>\<^bsub>M\<^esub> v)"  using hyp by auto
  thus ?case by fastforce
  next
    case (a_inv h)
    note hyp = this
    from this obtain a where a_def : "a \<in> A \<rightarrow> carrier R" " h = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a v \<odot>\<^bsub>M\<^esub> v)" by auto
  define f where f_def : "f =(\<lambda>v. \<ominus> \<one> \<otimes> a v)"
  have " (\<Oplus>\<^bsub>M\<^esub>v\<in>A. (\<ominus> \<one>) \<odot>\<^bsub>M\<^esub> ((a v) \<odot>\<^bsub>M\<^esub> v)) = (\<ominus>\<one>) \<odot>\<^bsub>M\<^esub> h"
    using module.finsum_smult_ldistr[OF module_axioms assms(1), of "(\<ominus>\<one>)" "\<lambda>v. a v \<odot>\<^bsub>M\<^esub> v"] a_def
    by (smt Pi_def R.add.inv_closed assms(2) mem_Collect_eq one_closed smult_closed subsetCE)
  also have "... = \<ominus>\<^bsub>M\<^esub> h"
    using smult_l_opposite smult_one Span_in_carrier hyp assms by auto
  finally have "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. (\<ominus> \<one>) \<odot>\<^bsub>M\<^esub> ((a v) \<odot>\<^bsub>M\<^esub> v)) =  \<ominus>\<^bsub>M\<^esub> h" by auto
  moreover have "\<And>v. v \<in> A \<Longrightarrow> (\<ominus> \<one>) \<odot>\<^bsub>M\<^esub> ((a v) \<odot>\<^bsub>M\<^esub> v) =  (f v \<odot>\<^bsub>M\<^esub> v) "
    using one_closed a_def assms(2) unfolding f_def
    by (metis (no_types, lifting) PiE R.add.inv_closed smult_assoc1 subsetCE)
  hence "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. (\<ominus> \<one>) \<odot>\<^bsub>M\<^esub> ((a v) \<odot>\<^bsub>M\<^esub> v)) = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. (f v \<odot>\<^bsub>M\<^esub> v))"
    using M.finsum_cong'[of A A "\<lambda>v. \<ominus> \<one> \<odot>\<^bsub>M\<^esub> (a v \<odot>\<^bsub>M\<^esub> v)" "\<lambda>v. (f v \<odot>\<^bsub>M\<^esub> v)"]
           smult_closed a_def one_closed R.add.inv_closed unfolding f_def
    by (smt PiE Pi_I assms(2) subsetCE)
  ultimately have "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. f v \<odot>\<^bsub>M\<^esub> v) = \<ominus>\<^bsub>M\<^esub> h" by auto
  moreover have "f \<in> A \<rightarrow> carrier R"
    using f_def a_def(1) m_closed[of "\<ominus> \<one>"] R.add.inv_closed[OF one_closed]
    by blast
  ultimately show ?case
    using Pi_iff by fastforce
next
  case (eng_add h1 h2)
  note hyp = this
  from hyp obtain a1 where a1_def : "a1 \<in> A \<rightarrow> carrier R" "h1 = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a1 v \<odot>\<^bsub>M\<^esub> v)" by auto
  hence a1_M : "(\<lambda>v. a1 v \<odot>\<^bsub>M\<^esub> v) \<in> A \<rightarrow> carrier M"
    using smult_closed assms by blast
  from hyp obtain a2 where a2_def : "a2 \<in> A \<rightarrow> carrier R" "h2 = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a2 v \<odot>\<^bsub>M\<^esub> v)" by auto
  hence a2_M : "(\<lambda>v. a2 v \<odot>\<^bsub>M\<^esub> v) \<in> A \<rightarrow> carrier M"
    using smult_closed assms by blast
  define f where f_def : "f =(\<lambda>v. (a1 v \<oplus> a2 v))"
  from this have fprop : "f \<in> A \<rightarrow> carrier R" using a1_def a2_def R.a_closed by auto
  hence f_M : "(\<lambda>v. f v \<odot>\<^bsub>M\<^esub> v) \<in> A \<rightarrow> carrier M"
    using smult_closed assms(2) by blast
  moreover have "\<And>i. i \<in> A \<Longrightarrow> (a1 i \<odot>\<^bsub>M\<^esub> i \<oplus>\<^bsub>M\<^esub> a2 i \<odot>\<^bsub>M\<^esub> i) = (f i \<odot>\<^bsub>M\<^esub> i) "
    unfolding f_def using smult_l_distr a1_def a2_def assms(2)
    by (smt Pi_iff restrict_ext subsetCE) 
  hence "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. f v \<odot>\<^bsub>M\<^esub> v) = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a1 v \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> a2 v \<odot>\<^bsub>M\<^esub> v)"
    by (metis (mono_tags, lifting) M.finsum_cong' f_M)
  moreover have "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. a1 v \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> a2 v \<odot>\<^bsub>M\<^esub> v) =
                 (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a1 v \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a2 v \<odot>\<^bsub>M\<^esub> v)"
    using finsum_addf[OF a1_M a2_M ] restrict_Pi_cancel by auto
  ultimately have "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. f v \<odot>\<^bsub>M\<^esub> v) = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a1 v \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a2 v \<odot>\<^bsub>M\<^esub> v)"
    by auto
  hence "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. f v \<odot>\<^bsub>M\<^esub> v) = h1 \<oplus>\<^bsub>M\<^esub> h2" using a1_def a2_def by auto
  then show ?case
    using fprop Pi_iff by fastforce
next
  case (eng_smult h1 h2)
  note hyp = this
  from this obtain a where a_def : " a \<in> A \<rightarrow> carrier R" "h2 = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a v \<odot>\<^bsub>M\<^esub> v)" by auto
  hence a_M : "(\<lambda>v. a v \<odot>\<^bsub>M\<^esub> v) \<in> A \<rightarrow> carrier M"
    using smult_closed assms by blast
  hence "h1 \<odot>\<^bsub>M\<^esub> h2 = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. h1 \<odot>\<^bsub>M\<^esub> (a v \<odot>\<^bsub>M\<^esub> v))"
    using finsum_smult_ldistr[OF assms(1) hyp(1) a_M] a_def(2) by blast
  moreover have "\<And>v. v \<in> A \<Longrightarrow> h1 \<odot>\<^bsub>M\<^esub> (a v \<odot>\<^bsub>M\<^esub> v) = ((h1 \<otimes> a v) \<odot>\<^bsub>M\<^esub> v)"
    using smult_assoc1[OF hyp(1)] a_def(1) assms(2)
    by (simp add: Pi_iff subset_eq) 
  hence "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. h1 \<odot>\<^bsub>M\<^esub> (a v \<odot>\<^bsub>M\<^esub> v)) = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. ((h1 \<otimes> a v) \<odot>\<^bsub>M\<^esub> v))"
    using finsum_cong'[of A A] a_M
    by (smt Pi_iff local.eng_smult(1) smult_closed)
  ultimately have "h1 \<odot>\<^bsub>M\<^esub> h2 = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. h1 \<otimes> a v \<odot>\<^bsub>M\<^esub> v)" by auto
  moreover have "(\<lambda>v. h1 \<otimes> a v) \<in> A \<rightarrow> carrier R"
    using a_def(1) smult_closed m_closed hyp assms
    by fastforce 
  ultimately show ?case by auto
qed

lemma (in vector_space) linear_combinations_incl :
  assumes "A \<subseteq> carrier M"
  shows "Span R M A  \<subseteq> { \<Oplus>\<^bsub>M\<^esub>s \<in> S. (a s) \<odot>\<^bsub>M\<^esub>  s | a S. a \<in> S \<rightarrow> carrier R \<and> finite S \<and> S \<subseteq> A}"
proof
  fix h assume h_def : "h \<in> Span R M A"
  obtain S where S_def : "S \<subseteq> A" "finite S" "h \<in> Span R M S"
    using h_in_finite_span[OF assms h_def] by auto
  from this obtain a where a_def : " a \<in> S \<rightarrow> carrier R \<and> ( h = (\<Oplus>\<^bsub>M\<^esub>v\<in>S. a v \<odot>\<^bsub>M\<^esub> v))"
    using linear_combinations_finite_incl[OF S_def(2) _ S_def(3)] assms S_def by auto
  thus " h \<in> {\<Oplus>\<^bsub>M\<^esub>s \<in> S. (a s) \<odot>\<^bsub>M\<^esub>  s | a S. a \<in> S \<rightarrow> carrier R \<and> finite S \<and> S \<subseteq> A}"
    using S_def by auto
qed


lemma (in vector_space) linear_combinations_finite_incl2 :
  assumes "finite A" and "A \<subseteq> carrier M" 
  shows "{ \<Oplus>\<^bsub>M\<^esub>s \<in> A. (a s) \<odot>\<^bsub>M\<^esub>  s | a. a: A \<rightarrow> carrier R } \<subseteq>  Span R M A"
        (is " { ?sum M A a  |a. a \<in> ?A_to_R } \<subseteq> Span R M A ")
proof
  fix x assume x_def : "x \<in> {\<Oplus>\<^bsub>M\<^esub>s\<in>A. a s \<odot>\<^bsub>M\<^esub> s |a. a \<in> A \<rightarrow> carrier R}"
  from this obtain a where a_def : "a \<in> ?A_to_R" "x = ?sum M A a" by auto
  show "x \<in> Span R M A" using assms a_def
  proof (induction A arbitrary : x a)
    case empty
    then show ?case using finsum_empty Span.zero[of M R "{}"]
      by simp 
  next
    case (insert xa F)
    define y z where y_def : "y = ?sum M F a" and z_def : "z = a xa \<odot>\<^bsub>M\<^esub> xa"
    from insert(5) have "a \<in> F \<rightarrow> carrier R " by auto
    hence "y \<in> Span R M F" using y_def insert by auto
    hence "y \<in> Span R M (insert xa F)" using Span_mono insert by blast 
    moreover have "z \<in> Span R M (insert xa F)"
      using Span.eng_smult Span.incl[of xa "insert xa F" R M] insert(5) z_def  by auto
    moreover have "x = y \<oplus>\<^bsub>M\<^esub> z"
      unfolding y_def z_def using insert finsum_insert[OF insert(1)insert(2)]
      by (simp add: M.add.m_comm Pi_iff subset_eq)
    ultimately show ?case using Span.eng_add[of y R M "insert xa F" z] by auto
  qed
qed

lemma (in vector_space) linear_combinations_incl2 :
  assumes "A \<subseteq> carrier M" 
  shows "{ \<Oplus>\<^bsub>M\<^esub>s \<in> S. (a s) \<odot>\<^bsub>M\<^esub>  s | a S. a \<in> S \<rightarrow> carrier R \<and> finite S \<and> S \<subseteq> A } \<subseteq>  Span R M A"
        (is " ?X \<subseteq> Span R M A ")
proof
  fix h assume h_def : "h \<in> ?X"
  obtain S a where S_a : "S \<subseteq> A" "finite S" "h = (\<Oplus>\<^bsub>M\<^esub>s \<in> S. (a s) \<odot>\<^bsub>M\<^esub>  s)" "a \<in> S \<rightarrow> carrier R"
    using h_def by blast
  have "h \<in> { \<Oplus>\<^bsub>M\<^esub>s \<in> S. (a s) \<odot>\<^bsub>M\<^esub>  s | a. a \<in> S \<rightarrow> carrier R}"
    using S_a by auto
  hence "h \<in> Span R M S" using linear_combinations_finite_incl2 assms S_a by blast
  thus "h \<in> Span R M A" using Span_mono S_a assms by blast
qed

proposition (in vector_space) Span_as_linear_combinations :
  assumes "A \<subseteq> carrier M"
  shows "{ \<Oplus>\<^bsub>M\<^esub>s \<in> S. (a s) \<odot>\<^bsub>M\<^esub>  s | a S. a \<in> S \<rightarrow> carrier R \<and> finite S \<and> S \<subseteq> A } = Span R M A"
  using linear_combinations_incl2 linear_combinations_incl assms
  by blast

lemma (in vector_space) lin_indep_trunc :
  assumes "lin_indep R M A"
  shows "lin_indep R M (A - K)"
proof-
  {
  fix K assume K_def : "K \<subseteq> A"
  have "lin_indep R M (A - K)"
  proof (rule ccontr)
    assume "\<not> lin_indep R M (A - K)"
    from this have dep : "lin_dep R M (A - K)"
      using lin_indep_not_dep[of "A - K"] assms by auto
    from this obtain S where S_def : "(S \<subset> (A - K))"  "Span R M S = Span R M (A - K)"
      by auto
    hence "(S \<union> K) \<subset> A" using K_def by auto
    moreover have "Span R M (S \<union> K) = Span R M ((A - K) \<union> K)"
      using Span_union[OF S_def(2)] S_def assms K_def dep by auto
    hence "Span R M (S \<union> K) = Span R M A"
      by (simp add: K_def Un_absorb2) 
    ultimately show False using assms
      by (metis psubsetE)
  qed}
  note aux_lemma = this
  show ?thesis
  proof (cases "K \<subseteq> A")
    case True
    thus ?thesis using aux_lemma by auto
  next
    case False
   have "A - K = A - (A \<inter> K)" using False by auto
   thus ?thesis using aux_lemma[of "A \<inter> K"] by auto
 qed
qed

lemma (in vector_space) add_vector_lin_dep :
  assumes "lin_indep R M A"
    and "x \<in> carrier M"
    and "S \<subset> (insert x A)"
    and "S \<inter> A \<subset> A"
    and "Span R M S = Span R M (insert x A)"
  shows "x \<in> S"
proof (rule ccontr)
  assume "x \<notin> S"
  hence S_incl : "S \<subset> A "using assms by auto
  hence "Span R M S \<subseteq> Span R M A" using Span_mono[of S A] assms by auto
  hence "Span R M (insert x A) \<subseteq> Span R M A" using assms by auto
  moreover have "Span R M A \<subseteq> Span R M (insert x A)"
    using Span_mono[of A "insert x A"] assms by auto
  ultimately have "Span R M A = Span R M (insert x A)" by auto
  thus False using S_incl assms(5) assms(1) by blast
qed

lemma (in vector_space) not_in_every_Span :
  assumes "lin_indep R M A"
    and "x \<in> Span R M A"
    and "x \<noteq> \<zero>\<^bsub>M\<^esub>"
  shows "\<exists> S. S \<subseteq> A \<and> x \<notin> Span R M S"
proof
  have "{} \<subseteq> A" by auto
  moreover have "Span R M {} \<subseteq> {\<zero>\<^bsub>M\<^esub>}"
  proof
    fix x assume "x \<in> Span R M {}"
    from this show "x \<in> {\<zero>\<^bsub>M\<^esub>}" apply (induction x rule : Span.induct) apply simp_all
      by (metis M.zero_closed R.zero_closed r_null smult_assoc1 smult_zero)
  qed
  hence "x \<notin> Span R M {}" using assms by auto
  ultimately show "{} \<subseteq> A \<and> x \<notin> Span R M {}" by auto

proposition (in vector_space) exchange_theorem :
  assumes "lin_indep R M A"
    and "lin_indep R M (insert x B)"
  shows "\<exists>y. lin_indep R M (insert x (A - {y}))"
proof (cases "lin_indep R M (insert x A)")
  case True
  then show ?thesis using lin_indep_trunc
    by (metis insert_Diff_single)
  next
    case False
    have x_M : "x \<in> carrier M" using assms(2) by auto
    from False have "lin_dep R M (insert x A)"
      using lin_indep_not_dep[of "insert x A"] assms by simp
    from this obtain S where S_def : "(S \<subset> insert x A)" "Span R M S = Span R M (insert x A)"
      by auto
    then show ?thesis
    proof (cases "x \<in> S")
      case True
      then show ?thesis sorry
    next
      case False
      have "\<not> S \<inter> A \<subset> A" apply (rule ccontr) apply simp
        using add_vector_lin_dep[OF assms(1) x_M S_def(1)] False S_def by blast
      hence "S = A" using S_def by auto
      then show ?thesis sorry
qed
qed


end