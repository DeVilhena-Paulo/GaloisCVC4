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

lemma (in module) mono_Span:
  assumes "I \<subseteq> J" and "J \<subseteq> carrier M"
  shows "Span R M I \<subseteq> Span R M J"
proof-
  have "I \<subseteq> Span R M J "
    using assms SpanE(2) by blast
  thus "Span R M I \<subseteq> Span R M J"
    using Span_min_submodule1[of I "Span R M J"] assms Span_is_submodule[OF assms(2)]
    by blast
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
      using module.mono_Span[of R "(M\<lparr>carrier := J\<rparr>)" I J ] submodule.submodule_is_module[OF J_def(1)]
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


abbreviation generator :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set => bool"
  where "generator R M A \<equiv> A \<subseteq> (carrier M) \<and> Span R M A = carrier M"

abbreviation finite_dim :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> bool"
  where "finite_dim R M \<equiv> \<exists> A. finite A \<and> generator R M A"

abbreviation lin_dep :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "lin_dep R M A \<equiv> \<exists> S. (S \<subset> A) \<and> Span R M S = Span R M A" 

abbreviation lin_indep :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "lin_indep R M A \<equiv> \<forall> S. (S \<subset> A) \<longrightarrow> Span R M S \<subset> Span R M A"

abbreviation base :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "base R M A \<equiv> lin_indep R M A \<and> generator R M A"

lemma (in vector_space) lin_indep_not_dep:
  assumes "A \<subseteq> carrier M"
  shows "lin_dep R M A \<longleftrightarrow> \<not>lin_indep R M A" 
proof
  assume "lin_dep R M A"
  thus "\<not> lin_indep R M A "
    by blast
next
  assume "\<not> lin_indep R M A"
  from this obtain S where S_def : "(S \<subset> A)" "\<not> (Span R M S \<subset> Span R M A) " by auto
  moreover have "Span R M S \<subseteq> Span R M A" using S_def(1) mono_Span[of S A] assms by auto
  ultimately show  " lin_dep R M A" by blast
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


lemma (in vector_space) linear_combination :
  assumes "finite A" and "A \<subseteq> carrier M" and "A \<noteq> {}"
shows "h \<in> Span R M A \<Longrightarrow> h \<in> {x. \<exists> a. a \<in> (A \<rightarrow> carrier R) \<and> x = (\<Oplus>\<^bsub>M\<^esub>  v\<in>A. (a v \<odot>\<^bsub>M\<^esub> v))} "
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
  thus ?case by blast
  next
    case (a_inv h)
  note hyp = this
  from this obtain a where a_def : "a \<in> A \<rightarrow> carrier R \<and> h = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a v \<odot>\<^bsub>M\<^esub> v)" by auto
  have " (\<Oplus>\<^bsub>M\<^esub>v\<in>A. (\<ominus> \<one>) \<odot>\<^bsub>M\<^esub> ((a v) \<odot>\<^bsub>M\<^esub> v)) = (\<ominus>\<one>) \<odot>\<^bsub>M\<^esub> h"
    using module.finsum_smult_ldistr[OF module_axioms assms(1), of "(\<ominus>\<one>)" "\<lambda>v. a v \<odot>\<^bsub>M\<^esub> v"] a_def
    by (smt Pi_def R.add.inv_closed assms(2) mem_Collect_eq one_closed smult_closed subsetCE)
  also have "... = \<ominus>\<^bsub>M\<^esub> h"
    using smult_l_opposite smult_one Span_in_carrier hyp assms by auto
  moreover have "(\<Oplus>\<^bsub>M\<^esub>v\<in>A. (\<ominus> \<one>) \<odot>\<^bsub>M\<^esub> ((a v) \<odot>\<^bsub>M\<^esub> v)) = (\<Oplus>\<^bsub>M\<^esub>v\<in>A. (\<ominus> \<one> \<otimes> (a v) \<odot>\<^bsub>M\<^esub> v))"
    using smult_assoc1[of "\<ominus> \<one>"]
  then show ?case sorry
next
  case (eng_add h1 h2)
  then show ?case sorry
next
  case (eng_smult h1 h2)
  then show ?case sorry
qed

end