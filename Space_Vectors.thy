(* ************************************************************************** *)
(* Title:      Space_Vectors.thy                                              *)
(* Author:     Martin Baillon                                                 *)
(* ************************************************************************** *)


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

lemma (in module) Span_empty :
"Span R M {} = {\<zero>\<^bsub>M\<^esub>}"
proof
  show "{\<zero>\<^bsub>M\<^esub>} \<subseteq> Span R M {}" using Span.zero[of M R "{}"] by auto
  show "Span R M {} \<subseteq> {\<zero>\<^bsub>M\<^esub>} "
  proof
    fix x assume x_def : "x \<in> Span R M {}"
    show "x \<in> {\<zero>\<^bsub>M\<^esub>} " using x_def
      apply (induction x rule : Span.induct)
      by simp_all
  qed
qed


lemma (in module) Span_singleton :
  assumes "x \<in> carrier M"
  shows "Span R M {x} = {k \<odot>\<^bsub>M\<^esub> x | k. k \<in> carrier R}"
proof
  show "{k \<odot>\<^bsub>M\<^esub> x |k. k \<in> carrier R} \<subseteq> Span R M {x}"
    using Span.eng_smult[of _ R x M "{x}"] Span.incl[of x "{x}" R M] by blast
  show "Span R M {x} \<subseteq> {k \<odot>\<^bsub>M\<^esub> x |k. k \<in> carrier R}"
  proof
    fix xa assume xa_def : "xa \<in> Span R M {x}"
    show "xa \<in> {k \<odot>\<^bsub>M\<^esub> x |k. k \<in> carrier R}" using xa_def
    proof (induction rule : Span.induct)
      case zero
      then show ?case using smult_l_null assms by force
    next
      case (incl h)
      then show ?case using smult_one assms by force
    next
      case (a_inv h)
      then show ?case
        by (smt assms cring_simprules(3) mem_Collect_eq module_axioms module_def smult_l_minus)
    next
      case (eng_add h1 h2)
      then show ?case using smult_l_distr[OF _ _ assms]
        by (smt R.add.m_closed mem_Collect_eq)
    next
      case (eng_smult h1 h2)
      then show ?case using m_closed[of h1]
        by (smt assms mem_Collect_eq smult_assoc1) 
    qed
  qed
qed


lemma (in module) Span_is_add_subgroup :
  assumes "H \<subseteq> carrier M"
  shows "subgroup (Span R M H) (add_monoid (M))"
 using zero[of M R H] Span_in_carrier assms eng_add[of _ R M H] a_inv[of _ R M H] a_inv_def[of M]
  by (auto intro! : subgroup.intro) 


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

lemma (in module) elt_in_Span_imp_Span_idem :
  assumes "A \<subseteq> carrier M"
    and "x \<in> Span R M A"
  shows "Span R M (insert x A) = Span R M A"
proof
  have x_M : "x \<in> carrier M" using Span_in_carrier assms by auto
  thus "Span R M A \<subseteq> Span R M (insert x A)" using Span_mono[of A "insert x A"] assms by auto
  have "insert x A \<subseteq> Span R M A" using assms Span.incl by auto
  hence "Span R M (insert x A) \<subseteq> Span R M (Span R M A)"
    using Span_mono[of "insert x A" "Span R M A"] assms Span.incl[of _ "insert x A" R M]
          Span_in_carrier[OF assms(1)] by auto
  thus "Span R M (insert x A) \<subseteq> Span R M A "
    using Span_idem[OF assms(1)] by auto
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


definition
generator :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> 'c set \<Rightarrow> bool"
  where "generator R M A K \<equiv> A \<subseteq> (carrier M) \<and> Span R M A = K"

definition finite_dim :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "finite_dim R M S \<equiv> \<exists> A. finite A \<and> generator R M A S"

abbreviation lin_dep :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "lin_dep R M A \<equiv> A \<subseteq> carrier M \<and> (\<exists> S. (S \<subset> A) \<and> Span R M S = Span R M A)" 

abbreviation lin_indep :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> bool"
  where "lin_indep R M A \<equiv> A \<subseteq> carrier M \<and> (\<forall> S. (S \<subset> A) \<longrightarrow> Span R M S \<subset> Span R M A)"

definition base :: "('a, 'b) ring_scheme \<Rightarrow> ('a, 'c, 'd) module_scheme \<Rightarrow> 'c set \<Rightarrow> 'c set \<Rightarrow> bool"
  where "base R M A K \<equiv> lin_indep R M A \<and> generator R M A K"

definition (in vector_space) dim :: "'c set \<Rightarrow> nat"
  where "dim K \<equiv> LEAST n. (\<exists> A. finite A \<and> card A = n  \<and>  generator R M A K)"

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


lemma (in vector_space) zero_imp_dep :
  assumes "\<zero>\<^bsub>M\<^esub> \<in> A"
    and "A \<subseteq> carrier M"
  shows "lin_dep R M A" using assms(2)
proof
  have "A - {\<zero>\<^bsub>M\<^esub>} \<subset> A" using assms by auto
  moreover have "\<zero>\<^bsub>M\<^esub> \<in> Span R M (A - {\<zero>\<^bsub>M\<^esub>})" using Span.zero by auto
  hence "Span R M (A - {\<zero>\<^bsub>M\<^esub>}) = Span R M A"
    using elt_in_Span_imp_Span_idem[of "A - {\<zero>\<^bsub>M\<^esub>}" "\<zero>\<^bsub>M\<^esub>"] assms
    by (metis insert_Diff insert_subset)
  ultimately show "\<exists>S\<subset>A. Span R M S = Span R M A " by auto
qed


lemma (in vector_space) h_in_finite_Span :
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
  have "\<And>v. v \<in> A \<Longrightarrow> (\<lambda>v. \<zero>) v \<odot>\<^bsub>M\<^esub> v = \<zero>\<^bsub>M\<^esub>" using assms smult_l_null by auto
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
    using smult_l_null assms by auto
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
    using smult_l_minus smult_one Span_in_carrier hyp assms by auto
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
    using h_in_finite_Span[OF assms h_def] by auto
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

corollary (in vector_space) lin_indep_incl :
  assumes "lin_indep R M A"
    and "S \<subseteq> A"
  shows "lin_indep R M S"
  using lin_indep_trunc[OF assms(1), of "A - S"] assms
  by (simp add: double_diff)

lemma (in vector_space) vector_in_Span_imp_dep :
  assumes "A \<subseteq> carrier M"
    and "x \<in> Span R M A"
    and "x \<notin> A"
  shows "lin_dep R M (insert x A)"
proof
  show "insert x A \<subseteq> carrier M"
    using assms(1) Span_in_carrier[OF assms(1-2)] by simp
  have "Span R M A = Span R M (insert x A)"
    using elt_in_Span_imp_Span_idem[OF assms(1-2)] by auto
  thus "\<exists>S\<subset>insert x A. Span R M S = Span R M (insert x A)" using assms by auto
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
    from this show "x \<in> {\<zero>\<^bsub>M\<^esub>}" apply (induction x rule : Span.induct) by simp_all
  qed
  hence "x \<notin> Span R M {}" using assms by auto
  ultimately show "{} \<subseteq> A \<and> x \<notin> Span R M {}" by auto
qed

lemma (in vector_space) not_in_Span_imp_no_Span_inter :
  assumes "A \<subseteq> carrier M"
    and "x \<in> carrier M"
    and "x \<notin> Span R M A"
  shows "(Span R M A) \<inter> (Span R M {x}) = {\<zero>\<^bsub>M\<^esub>} "
proof
  have "{\<zero>\<^bsub>M\<^esub>} \<subseteq> Span R M A" using Span.zero by auto
  moreover have "{\<zero>\<^bsub>M\<^esub>} \<subseteq> Span R M {x}" using Span.zero by auto
  ultimately show "{\<zero>\<^bsub>M\<^esub>} \<subseteq> Span R M A \<inter> Span R M {x}" by auto
  show "Span R M A \<inter> Span R M {x} \<subseteq> {\<zero>\<^bsub>M\<^esub>}"
  proof (rule ccontr)
    assume "\<not> Span R M A \<inter> Span R M {x} \<subseteq> {\<zero>\<^bsub>M\<^esub>}"
    hence "\<exists> y. y \<in> Span R M A \<inter> Span R M {x} \<and> y \<notin> {\<zero>\<^bsub>M\<^esub>}" by auto
    from this obtain y where y_def : "y \<in> Span R M A \<inter> Span R M {x} \<and> y \<notin> {\<zero>\<^bsub>M\<^esub>}" by auto
    hence not_zero : "y \<noteq> \<zero>\<^bsub>M\<^esub>" by auto
    have "y \<in> {k \<odot>\<^bsub>M\<^esub> x | k. k \<in> carrier R}"
      using Span_singleton assms y_def by auto
    from this obtain k where k_def : "k \<in> carrier R" "k \<odot>\<^bsub>M\<^esub> x = y" by blast
    have "k \<odot>\<^bsub>M\<^esub> x \<in> Span R M A" using y_def k_def by auto
    moreover have "k \<noteq> \<zero>" using k_def(2) not_zero smult_l_null y_def assms(2) by auto
    hence inv_R : "inv k \<in> carrier R"
      by (simp add: k_def(1) local.field_Units)
    ultimately have "inv k \<odot>\<^bsub>M\<^esub> (k \<odot>\<^bsub>M\<^esub> x) \<in> Span R M A"
      using Span.eng_smult[of "inv k" R "k \<odot>\<^bsub>M\<^esub> x" M A] by auto
    hence "(inv k \<otimes> k) \<odot>\<^bsub>M\<^esub> x \<in> Span R M A"
      using smult_assoc1[of "inv k" k x] using k_def
      by (simp add: inv_R assms(2))
    hence "x \<in> Span R M A"
      by (simp add: \<open>k \<noteq> \<zero>\<close> assms(2) k_def(1) local.field_Units)
    thus False using assms by auto
  qed
qed
      
lemma (in vector_space) vector_indep :
  assumes "x \<in> carrier M"
    and "x \<noteq> \<zero>\<^bsub>M\<^esub>"
  shows "lin_indep R M {x}"
proof
  show "{x} \<subseteq> carrier M" using assms by auto
  show "\<forall>S\<subset>{x}. Span R M S \<subset> Span R M {x}"
  proof-
    {fix S assume S_def : "S \<subset> {x}" have "Span R M S \<subset> Span R M {x}"
      proof-
        from S_def have S_empty : "S = {}" by auto
        hence "S \<subseteq> {\<zero>\<^bsub>M\<^esub>}" by auto
        moreover have "Span R M {\<zero>\<^bsub>M\<^esub>} = {k \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> |k. k \<in> carrier R}"
          using Span_singleton[OF M.zero_closed] by auto
        moreover have "{k \<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> |k. k \<in> carrier R} \<subseteq> {\<zero>\<^bsub>M\<^esub>}" using smult_r_null
          by blast
        ultimately have "Span R M S \<subseteq> {\<zero>\<^bsub>M\<^esub>}"
          using Span_mono[of S "{\<zero>\<^bsub>M\<^esub>}"] M.zero_closed by blast
        moreover have "x \<in> Span R M {x}" using Span.incl[of x] by auto
        ultimately show "Span R M S \<subset> Span R M {x}" using assms
          using Span_mono S_empty by blast
      qed}
    thus "\<forall>S\<subset>{x}. Span R M S \<subset> Span R M {x}" by blast
  qed
qed


lemma (in vector_space) vector_decomposition :
  assumes "A \<subseteq> carrier M"
    and "B \<subseteq> carrier M"
    and "x \<in> Span R M (A \<union> B)"
  shows "\<exists> x1 x2. x1 \<in> Span R M A \<and> x2 \<in> Span R M B \<and> x1 \<oplus>\<^bsub>M\<^esub> x2 = x" using assms(3)
proof (induction rule : Span.induct)
  case zero
  then show ?case using Span.zero M.r_zero by blast
next
  case (incl h)
  then show ?case 
  proof
    assume "h \<in> A"
    thus ?case using M.r_zero[of h] Span.incl[of h A R M] Span.zero[of M R B] assms by blast
  next
    assume "h \<in> B"
    thus ?case using M.l_zero[of h] Span.incl[of h B R M] Span.zero[of M R A] assms by blast
  qed
next
  case (a_inv h)
  from this obtain x1 x2 where x1x2 : "x1 \<in> Span R M A" "x2 \<in> Span R M B" "x1 \<oplus>\<^bsub>M\<^esub> x2 = h" by auto
  hence "\<ominus>\<^bsub>M\<^esub> x1 \<in> Span R M A"
    using smult_l_minus[of "\<one>" x1] assms(1) smult_one[of x1] by (simp add: Span.a_inv)
  moreover have "\<ominus>\<^bsub>M\<^esub> x2 \<in> Span R M B"
    using Span.a_inv x1x2 by auto
  moreover have "\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> x2 = \<ominus>\<^bsub>M\<^esub> h"
    using x1x2 a_inv(1) smult_l_minus[of "\<one>" "x1 \<oplus>\<^bsub>M\<^esub> x2" ] smult_r_distr[of "\<one>" x1 x2]
         Span_in_carrier[OF assms(1) x1x2(1)] Span_in_carrier[OF assms(2) x1x2(2)]
    using M.minus_add by auto
  ultimately show ?case  by auto
next
  case (eng_add h1 h2)
  from this obtain x1 x2 where x1x2 : "x1 \<in> Span R M A" "x2 \<in> Span R M B" "x1 \<oplus>\<^bsub>M\<^esub> x2 = h1"
    by auto
  from eng_add obtain y1 y2 where y1y2 : "y1 \<in> Span R M A" "y2 \<in> Span R M B" "y1 \<oplus>\<^bsub>M\<^esub> y2 = h2"
    by auto
  have "h1 \<oplus>\<^bsub>M\<^esub> h2 = x1 \<oplus>\<^bsub>M\<^esub> x2 \<oplus>\<^bsub>M\<^esub> y1 \<oplus>\<^bsub>M\<^esub> y2"
    using x1x2 y1y2 assms Span_in_carrier M.add.m_assoc by auto 
  also have "... = x1 \<oplus>\<^bsub>M\<^esub> y1 \<oplus>\<^bsub>M\<^esub> x2 \<oplus>\<^bsub>M\<^esub> y2"
    using x1x2 y1y2 assms Span_in_carrier M.add.m_comm M.add.m_lcomm by auto
  finally have "h1 \<oplus>\<^bsub>M\<^esub> h2 =  (x1 \<oplus>\<^bsub>M\<^esub> y1) \<oplus>\<^bsub>M\<^esub> (x2 \<oplus>\<^bsub>M\<^esub> y2)"
    using x1x2 y1y2 assms Span_in_carrier M.add.m_assoc by auto
  moreover have "(x1 \<oplus>\<^bsub>M\<^esub> y1) \<in> Span R M A" using x1x2 y1y2 Span.eng_add by auto
  moreover have "(x2 \<oplus>\<^bsub>M\<^esub> y2) \<in> Span R M B" using x1x2 y1y2 Span.eng_add by auto
  ultimately show ?case by auto
next
  case (eng_smult h1 h2)
  then show ?case using smult_r_distr[of h1] Span_in_carrier assms
    by (metis Span.intros(5))
qed


lemma (in vector_space) two_vectors_exchange_Span :
  assumes "A \<subseteq> carrier M"
    and "x \<in> carrier M"
    and "y \<in> Span R M (insert x A)"
    and "y \<notin> Span R M A"
  shows "x \<in> Span R M (insert y A)"
proof-
  have "\<exists> x1 x2. x1 \<in> Span R M A \<and> x2 \<in> Span R M {x} \<and> x1 \<oplus>\<^bsub>M\<^esub> x2 = y"
    using vector_decomposition[of A "{x}" y] assms by auto
  from this obtain x1 x2 where x1x2 : "x1 \<in> Span R M A \<and> x2 \<in> Span R M {x} \<and> x1 \<oplus>\<^bsub>M\<^esub> x2 = y"
    by auto
  have not_null : "x2 \<noteq> \<zero>\<^bsub>M\<^esub>"
  proof
    assume x_zero : "x2 = \<zero>\<^bsub>M\<^esub>"
    hence "y = x1" using x1x2 M.r_zero assms Span_in_carrier by auto
    thus False using assms x1x2 by auto
  qed
  moreover have "x2 \<in> {k \<odot>\<^bsub>M\<^esub> x | k. k \<in> carrier R}"
    using Span_singleton x1x2 assms by auto
  from this obtain k where k_def : "k \<in> carrier R" "x2 = k \<odot>\<^bsub>M\<^esub> x" by auto
  hence k_prop : "k \<noteq> \<zero>"
    using not_null smult_l_null[of x2] x1x2 Span_in_carrier assms by auto 
  ultimately have "inv k \<odot>\<^bsub>M\<^esub>(\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> y) = inv k \<odot>\<^bsub>M\<^esub>\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> inv k \<odot>\<^bsub>M\<^esub> y"
    using smult_r_distr[of "inv k" x1 y] using assms Span_in_carrier x1x2 k_def field_Units
    by (metis Diff_iff M.add.inv_closed M.add.m_closed Units_inv_closed module.smult_closed
        module.smult_r_distr module_axioms singletonD)
  also have "... = inv k \<odot>\<^bsub>M\<^esub>\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> inv k \<odot>\<^bsub>M\<^esub> (x1 \<oplus>\<^bsub>M\<^esub> x2)"
    using x1x2 Span_in_carrier assms by auto
  also have "... = inv k \<odot>\<^bsub>M\<^esub>\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> inv k \<odot>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> inv k \<odot>\<^bsub>M\<^esub> x2"
    using x1x2 Span_in_carrier assms smult_r_distr[of "inv k" x1 x2] M.a_assoc
          k_prop k_def field_Units by auto 
  also have "... = inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> x1) \<oplus>\<^bsub>M\<^esub> inv k \<odot>\<^bsub>M\<^esub> x2"
    using smult_r_distr x1x2 k_def Span_in_carrier assms k_prop field_Units by auto
  also have "... = inv k \<odot>\<^bsub>M\<^esub> (\<zero>\<^bsub>M\<^esub>) \<oplus>\<^bsub>M\<^esub> inv k \<odot>\<^bsub>M\<^esub> x2"
    using x1x2 k_def Span_in_carrier assms M.l_neg by auto 
  also have "... = inv k \<odot>\<^bsub>M\<^esub> x2"
    using smult_r_null[of "inv k"] x1x2 k_def Span_in_carrier assms M.l_zero M.r_neg1 calculation
    by auto
  also have "... = inv k \<odot>\<^bsub>M\<^esub> (k \<odot>\<^bsub>M\<^esub> x)" using k_def by auto
  finally have "inv k \<odot>\<^bsub>M\<^esub>(\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> y) = x"
    using smult_assoc1[of "inv k" k x] assms k_def
    by (simp add: k_prop local.field_Units)
  moreover have "x1 \<in> Span R M (insert y A)"
    using x1x2 Span_mono[of A "insert y A"] assms Span_in_carrier by blast
  hence  "inv k \<odot>\<^bsub>M\<^esub>(\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> y) \<in> Span R M (insert y A)"
    using Span.eng_add[of "\<ominus>\<^bsub>M\<^esub> x1" R M "insert y A" y] Span.a_inv[of x1 R M "insert y A"]
          Span.eng_smult[of "inv k" R "\<ominus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> y" M "insert y A"] k_def k_prop x1x2
    by (simp add: Span.incl field_Units)
  ultimately show "x \<in> Span R M (insert y A)" by auto
qed

lemma (in vector_space) aux_lemma_for_replacement :
  assumes "lin_indep R M A"
    and "finite A"
    and "y \<in> Span R M A"
    and "y \<noteq> \<zero>\<^bsub>M\<^esub>"
  shows "\<exists> z \<in> carrier M. y \<notin> Span R M (A - {z})" using assms(2) assms(1,3)
proof (induction A)
  case empty
  then show ?case using assms
    using empty_Diff not_in_every_Span not_psubset_empty by force
next
  case (insert x F)
  have indep : "lin_indep R M F" using insert lin_indep_trunc[of "insert x F" "{x}"]  by simp
  show ?case
  proof (cases "y \<in> Span R M F")
    case True
    from this obtain z where z_def : "z \<in> carrier M""y \<notin> Span R M (F - {z})"
      using insert indep by auto
    have "y \<notin> Span R M (insert x F - {z})"
    proof
      assume hyp : "y \<in> Span R M (insert x F - {z})"
      from True obtain z1 z2
        where z1z2 : "z1 \<in> Span R M (F - {z})" "z2 \<in> Span R M {z}" "z1 \<oplus>\<^bsub>M\<^esub> z2 = y"
        using vector_decomposition[of "F - {z}" "{z}" y] insert(4) insert_is_Un[of z "F-{z}"]z_def
        by (metis (no_types, lifting) Diff_empty Diff_insert0 Un_commute empty_subsetI insert_Diff
           insert_subset)
      have z1_insert : "z1 \<in> Span R M (insert x (F - {z}))"
        using z1z2 Span_mono[of "F - {z}" "insert x (F - {z})"] insert insert_subset
        by (metis (no_types, lifting) Diff_empty Diff_insert0 insert_Diff subset_insertI)
      have z20 : "z2 \<noteq> \<zero>\<^bsub>M\<^esub>"
      proof
        assume "z2 = \<zero>\<^bsub>M\<^esub>"
        then have "y = z1" using z1z2 Span_in_carrier insert(4) z_def
          by (meson Span.eng_add Span.zero)
        thus False using z1z2(1) z_def by auto
      qed
      have "z2 \<in> {k \<odot>\<^bsub>M\<^esub> z |k. k \<in> carrier R}"
        using Span_singleton[OF z_def(1)] z1z2(2) by auto
      from this obtain k where k_def : "k \<in> carrier R" "z2 = k \<odot>\<^bsub>M\<^esub> z" by auto
      hence k0 : "k \<noteq> \<zero>"
        using z20 smult_l_null[OF z_def(1)] by auto
      hence inv : "inv k \<in> carrier R" using field_Units k_def by blast
      hence "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> z1 \<oplus>\<^bsub>M\<^esub> y) \<in> Span R M (insert x (F - {z}))"
        using hyp z1z2(1) Span.a_inv[OF z1_insert] Span.eng_add[OF _ hyp, of "\<ominus>\<^bsub>M\<^esub> z1"]
              Span.eng_smult[OF inv, of "(\<ominus>\<^bsub>M\<^esub> z1 \<oplus>\<^bsub>M\<^esub> y)"]
        by (smt insert_Diff_if z_def(2)) 
      moreover have "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> z1 \<oplus>\<^bsub>M\<^esub> y) = inv k \<odot>\<^bsub>M\<^esub> (\<zero>\<^bsub>M\<^esub> \<oplus>\<^bsub>M\<^esub> z2)"
        using z1z2 M.l_neg M.l_zero M.r_neg1 Span_in_carrier smult_closed z_def(1) insert_subset
        by (metis (no_types, lifting) Diff_empty Diff_insert0 insert.prems(1) insert_Diff k_def) 
      hence "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> z1 \<oplus>\<^bsub>M\<^esub> y) = inv k \<odot>\<^bsub>M\<^esub> (k \<odot>\<^bsub>M\<^esub> z)"
        using M.l_zero k_def Span_in_carrier z_def(1) smult_closed[OF k_def(1) z_def(1)] by auto
      hence "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> z1 \<oplus>\<^bsub>M\<^esub> y) = z"
        using smult_assoc1[OF inv k_def(1)] by (simp add: k0 k_def(1)field_Units z_def(1)) 
      ultimately have "z \<in> Span R M (insert x (F - {z}))" by auto
      moreover have "insert x (F - {z}) \<subseteq> carrier M"
        using insert(4) by blast
      ultimately have "lin_dep R M (insert z (insert x (F - {z})))"
        using vector_in_Span_imp_dep[of "(insert x (F - {z}))" z]True insert(2) z_def by fastforce
      hence "lin_dep R M (insert x F)" using True z_def
        by (metis (no_types, lifting) Diff_empty Diff_insert0 insert_Diff insert_commute)
      thus False using insert(4) by auto
    qed
    then show ?thesis using z_def by auto
  next
    case False
    then have "y \<notin> Span R M (insert x F - {x})"
      by (simp add: insert.hyps(2))
    then show ?thesis using insert(4) by blast
  qed
qed



lemma (in vector_space) non_null_decomposition :
  assumes "A \<subseteq> carrier M"
    and "x \<in> Span R M A"
    and "x \<noteq> \<zero>\<^bsub>M\<^esub>"
  shows "\<exists> y \<in> A. \<exists> z \<in> Span R M (A - {y}). \<exists> y2 \<in> Span R M {y}. y2 \<noteq> \<zero>\<^bsub>M\<^esub> \<and> z \<oplus>\<^bsub>M\<^esub> y2 = x"
proof-
    {fix I x assume Ix : "x \<in> Span R M I" "finite I" "x \<noteq>\<zero>\<^bsub>M\<^esub>" "I \<subseteq> carrier M"
    have "\<exists> y \<in> I. \<exists> z \<in> Span R M (I - {y}). \<exists> y2 \<in> Span R M {y}. y2 \<noteq> \<zero>\<^bsub>M\<^esub> \<and> z \<oplus>\<^bsub>M\<^esub> y2 = x"
      using Ix(2,1,3,4)
    proof(induction I rule : finite.induct)
      case emptyI
      then have "x = \<zero>\<^bsub>M\<^esub>"
        using aux_lemma_for_replacement by fastforce
      then show ?case using emptyI by auto
    next
      case (insertI A a)
      then have inM : "x \<in> carrier M" "a \<in> carrier M" using Span_in_carrier by blast+
      show ?case
      proof (cases "x \<in> Span R M A")
        case True
        hence "\<exists>y\<in>A. \<exists>z\<in>Span R M (A - {y}). \<exists>y2\<in>Span R M {y}. y2 \<noteq> \<zero>\<^bsub>M\<^esub> \<and> z \<oplus>\<^bsub>M\<^esub> y2 = x"
          using insertI by auto
        then obtain y z y2 
          where yz : "y \<in> A" "z\<in>Span R M (A - {y})" "y2\<in>Span R M {y}" "y2 \<noteq> \<zero>\<^bsub>M\<^esub>""z \<oplus>\<^bsub>M\<^esub> y2 = x"
          by auto
        then have "y \<in> insert a A" by auto
        moreover have "z\<in>Span R M ((insert a A) - {y})"
          using Span_mono[of "A - {y}" "insert a A - {y}"] insertI yz by blast
        ultimately show ?thesis using yz
          by blast 
      next
        case False
        from insertI obtain x1 x2
          where x1x2 : "x1 \<in> Span R M ((insert a A) - {a})" "x2 \<in> Span R M {a}" "x1 \<oplus>\<^bsub>M\<^esub> x2 = x"
          using vector_decomposition[of "(insert a A) - {a}" "{a}"] insert_is_Un insert_absorb
          by (smt Diff_insert_absorb False Un_commute empty_subsetI insert_subset)
        have x20 : "x2 \<noteq> \<zero>\<^bsub>M\<^esub>"
        proof
          assume "x2 = \<zero>\<^bsub>M\<^esub>"
          then have "x = x1" using x1x2 Span_in_carrier[of "insert a A - {a}"] inM insertI
            by fastforce
          thus False using x1x2(1) False insertI
            by (metis Diff_insert_absorb insert_absorb)
        qed
        then show ?thesis 
          using x1x2(1) x1x2(2) x1x2(3) by blast
      qed
    qed}
  note existence = this
  obtain S where S_def :  "S \<subseteq> A" "finite S" "x \<in> Span R M S"
    using h_in_finite_Span assms by meson 
  hence "\<exists>y\<in>S. \<exists>z\<in>Span R M (S - {y}). \<exists>y2\<in>Span R M {y}. y2 \<noteq> \<zero>\<^bsub>M\<^esub> \<and> z \<oplus>\<^bsub>M\<^esub> y2 = x"
    using S_def existence assms(1) assms(3) by blast
  from this obtain y z y2
    where aux : "y\<in>S" "z\<in>Span R M (S - {y})" "y2\<in>Span R M {y}" "y2 \<noteq> \<zero>\<^bsub>M\<^esub>" "z \<oplus>\<^bsub>M\<^esub> y2 = x"
    by auto
  have "y \<in> A" using aux S_def by auto
  moreover have "z\<in>Span R M (A - {y})"
    using Span_mono[of "S - {y}" "A- {y}"] assms(1) aux(2) S_def(1) by blast
  ultimately show ?thesis using aux by auto
qed


lemma (in vector_space) inter_null_imp_indep :
  assumes "lin_indep R M A"
    and "lin_indep R M B"
    and "Span R M A \<inter> Span R M B = {\<zero>\<^bsub>M\<^esub>}"
  shows "lin_indep R M (A \<union> B)" 
proof
  show carrier : "A \<union> B \<subseteq> carrier M" using assms by auto
  {fix S I J x
    assume hyp : "S \<subset> I \<union> J" "lin_indep R M I" "lin_indep R M J" "Span R M I \<inter> Span R M J = {\<zero>\<^bsub>M\<^esub>}"
                 "x \<in> I - S" "x \<in> Span R M S" have False
    proof-
      have not0 : "\<zero>\<^bsub>M\<^esub> \<notin> I" using zero_imp_dep[of I] hyp(2,5) lin_indep_not_dep by blast
      hence xnot0 : "x \<noteq> \<zero>\<^bsub>M\<^esub>" using hyp(5) by auto
      have "I \<inter> J \<subseteq> {}" using Span.incl[of _ "I \<inter> J" R M] Span_mono[of "I \<inter> J"] not0 hyp(2,3,4)
        by (smt Diff_disjoint Diff_insert_absorb IntI Int_lower1 Int_lower2 set_rev_mp subsetI)
      hence S_decomp : "S = (S - I) \<union> (S - J)" by blast
      from vector_decomposition[of "S - I" "S - J" x] hyp(1,2,3,6) this obtain x1 x2
        where x1x2 :"x1 \<in> Span R M (S - I)" "x2 \<in> Span R M (S - J)" "x1 \<oplus>\<^bsub>M\<^esub> x2 = x"
        by (metis (no_types, lifting) Diff_subset_conv psubset_imp_subset
            sup.absorb_iff1 sup.absorb_iff2 sup_left_commute)
      have "x \<in> carrier M" using hyp(1,2,3,5) by auto
      hence allM : "x \<in> carrier M""x1 \<in> carrier M""x2 \<in> carrier M" apply simp
        using x1x2 Span_in_carrier[of "S - I" x1]Span_in_carrier[of "S - J" x2] hyp(1,2,3)
         by (metis Diff_subset_conv psubset_imp_subset subset_trans sup_commute)+
       hence "x \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> x2 = x1" using x1x2 by (metis M.add.inv_solve_right)
       moreover have "x \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> x2 \<in> Span R M I"
         using x1x2(2) hyp(5) Span.incl[of x I R M] Span.a_inv[of x2 R M I] S_decomp hyp(1,2)
               Span.eng_add[of x R M I"\<ominus>\<^bsub>M\<^esub> x2"] Span_mono[of "S - J" I] by blast
       moreover have "x1 \<in> Span R M J"
         using x1x2(1) S_decomp hyp(1,3) Span_mono[of "S - I" J] insert_Diff by blast
       ultimately have "x1 \<in> Span R M I \<inter> Span R M J" by simp
       hence "x1 = \<zero>\<^bsub>M\<^esub>" using hyp(4) by auto
       hence "x = x2" using x1x2(3) allM M.l_zero by auto
       hence "x \<in> Span R M (S \<inter> I)"
         using x1x2(2) S_decomp hyp(1,2) Span_mono[of "S - J""S \<inter> I"] by blast 
       moreover have "lin_indep R M (insert x (S \<inter> I))"
         using lin_indep_incl[OF hyp(2), of "(insert x (S \<inter> I))"] hyp(5) by auto
       ultimately show False
         by (metis Diff_iff Int_iff hyp(5) insert_subset psubsetE vector_in_Span_imp_dep) 
     qed}
   note aux = this
   show "\<forall>S\<subset>A \<union> B. Span R M S \<subset> Span R M (A \<union> B)"
   proof-
     {fix S assume S_def : "S \<subset> A \<union> B" have "Span R M S \<subset> Span R M (A \<union> B)"
       proof
         show  "Span R M S \<subseteq> Span R M (A \<union> B)" using Span_mono assms S_def by auto
         show"Span R M S \<noteq> Span R M (A \<union> B)"
         proof
           assume hyp : "Span R M S = Span R M (A \<union> B)"
           from S_def obtain x where x_def : "x \<in> (A \<union> B) - S" by auto
           show False
           proof (cases "x \<in> A")
             case True
             then show ?thesis
               using aux[OF S_def assms(1,2,3)] x_def hyp Span.incl[of x "A \<union> B" R M] by blast
           next
             case False
             hence "x \<in> B" using x_def by auto
             then show ?thesis
               using aux[of S B A, OF _ assms(2,1)] S_def assms x_def hyp Span.incl[of x "A \<union> B" R]
               by (metis Diff_iff Un_commute inf_commute)
           qed
         qed
       qed}
     thus ?thesis by auto
   qed
qed


lemma (in vector_space) indep_inter_null :
  assumes  "lin_indep R M (A \<union> B)"
    and "A \<inter> B = {}"
  shows "Span R M A \<inter> Span R M B = {\<zero>\<^bsub>M\<^esub>}"
proof
  show "{\<zero>\<^bsub>M\<^esub>} \<subseteq> Span R M A \<inter> Span R M B" using Span.zero by auto
  have indA : "lin_indep R M A" using lin_indep_incl[OF assms(1)] by auto
  show "Span R M A \<inter> Span R M B \<subseteq> {\<zero>\<^bsub>M\<^esub>}" using assms indA
  proof(induction A arbitrary : B rule : infinite_finite_induct)
    case (infinite A)
    show ?case apply auto apply (rule ccontr) 
    proof-
      fix x assume x_def : "x \<in>Span R M A" "x \<in> Span R M B" "x \<noteq> \<zero>\<^bsub>M\<^esub>"
      from non_null_decomposition[of A x] x_def infinite obtain y z y2
        where hyp : "y\<in>A" "z\<in>Span R M (A - {y})" "y2\<in>Span R M {y}" "y2 \<noteq> \<zero>\<^bsub>M\<^esub>" "z \<oplus>\<^bsub>M\<^esub> y2 = x"
        by auto
      have "\<ominus>\<^bsub>M\<^esub>z\<oplus>\<^bsub>M\<^esub>x = y2" using hyp a_comm_group infinite Span_in_carrier
        by (metis (no_types, lifting) M.r_neg1  empty_subsetI insert_Diff insert_subset)
      moreover have indep : "lin_indep R M ((A - {y})\<union> B)"
        using infinite lin_indep_incl[of "(A \<union> B)""((A - {y})\<union> B)"] by fastforce
      then have "z\<in>Span R M ((A - {y})\<union> B)""x\<in>Span R M ((A - {y})\<union> B)"
        using x_def(2) hyp(2) Span_mono[of B "((A - {y})\<union> B)"] Span_mono[of"A - {y}" "(A - {y})\<union> B"]
        by auto
      then have "\<ominus>\<^bsub>M\<^esub>z\<oplus>\<^bsub>M\<^esub>x \<in> Span R M ((A - {y})\<union> B)"
        using Span.eng_add[of "\<ominus>\<^bsub>M\<^esub>z" R M "((A - {y})\<union> B)" x] Span.a_inv[of z R M "((A - {y})\<union> B)"]
        by blast
      ultimately have y2 : "y2 \<in> Span R M ((A - {y})\<union> B)" by auto
      hence "y2 \<in> Span R M (A - {y} \<union> B) \<inter> Span R M {y}" using hyp by auto
      moreover have "insert y (A - {y} \<union> B) = A \<union> B" using hyp(1) by auto
      moreover have "y \<in> carrier M" using infinite hyp(1) by auto
      ultimately show  False using vector_in_Span_imp_dep[of "A - {y} \<union> B" y] hyp(1,4) infinite(2)
                        not_in_Span_imp_no_Span_inter[of "A - {y} \<union> B" y]
        by (metis DiffE IntI UnE empty_iff indep infinite.prems(2) less_le singletonD singletonI)
    qed
  next
    case empty
    then show ?case using Span_empty by auto
  next
    case (insert a F)
    show ?case
    proof (cases "a \<in> Span R M B")
      case True
      then have "a \<in> Span R M (F \<union> B)"
        using Span_mono[of B "(F \<union> B)"] insert lin_indep_incl[of "(F \<union> B)" "(insert a F \<union> B)"]
        by auto
      moreover have "a \<notin> B" using insert by auto
      ultimately have  "lin_dep R M (insert a F \<union> B)"
        using vector_in_Span_imp_dep[of "(F\<union>B)" a] insert lin_indep_incl[OF insert(4), of "(F \<union> B)"]
        by auto
      then show ?thesis using insert(4) lin_indep_not_dep
        by meson
    next
      case False
      then have indep : "lin_indep R M (F \<union> insert a B)"
        using insert by (simp add: insert.IH)
      moreover have "F \<inter> insert a B = {}" using insert by auto
      ultimately have inter : "Span R M F \<inter> Span R M (insert a B) \<subseteq> {\<zero>\<^bsub>M\<^esub>}"
        using insert(3)[of "insert a B"] lin_indep_incl[OF insert(4),of F] by auto       
      show ?thesis 
      proof
        fix x assume x_def : "x \<in> Span R M (insert a F) \<inter> Span R M B"
        from this have xincl : "x \<in> Span R M (insert a F)"  by auto
        from this vector_decomposition[of F "{a}" x] insert obtain x1 x2
          where x1x2 : "x1 \<in> Span R M F" "x2 \<in> Span R M {a}" "x1 \<oplus>\<^bsub>M\<^esub> x2 = x" by auto
        moreover have "x \<in> Span R M (insert a B)"
          using Span_mono[of B "insert a B"] lin_indep_incl[OF indep, of "insert a B"] x_def by auto
        hence "x \<oplus>\<^bsub>M\<^esub> \<ominus>\<^bsub>M\<^esub> x2 \<in> Span R M (insert a B)"
          using x1x2(2) Span_mono[of "{a}" "insert a B"] lin_indep_incl[OF indep, of "insert a B"]
                Span.a_inv[of x2 R M] Span.eng_add[of x R M "insert a B""\<ominus>\<^bsub>M\<^esub> x2 "]
          by (metis Int_lower2 Un_upper2 insert.prems(2) insert_Diff insert_mono insert_subset)
        hence "x1 \<in> Span R M (insert a B)"
          using x1x2 M.add.inv_solve_right[of x1 x x2] Span_in_carrier x_def
          by (metis xincl empty_subsetI insert.prems(3) insert_subset)
        ultimately have "x1 =\<zero>\<^bsub>M\<^esub> " using inter  by blast
        hence "x = x2" using x1x2 Span_in_carrier[of "{a}" x2] M.l_zero[of x2] insert by blast
        hence "x \<in>Span R M {a} \<inter> Span R M B" using x1x2 x_def by auto
        moreover have "Span R M {a} \<inter> Span R M B = {\<zero>\<^bsub>M\<^esub>}"
          using not_in_Span_imp_no_Span_inter[of B, OF _ _ False] lin_indep_incl[OF indep, of B]
                insert by auto
        ultimately show "x \<in> {\<zero>\<^bsub>M\<^esub>}" by auto
      qed
    qed
  qed
qed

lemma (in vector_space) indep_eq_inter_null :
  assumes "lin_indep R M A"
    and "lin_indep R M B"
    and "A\<inter>B = {}"
  shows "(lin_indep R M (A \<union> B)) = ((Span R M A) \<inter> (Span R M B) = {\<zero>\<^bsub>M\<^esub>})"
  using indep_inter_null[OF _ assms(3)] inter_null_imp_indep[OF assms(1,2)]
  by meson


lemma (in vector_space) add_vector_indep :
  assumes "lin_indep R M A"
    and "y \<in> carrier M"
    and "y \<notin> Span R M A"
  shows "lin_indep R M (insert y A)"
  using not_in_Span_imp_no_Span_inter[OF _ assms(2,3)] assms Span.zero[of M R A]
       inter_null_imp_indep[OF assms(1) vector_indep[OF assms(2)]]
  by (metis Un_insert_right sup_bot.right_neutral)


proposition (in vector_space) replacement_theorem :
  assumes "lin_indep R M A"
    and "lin_indep R M (insert x B)"
  shows "\<exists>y. lin_indep R M (insert x (A - {y}))"
proof (cases "x \<in> Span R M A")
  case True
  have not0 : "x \<noteq> \<zero>\<^bsub>M\<^esub>" using assms(2) zero_imp_dep[of "insert x B"]
    by (meson insert_iff lin_indep_not_dep)
  obtain S where S_def : "S \<subseteq> A""finite S" "x \<in> Span R M S"
    using h_in_finite_Span[of A, OF _ True] assms by auto
  hence "\<exists>z\<in>carrier M. x \<notin> Span R M (S - {z})"
    using aux_lemma_for_replacement[OF _ S_def(2,3) not0] lin_indep_trunc[OF assms(1), of "A - S"]
    by (simp add: double_diff) 
  then obtain y where y_def : "y \<in> carrier M" "x \<notin> Span R M (S - {y})" by auto
  have "x \<notin> Span R M (A - {y})"
  proof
    assume hyp : "x \<in> Span R M (A - {y})"
    obtain y1 y2
      where y1y2 : "y1 \<in> Span R M (S - {y})" "y2 \<in> Span R M {y}" "y1 \<oplus>\<^bsub>M\<^esub> y2 = x"
      using vector_decomposition[of "S - {y}" "{y}" x] insert_is_Un insert_absorb S_def y_def assms
      by (smt Diff_empty Diff_insert0 Un_Diff_cancel Un_commute empty_subsetI insert_subset
              subset_trans)
    have allM : "x \<in> carrier M""y1 \<in> carrier M""y2 \<in> carrier M"
      using assms y1y2(1,2) y_def(1) Span_in_carrier[of "S- {y}" y1] Span_in_carrier[of "{y}" y2]
             S_def(1)
      by fastforce+
    have y20 : "y2 \<noteq> \<zero>\<^bsub>M\<^esub>"
    proof
      assume "y2 = \<zero>\<^bsub>M\<^esub>"
      then have "x = y1" using y1y2 Span_in_carrier y_def
        by (meson Span.eng_add Span.zero)
      thus False using y1y2(1) y_def by auto
    qed
    have "\<ominus>\<^bsub>M\<^esub>y1 \<oplus>\<^bsub>M\<^esub> x = y2" using allM y1y2(3) M.r_neg1 by blast
    moreover have "y1 \<in> Span R M (A - {y})"
      using S_def y1y2(1) Span_mono[of "S - {y}""(A - {y})"] assms by auto
    hence "\<ominus>\<^bsub>M\<^esub>y1 \<oplus>\<^bsub>M\<^esub> x \<in> Span R M (A - {y})"by (simp add: Span.a_inv Span.eng_add hyp)
    ultimately have "y2 \<in> Span R M (A - {y})" by auto
    hence "y2 \<in> Span R M (A - {y}) \<inter> Span R M {y}" using y1y2 by auto
    moreover have "(A - {y}) \<inter> {y} = {}" by blast
    moreover have "lin_indep R M (A - {y} \<union> {y})"
      using assms(1) S_def calculation(2) y_def(2) Diff_insert0 Un_Diff_Int
      by (metis (no_types, lifting) Diff_empty Diff_idemp Un_insert_right insert_Diff subsetCE)
    ultimately show False using indep_inter_null[of "A - {y}""{y}"] y20 assms(1) by blast
  qed
    then show ?thesis
      using add_vector_indep[of "A - {y}" x] assms lin_indep_trunc by auto
next
  case False
  then show ?thesis
    using add_vector_indep[OF assms(1) _ False] assms lin_indep_trunc[of "insert x A"]
    by (metis Diff_idemp Diff_insert_absorb insert_subset lin_indep_not_dep zero_imp_dep)
qed

lemma (in vector_space) vector_unique_decomposition_aux :
  assumes "lin_indep R M(A \<union> B)"
    and "A \<inter> B = {}"
    and "x \<in> Span R M (A \<union> B)"
shows "\<exists>! x1. \<exists>! x2. x1 \<in> Span R M A \<and> x2 \<in> Span R M B \<and> x1 \<oplus>\<^bsub>M\<^esub> x2 = x"
proof-
  have AM : "A \<subseteq> carrier M" using assms(1) by auto
  have BM : "B \<subseteq> carrier M" using assms(1) by auto
  from vector_decomposition[of A B x] obtain x1 x2
    where x1x2 : "x1 \<in> Span R M A" "x2 \<in> Span R M B" "x1 \<oplus>\<^bsub>M\<^esub> x2 = x" using assms AM BM by auto
  show ?thesis
  proof
    show  "\<exists>!x2. x1 \<in> Span R M A \<and> x2 \<in> Span R M B \<and> x1 \<oplus>\<^bsub>M\<^esub> x2 = x"
    proof
      show "x1 \<in> Span R M A \<and> x2 \<in> Span R M B \<and> x1 \<oplus>\<^bsub>M\<^esub> x2 = x" using x1x2 by auto
      { fix xb assume xb : "xb \<in> Span R M B" "x1 \<oplus>\<^bsub>M\<^esub> xb = x" have "xb = x2"
        proof-
          from xb have "\<ominus>\<^bsub>M\<^esub>x1 \<oplus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> xb = xb"
            using x1x2 xb assms Span_in_carrier M.l_neg by auto
          moreover have "\<ominus>\<^bsub>M\<^esub>x1 \<oplus>\<^bsub>M\<^esub> x1 \<oplus>\<^bsub>M\<^esub> xb = \<ominus>\<^bsub>M\<^esub>x1 \<oplus>\<^bsub>M\<^esub> x"
            using x1x2 xb assms Span_in_carrier M.l_neg AM BM M.add.inv_solve_left by force
          moreover have "\<ominus>\<^bsub>M\<^esub>x1 \<oplus>\<^bsub>M\<^esub> x = x2"
            using x1x2 assms Span_in_carrier AM BM M.l_neg  M.r_neg1 by auto 
          ultimately show  "xb = x2" by auto
        qed}
      thus "\<And>x2a. x1 \<in> Span R M A \<and> x2a \<in> Span R M B \<and> x1 \<oplus>\<^bsub>M\<^esub> x2a = x \<Longrightarrow> x2a = x2" by auto
    qed
    {fix xa assume xa : "\<exists>!x2. xa \<in> Span R M A \<and> x2 \<in> Span R M B \<and> xa \<oplus>\<^bsub>M\<^esub> x2 = x"
      have "xa = x1"
      proof-
        from xa obtain xb where xb : "xa \<in> Span R M A \<and> xb \<in> Span R M B \<and> xa \<oplus>\<^bsub>M\<^esub> xb = x" by auto
        hence "xa \<oplus>\<^bsub>M\<^esub> xb = x1 \<oplus>\<^bsub>M\<^esub> x2"
          using x1x2 by auto
        hence "\<ominus>\<^bsub>M\<^esub>x1 \<oplus>\<^bsub>M\<^esub> xa \<oplus>\<^bsub>M\<^esub> xb = x2"
          using AM BM xb Span_in_carrier M.l_neg M.add.m_assoc M.r_neg1 x1x2 by auto
        hence eq : "\<ominus>\<^bsub>M\<^esub>x1 \<oplus>\<^bsub>M\<^esub> xa = x2 \<ominus>\<^bsub>M\<^esub>xb" 
          using AM BM xb Span_in_carrier M.r_neg M.add.m_assoc M.r_neg1 x1x2
          by (metis M.add.inv_solve_right M.a_closed M.minus_eq M.a_inv_closed) 
        moreover have "\<ominus>\<^bsub>M\<^esub>x1 \<oplus>\<^bsub>M\<^esub> xa \<in> Span R M A"
          using x1x2 xb by (simp add: Span.a_inv Span.eng_add)
        moreover have "x2 \<ominus>\<^bsub>M\<^esub>xb \<in> Span R M B"
          using x1x2 xb by (metis BM M.minus_eq Span.a_inv Span.eng_add Span_in_carrier)
        moreover have "Span R M A \<inter> Span R M B = {\<zero>\<^bsub>M\<^esub>}" using indep_inter_null[OF assms(1,2)].
        ultimately have "x2 \<ominus>\<^bsub>M\<^esub> xb = \<zero>\<^bsub>M\<^esub>" by auto
        thus "xa = x1" using eq xb x1x2(1) Span_in_carrier[of A] lin_indep_incl[OF assms(1), of A]
          by (metis AM M.minus_unique M.r_neg Span.a_inv)
      qed}
    thus "\<And>x1a. \<exists>!x2. x1a \<in> Span R M A \<and> x2 \<in> Span R M B \<and> x1a \<oplus>\<^bsub>M\<^esub> x2 = x \<Longrightarrow> x1a = x1" by auto
  qed
qed

corollary (in vector_space) vector_unique_decomposition :
  assumes "lin_indep R M(A \<union> B)"
    and "A \<inter> B = {}"
    and "x \<in> Span R M (A \<union> B)"
  shows "\<exists> x1 x2. x1 \<in> Span R M A \<and> x2 \<in> Span R M B \<and> x1 \<oplus>\<^bsub>M\<^esub> x2 = x \<and>
        (\<forall> y z. (y \<in> Span R M A \<and> z \<in> Span R M B \<and> y \<oplus>\<^bsub>M\<^esub> z = x) \<longrightarrow> y = x1 \<and> z = x2)"
  apply simp using vector_unique_decomposition_aux[OF assms]
  unfolding Ex1_def apply simp using assms Span_in_carrier
  by (metis (no_types, lifting) abelian_group.r_neg1 le_sup_iff module_axioms module_def)

lemma (in vector_space) extended_replacement_theorem :
  assumes "finite I"
    and "lin_indep R M I"
    and "lin_indep R M J"
    and "card J \<ge> card I"
  shows "\<forall> S \<subseteq> I. \<exists> V \<subseteq> J. finite V \<and> (card V = card S) \<and> S \<inter> (J-V) = {}
                            \<and>lin_indep R M (S \<union> (J - V))"
  using assms
proof(induction I arbitrary : J rule : finite_induct)
  case empty  
  then show ?case using  Diff_empty Un_empty_left  finite.emptyI
    by (metis Diff_disjoint empty_subsetI subset_empty) 
next
  case (insert x F)
  have indepF : "lin_indep R M F"
    using insert(4) lin_indep_trunc[of "insert x F" "{x}"]by (simp add: insert.hyps(2))
  have xnot0 : "x \<noteq> \<zero>\<^bsub>M\<^esub>"
    using zero_imp_dep[of "insert x F"] insert(4) by (meson insert_iff lin_indep_not_dep)
  {fix S assume S_def : "S \<subseteq> insert x F"
    have "(\<exists>V \<subseteq> J. finite V \<and> card V = card S \<and> S \<inter> (J-V) = {} \<and> lin_indep R M (S \<union> (J - V)))"
          (is "?P S J")
    proof (cases "S \<subseteq> F")
      case True
      then show ?thesis using insert(3)[OF indepF insert(5)] insert by auto
    next
      case False
      hence "x \<in> S" using S_def by auto
      from this obtain V where V_def : "x \<notin> V""S = insert x V" by (meson Set.set_insert)
      hence inclF : "V \<subseteq> F" using S_def by auto
      have indep : "lin_indep R M S" using insert lin_indep_incl[OF insert(4) S_def] by simp
      hence indep2 : "lin_indep R M V"
        using lin_indep_incl[OF indep, of V] V_def  by (simp add: subset_insertI) 
      have notx : "x \<notin> Span R M V"
        using indep vector_in_Span_imp_dep[of V x] indep2 V_def indep2 by (meson lin_indep_not_dep)
      have "?P V J"
        using insert(3)[OF lin_indep_incl[OF insert(4)]lin_indep_incl[OF insert(5), of J]]inclF
        by (meson card_insert_le le_trans insert(1,6) order_refl subset_insertI)
      from this obtain L
        where L_def : "L\<subseteq>J""lin_indep R M (V \<union> (J - L))" "card L = card V"
                      "finite L" "V \<inter> (J-L) = {}" 
        by auto
      show ?thesis
      proof (cases "x \<in> Span R M (J-V-L)")
        case True
        from non_null_decomposition[OF _ True xnot0] insert(5) obtain y z y2
          where yz : "y\<in>J-V-L""z\<in>Span R M (J-V-L-{y})""y2\<in>Span R M {y}""y2 \<noteq> \<zero>\<^bsub>M\<^esub>""z \<oplus>\<^bsub>M\<^esub> y2 = x"
          by auto
        have "x \<notin> Span R M (V \<union> (J - V - L - {y}))"
        proof
          assume hyp : "x \<in> Span R M (V \<union> (J - V - L - {y}))"
          have "V \<union> (J - V-L - {y}) \<subseteq> carrier M" using indep2 insert(5) by blast
          moreover have "J - V - L - {y} \<subseteq> V \<union> (J - L - {y})" by blast
          hence "\<ominus>\<^bsub>M\<^esub>z \<in> Span R M (V \<union> (J - V-L - {y}))"
            using  yz(2)Span.a_inv[of z R M "(J - V - L - {y})"]calculation
            by (metis Span_mono insert_Diff insert_subset sup_ge2)
          ultimately have "\<ominus>\<^bsub>M\<^esub>z \<oplus>\<^bsub>M\<^esub> x \<in> Span R M (V \<union> (J - V-L - {y}))"
            using Span.eng_add[OF _ hyp, of "\<ominus>\<^bsub>M\<^esub>z"] by metis
          moreover have "\<ominus>\<^bsub>M\<^esub>z \<oplus>\<^bsub>M\<^esub> x = y2"
            using Span_in_carrier yz M.r_neg1[of z y2]
            by (meson Diff_subset empty_subsetI insert.prems(2) insert_subset subset_trans)
          ultimately have "y2 \<in> Span R M (V \<union> (J - V-L - {y}))" by auto
          moreover have "V \<union> (J - V-L - {y}) \<union>  {y} = V \<union> (J - L)" using yz(1) by auto
          moreover have "(V \<union> (J - V - L - {y})) \<inter> {y} = {}"
            using yz(1) by blast
          ultimately show False
            using L_def(2) indep_inter_null[of "V \<union> (J - V-L - {y})" "{y}"] yz(1,3,4) by auto
        qed
        moreover have "(V \<union> (J - V - L - {y})) = (V \<union> (J  - L - {y}))" by blast
        ultimately have xSpan : "x \<notin> Span R M (V \<union> (J - L - {y}))" by auto
        hence "x \<notin> ((V \<union> (J - L - {y})))" using Span.incl[of x "(V \<union> (J - L - {y}))"] by auto
        hence inter : "S \<inter> (J - L - {y}) = {}"
          using V_def L_def(5) by blast
        have "(insert x V) \<union> (J - L - {y}) = insert x (V \<union> (J - L - {y}))" by blast
        hence "lin_indep R M ((insert x V) \<union> (J - L - {y}))"
          using add_vector_indep[OF lin_indep_incl[OF L_def(2),of "(V \<union> (J - L - {y}))"], of x] insert(4)
                 subsetCE xSpan by force
        hence "lin_indep R M (S \<union> (J - L - {y}))" using V_def by auto
        moreover have "y \<notin> L" using yz(1) by auto
        hence "card (insert y L) = card V + 1" using L_def(3,4) by auto
        hence "card (insert y L) = card S"
          using V_def finite_subset[OF S_def] insert(1) by simp
        moreover have "finite (insert y L)" using L_def(4) by auto
        moreover have "(S \<union> (J - (insert y L))) = (S \<union> (J - L - {y}))"by auto
        ultimately show ?thesis using inter L_def(1) yz(1)
          by (metis DiffD1 Diff_insert insert_subset) 
      next
        case False
        note F = this
        show ?thesis
        proof (cases "x \<in> Span R M (V\<union>(J-L-V))")
          case True
          have "(V\<union>(J-L-V)) = (V\<union>(J-L))" by simp
          hence indep3 : "lin_indep R M (V\<union>(J-L-V))" using L_def(2) by auto
          from vector_unique_decomposition[OF indep3 _ True] obtain x1 x2
            where x1x2 : "x1 \<in> Span R M V"  "x2 \<in> Span R M (J - L - V)" "x1 \<oplus>\<^bsub>M\<^esub> x2 = x"
           "(\<forall>y z. y \<in> Span R M V \<and> z \<in> Span R M (J - L - V) \<and> y \<oplus>\<^bsub>M\<^esub> z = x \<longrightarrow> y = x1 \<and> z = x2)"
            by auto
          have carrier : "x \<in> carrier M""x1 \<in> carrier M""x2 \<in> carrier M"
            using insert(4,5) Span_in_carrier x1x2(1,2) indep2 Span_mono[of "J-L-V" J]
            by auto+           
          have x20 : "x2 \<noteq> \<zero>\<^bsub>M\<^esub>"
          proof
            assume hyp : "x2 = \<zero>\<^bsub>M\<^esub>"
            hence "x = x1" using carrier x1x2(3) M.l_zero[of x1] by auto
            thus False using x1x2(1)notx indep by auto
          qed
          from non_null_decomposition[OF _ x1x2(2) x20] insert(5) obtain y z y2
            where yz : "y\<in>J-L-V" "z\<in>Span R M (J-L-V-{y})" "y2\<in>Span R M {y}"
                       "y2 \<noteq> \<zero>\<^bsub>M\<^esub>" "z \<oplus>\<^bsub>M\<^esub> y2 = x2"
            by auto
          have x2_not_incl : "x2 \<notin> Span R M (J-L-V-{y})"
          proof
            assume hyp : "x2 \<in> Span R M (J - L - V-{y})"
            hence "\<ominus>\<^bsub>M\<^esub>z \<oplus>\<^bsub>M\<^esub> x2 \<in> Span R M (J-L-V-{y})"
              using yz(2) Span.a_inv[OF yz(2)] Span.eng_add[of "\<ominus>\<^bsub>M\<^esub>z", OF _ hyp] by auto
            moreover have "\<ominus>\<^bsub>M\<^esub>z \<oplus>\<^bsub>M\<^esub> x2 = y2"
              using carrier(3) yz Span_mono Span_in_carrier M.r_neg1[of z y2]
              by (meson Diff_subset  empty_subsetI insert.prems(2) insert_subset subset_trans)
            ultimately have "y2 \<in> Span R M (J - L - V - {y}) \<inter> Span R M {y}" using yz(3) by auto
            moreover have "(J - L - V - {y} \<union> {y}) = (J - L - V)" using yz(1) by blast
            hence "lin_indep R M (J - L - V - {y} \<union> {y})"
              using lin_indep_trunc[OF lin_indep_trunc[OF insert(5), of L]] by auto
            ultimately show False using yz(4) using indep_inter_null[of "(J - L - V - {y})""{y}"]
              by auto
          qed
          have xSpan :  "x \<notin> Span R M (V \<union> (J - L - {y}))"
          proof
            assume hyp : "x \<in> Span R M (V \<union> (J - L - {y}))"
            hence hyp2 : "x \<in> Span R M (V \<union> (J - L - V - {y}))"
              by (metis Diff_insert Diff_insert2 Un_Diff_cancel)
            from vector_decomposition[OF _ _ hyp2] indep2 lin_indep_incl[OF insert(5)] obtain z1 z2 
              where z1z2 : "z1 \<in> Span R M V"  "z2 \<in> Span R M (J-L-V-{y})" "z1 \<oplus>\<^bsub>M\<^esub> z2 = x"
              by auto
            hence "z2 \<in> Span R M (J-L-V)"
              using Span_mono[of "J-L-V-{y}" "J-L-V"] lin_indep_incl[OF L_def(2), of "J-L"] by auto 
            hence "z2 = x2" using x1x2(4) z1z2 by auto      
            thus False using z1z2(2) x2_not_incl by auto
          qed
          hence"lin_indep R M (insert x (V \<union> (J - L - {y})))"
            using add_vector_indep[OF lin_indep_incl[OF L_def(2),of "V \<union> (J-L-{y})"],of x] carrier
            by fastforce
          moreover from xSpan have "x \<notin> (V \<union> (J - L - {y}))"
            using Span.incl[of x "V \<union> (J - L - {y})"] by auto
          hence "S \<inter> (J - L - {y}) = {}"
            using V_def L_def(5) by blast
          moreover have "y \<notin> L" using yz(1) by auto
          hence "card (insert y L) = card V + 1" using L_def(3,4) by auto
          hence "card (insert y L) = card S"
            using V_def finite_subset[OF S_def] finite_insert[of F] insert(1) by auto
          moreover have "finite (insert y L)" using L_def(4) finite_insert by auto
          moreover have "(insert y L) \<subseteq> J" using L_def(1) yz(1) by auto
          moreover have "V \<union> (J - L - {y}) = V \<union> (J - insert y L)" by blast
          hence "insert x (V \<union> (J - L - {y})) = S \<union> (J - insert y L)"
            using yz(1) V_def by blast
          ultimately show ?thesis by (metis Diff_insert)
        next
          case False
          have "(V \<union> (J - L - V)) = (V \<union> (J - L))" by blast
          hence "x \<notin> Span R M (V \<union> (J - L))" using False by auto
          hence "lin_indep R M (insert x (V \<union> (J - L)))"
            using add_vector_indep[OF L_def(2), of x] insert(4) by auto
          moreover have "insert x (V \<union> (J - L)) = insert x V \<union> (J - L)" by blast
          hence "insert x (V \<union> (J - L)) = S \<union> (J - L)"
            using V_def by auto
          ultimately have "lin_indep R M (S \<union> (J - L))" by auto
          moreover have "\<exists> y. y \<in> (J-L)"
            using insert(1,6) L_def(3,4) inclF card_insert_le[OF insert(1), of x]
            by (metis Diff_subset_conv L_def(1) Un_absorb1 Un_absorb2 card_seteq
                finite_insert insert.hyps(2) insertI1 subsetI subset_Diff_insert)
          from this obtain y where y : "y \<in> J-L" by auto
          ultimately have "lin_indep R M (S \<union> (J - insert y L))"
            using lin_indep_incl[of "(S \<union> (J - L))" "(S \<union> (J - insert y L))"] by fastforce
          moreover have  "y \<notin> L" using y by simp
          hence "card (insert y L) = card V + 1" using L_def(3,4) by auto
          hence "card (insert y L) = card S"
            using V_def finite_subset[OF S_def] finite_insert[of F] insert(1) by auto
          moreover have "finite (insert y L)" using L_def(4) finite_insert by auto
          moreover have "(insert y L) \<subseteq> J" using L_def(1) y by auto
          moreover from False have "x \<notin> (V \<union> (J - L)) "
            using Span.incl[of x "(V \<union> (J - L - V)) "] by auto
          hence "S \<inter> (J - (insert y L)) = {}"
            using L_def(5) V_def by blast
          ultimately show ?thesis by blast
        qed
      qed
    qed}
  thus ?case by auto
qed

lemma (in vector_space) finite_dim_imp_finite_base :
  assumes "finite_dim R M K"
    and "base R M S K"
    and "dim K = n"
  shows "finite S"
proof (rule ccontr)
  assume infinity : "infinite S"
  have n_def : "n = (LEAST n. (\<exists> A. finite A \<and> card A = n  \<and>  generator R M A K))" using assms
    by (simp add: dim_def)
  moreover have "(\<exists> A. finite A \<and>  generator R M A K)"
    using assms(1) unfolding finite_dim_def by simp
  ultimately have "(\<exists> A. finite A \<and> card A = n \<and> generator R M A K)" using assms
    by (smt LeastI)
  from this obtain A where A_def : "finite A" "card A = n" "generator R M A K" by auto
  have indep_A :"lin_indep R M A"
  proof
    show "A \<subseteq> carrier M" using A_def unfolding generator_def by auto
    {fix I assume I_def : "I \<subset> A" have "Span R M I \<subset> Span R M A"
      proof
        show "Span R M I \<subseteq> Span R M A"
          using Span_mono[of I A] I_def A_def(3) unfolding generator_def by auto
        show "Span R M I \<noteq> Span R M A "
        proof
          assume hyp : "Span R M I = Span R M A"
          hence "Span R M I = K" using A_def unfolding generator_def by auto
          moreover have "card I < n" using I_def A_def
            using psubset_card_mono by blast
          moreover have "finite I" using A_def I_def infinite_super by blast
          ultimately show False using n_def A_def(3) unfolding generator_def
            by (smt I_def not_less_Least psubsetE psubset_subset_trans)
        qed
      qed}
    thus "\<forall>S\<subset>A. Span R M S \<subset> Span R M A" by simp
  qed
  from infinity obtain S2
    where S2 :"finite S2""S2 \<subseteq> S""card S2 \<ge> (n + n + 1)"
    by (metis infinite_arbitrarily_large order_refl)
  hence "card S2 \<ge> n" by auto
  from this S2(1,2) obtain V where V_def : "finite V""card V = card A" "lin_indep R M (A \<union> (S2 - V))"
    using extended_replacement_theorem[OF A_def(1), of S2]lin_indep_incl[OF _ S2(2)] A_def(2) indep_A
            assms(2) unfolding base_def by auto
  have "card (A \<union> V) \<le> n + n" using A_def(1,2) V_def(1,2)
    by (metis card_Un_le)
  hence "S2 - (A \<union> V) \<noteq> {} "
    using S2  A_def(1) V_def(1) card_seteq  diff_is_0_eq' Diff_eq_empty_iff diff_add_inverse
    by (metis One_nat_def add.right_neutral add_Suc_right finite_UnI le_SucI le_trans nat.simps(3))
  moreover have "(A \<union> (S2 - (A \<union> V))) = (A \<union> (S2 - V))" by blast
  ultimately have "A \<subset> (A \<union> (S2 - V))"  by blast
  moreover have "Span R M (A \<union>(S2 - V)) \<subseteq> K"
    using assms A_def S2(2) unfolding generator_def base_def
    by (smt Diff_subset SpanE(2) Span_is_submodule Span_min_submodule1 Un_least subset_trans) 
    
  ultimately show False using V_def(2,3) A_def(3) unfolding generator_def by blast    
qed

proposition (in vector_space) dimension_unique :
  assumes "finite_dim R M K"
    and "base R M S K"
    and "dim K = n"
  shows "card S = n"
proof (rule ccontr)
  assume hyp : "card S \<noteq> n"
  have finite : "finite S" using assms finite_dim_imp_finite_base by auto
  have n_def : "n = (LEAST n. (\<exists> A. finite A \<and> card A = n  \<and>  generator R M A K))" using assms
    by (simp add: dim_def)
  moreover have "(\<exists> A. finite A \<and>  generator R M A K)"
    using assms(1) unfolding finite_dim_def by simp
  ultimately have "(\<exists> A. finite A \<and> card A = n \<and> generator R M A K)" using assms
    by (smt LeastI)
  from this obtain A where A_def : "finite A" "card A = n" "generator R M A K" by auto
  have indep_A :"lin_indep R M A"
  proof
    {fix I assume I_def : "I \<subset> A" have "Span R M I \<subset> Span R M A"
      proof
        show "Span R M I \<subseteq> Span R M A"
          using Span_mono[of I A] I_def A_def(3) unfolding generator_def by auto
        show "Span R M I \<noteq> Span R M A "
        proof
          assume hyp : "Span R M I = Span R M A"
          hence "Span R M I = K" using A_def unfolding generator_def by auto
          moreover have "card I < n" using I_def A_def
            using psubset_card_mono by blast
          moreover have "finite I" using A_def I_def infinite_super by blast
          ultimately show False using n_def A_def(3) unfolding generator_def
            by (smt I_def not_less_Least psubsetE psubset_subset_trans)
        qed
      qed}
    thus "\<forall>S\<subset>A. Span R M S \<subset> Span R M A" by simp
    show "A \<subseteq> carrier M" using A_def unfolding generator_def by auto
  qed
  show False
  proof (cases "card S \<ge> n")
    case True
    from this extended_replacement_theorem[OF A_def(1)indep_A, of S]
    obtain V
      where V_def : "V\<subseteq>S" "finite V" "card V = card A" "A \<inter> (S - V) = {}"
                    "lin_indep R M (A \<union> (S - V))"
      using A_def(2) assms(2) unfolding base_def by force
    have "S-V \<noteq> {}" using V_def(1,3) True A_def(2) hyp by auto
    hence "A \<subset> (A \<union> (S - V))"
      using V_def(3,4) by auto
    moreover have "Span R M (A \<union>(S - V)) \<subseteq> K"
      using assms A_def V_def(1) Span_union unfolding generator_def base_def
      by (smt Diff_partition Un_subset_iff set_eq_subset sup.right_idem)
    ultimately show ?thesis
      using assms(2) A_def(3) V_def(5) unfolding base_def
      by (metis generator_def psubsetE)
  next
    case False
    define m where m : "m = card S"
    hence "m < n" using False by linarith
    moreover have "finite S \<and> card S = m \<and> generator R M S K"
      using assms(2) m finite unfolding base_def by auto
    ultimately show False using assms(3) not_less_Least unfolding dim_def by auto
  qed
qed



end