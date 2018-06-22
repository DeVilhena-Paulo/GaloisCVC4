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
  where "dim K \<equiv> LEAST n. (\<exists> A. finite A \<and> card A = n  \<and>  generator R M K A)"

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

lemma (in vector_space) not_in_span_imp_no_Span_inter :
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


lemma (in vector_space) two_vectors_exchange :
  assumes "lin_indep R M A"
    and "y \<in> carrier M"
    and "y \<notin> Span R M A"
  shows "lin_indep R M (insert y A)"
proof
  show A1 : "insert y A \<subseteq> carrier M" using assms by auto
  show "\<forall>S\<subset>insert y A. Span R M S \<subset> Span R M (insert y A)"
  proof (cases "A = {}")
    case True
    thus ?thesis using vector_indep[OF assms(2)] assms Span.zero[of M R A]
      by auto
  next
    case False
    {fix S assume S_def : "S \<subset> insert y A" have "Span R M S \<subset> Span R M (insert y A)" 
    proof-
      from S_def have S_carrier : "S \<subseteq> carrier M" using A1 by auto
      show "Span R M S \<subset> Span R M (insert y A)" 
      proof(cases "y \<in> S")
        case True
        have S1 : "S - {y} \<subset> A" using S_def True by auto
        hence "A - S \<noteq> {}" using S_def by auto
        hence  x1 : "\<exists> x \<in> (A - S). x \<noteq> \<zero>\<^bsub>M\<^esub>"
          using assms zero_imp_dep[of "(A - S)"] False lin_indep_not_dep[of "(A - S)"]
              lin_indep_trunc[OF assms(1), of "S"]
          by (metis all_not_in_conv)
        from x1 obtain x where x_def : "x \<in> (A - S)""x \<noteq> \<zero>\<^bsub>M\<^esub>" by auto
        have x_prop :  "x \<notin> Span R M (S - {y})"
        proof
          assume hyp : "x \<in> Span R M (S - {y})"
          have "S - {y} \<subset> insert x (S - {y})"
            using x_def by auto
          moreover have "A - (A - (insert x (S - {y}))) = insert x (S - {y})" using S1 x_def
            by blast
          hence "lin_indep R M (insert x (S - {y}))"
            using lin_indep_trunc[OF assms(1), of "(A - (insert x (S - {y})))"] x_def
            by simp
          ultimately show False using  S1 assms(1) x_def (1)
           elt_in_Span_imp_Span_idem[of "S - {y}" x, OF _ hyp]
            by (metis insert_subset psubset_eq)
        qed
        have "x \<notin> Span R M S" apply auto
        proof-
          assume hyp : "x \<in> Span R M S"
          hence "\<exists> z1 z2. z1 \<in> Span R M (S - {y}) \<and> z2 \<in> Span R M {y} \<and> z1 \<oplus>\<^bsub>M\<^esub> z2 = x"
            using vector_decomposition[of "S - {y}" "{y}" x] S1 assms True insert_subset Un_commute
            by (smt empty_subsetI insert_Diff insert_is_Un psubset_imp_subset psubset_subset_trans)
          from this obtain z1 z2 
            where z1z2 : " z1 \<in> Span R M (S - {y})" "z2 \<in> Span R M {y}" "z1 \<oplus>\<^bsub>M\<^esub> z2 = x"
            by auto
          hence z1Span : "z1 \<in> Span R M A" using Span_mono[of "S - {y}" A] S1 assms by auto
          hence "\<ominus>\<^bsub>M\<^esub> z1 \<in> Span R M A" using Span.a_inv[of z1 R] by auto
          hence "\<ominus>\<^bsub>M\<^esub> z1 \<oplus>\<^bsub>M\<^esub> x \<in> Span R M A"
            using Span.eng_add[of "\<ominus>\<^bsub>M\<^esub> z1" R M A x] x_def(1) Span.incl[of x A] by auto
          hence z2Span : "z2 \<in> Span R M A"
            using z1z2 M.l_neg[of z1] Span_in_carrier assms S1 M.a_assoc
            by (metis M.r_neg1 z1Span empty_subsetI insert_subset)
          have "z2 \<in> {k \<odot>\<^bsub>M\<^esub> y |k. k \<in> carrier R}"
            using Span_singleton[OF assms(2)] z1z2 by auto
          moreover have "z2 \<noteq> \<zero>\<^bsub>M\<^esub>"
          proof
            assume hyp2 : "z2 = \<zero>\<^bsub>M\<^esub>"
            hence "x = z1"
              using M.r_zero[of z1] z1z2(1,3) Span_in_carrier S1 assms(1) 
              by (metis (no_types, lifting) S_carrier True insert_Diff insert_subset)
            thus False using z1z2 x_prop by auto
          qed
          ultimately have "\<exists> k. k \<in> carrier R \<and> z2 = k \<odot>\<^bsub>M\<^esub> y \<and> k \<noteq> \<zero>"
            using smult_l_null[of y] assms(2) by blast 
          from this obtain k where k_def : "k \<in> carrier R" "z2 = k \<odot>\<^bsub>M\<^esub> y" "k \<noteq> \<zero>" by auto
          hence invk : "inv k \<in> carrier R"
            using field_Units by auto
          hence "inv k \<odot>\<^bsub>M\<^esub> z2 \<in> Span R M A"
            using hyp Span.eng_smult[of "inv k" R] z2Span by auto
          moreover have "inv k \<odot>\<^bsub>M\<^esub> z2 = y"
            using k_def field_Units smult_assoc1[of "inv k" k y] assms invk
            by simp
          ultimately show False using assms by auto
        qed
        thus "Span R M S \<subset> Span R M (insert y A)"
          using x_def Span.incl[of x "insert y A" R M] A1 S_def
          by (metis DiffD1 insertI2 module.Span_mono module_axioms psubsetI psubset_imp_subset)
      next
        case False
        hence "Span R M S \<subseteq> Span R M (A)"
          using S_def Span_mono[of S A] assms by blast
        hence "y \<notin> Span R M S" using assms by auto
        moreover have "y \<in> Span R M (insert y A)" using Span.incl[of y "insert y A"] by auto
        moreover have "Span R M S \<subseteq> Span R M (insert y A)" using Span_mono S_def assms by auto
        ultimately show ?thesis by auto
      qed
      qed}
    thus "\<forall>S\<subset>insert y A. Span R M S \<subset> Span R M (insert y A)" by auto
  qed
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
      from this obtain y1 y2 
        where y1y2 : "y1 \<in> Span R M (F - {z})" "y2 \<in> Span R M {x}" "y1 \<oplus>\<^bsub>M\<^esub> y2 = y"
        using vector_decomposition[of "F - {z}" "{x}" y] insert(4) insert_is_Un insert_absorb z_def
        by (smt Diff_insert_absorb Diff_subset True Un_insert_right empty_subsetI insert_Diff_single 
                insert_subset sup_bot.right_neutral)
      have "y2 \<noteq> \<zero>\<^bsub>M\<^esub>"
      proof
        assume "y2 = \<zero>\<^bsub>M\<^esub>"
        then have "y = y1" using y1y2 Span_in_carrier insert(4) z_def
          by (metis Span.eng_add Span.zero)
        thus False using y1y2(1) z_def by auto
      qed
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
    have y20 : "y2 \<noteq> \<zero>\<^bsub>M\<^esub>"
    proof
      assume "y2 = \<zero>\<^bsub>M\<^esub>"
      then have "x = y1" using y1y2 Span_in_carrier y_def
        by (meson Span.eng_add Span.zero)
      thus False using y1y2(1) y_def by auto
    qed
    have "y2 \<in> {k \<odot>\<^bsub>M\<^esub> y |k. k \<in> carrier R}"
      using Span_singleton[OF y_def(1)] y1y2(2) by auto
    from this obtain k where k_def : "k \<in> carrier R" "y2 = k \<odot>\<^bsub>M\<^esub> y" by auto
    hence k0 : "k \<noteq> \<zero>"
      using y20 smult_l_null[OF y_def(1)] by auto
    hence inv : "inv k \<in> carrier R" using field_Units k_def by blast
    have "A - {y} - (S - {y})= (A - S)"
      using S_def Diff_insert0 y_def(2) by auto
    from hyp this obtain z1 z2
      where z1z2 : "z1 \<in> Span R M (S - {y})" "z2 \<in> Span R M (A - S)" "z1 \<oplus>\<^bsub>M\<^esub> z2 = x"
      using vector_decomposition[of "S - {y}" "A-{y} - (S - {y})"] insert_is_Un insert_absorb assms
      by (smt Diff_empty Diff_insert0 Diff_partition Un_subset_iff insert_Diff subset_insert_iff S_def)
    have "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> y1 \<oplus>\<^bsub>M\<^esub> x) \<in> Span R M ((A - {y}))"
      using hyp z1z2(1) Span.a_inv[OF y1y2(1)] Span.eng_add[OF _ hyp, of "\<ominus>\<^bsub>M\<^esub> y1"] assms(1)S_def(1)
            Span.eng_smult[OF inv, of "(\<ominus>\<^bsub>M\<^esub> y1 \<oplus>\<^bsub>M\<^esub> x)" M "A-{y}"] Span_mono[of "S-{y}" "A-{y}"]
      by (metis (no_types, hide_lams) Diff_empty Diff_mono Diff_subset lin_indep_trunc subsetCE)
    moreover have "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> y1 \<oplus>\<^bsub>M\<^esub> x) = inv k \<odot>\<^bsub>M\<^esub> (\<zero>\<^bsub>M\<^esub> \<oplus>\<^bsub>M\<^esub> y2)"
      using y1y2 M.l_neg M.l_zero M.r_neg1 Span_in_carrier smult_closed y_def(1) insert_subset
            S_def(1) assms(1) k_def
      by (metis (no_types, lifting) Diff_empty Diff_insert0 insert_Diff subset_trans)
      hence "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> y1 \<oplus>\<^bsub>M\<^esub> x) = inv k \<odot>\<^bsub>M\<^esub> (k \<odot>\<^bsub>M\<^esub> y)"
        using M.l_zero[OF smult_closed[OF k_def(1) y_def(1)]] k_def y_def(1) by auto
      hence "inv k \<odot>\<^bsub>M\<^esub> (\<ominus>\<^bsub>M\<^esub> y1 \<oplus>\<^bsub>M\<^esub> x) = y"
        using smult_assoc1[OF inv k_def(1)] by (simp add: k0 k_def(1)field_Units y_def(1)) 
      ultimately have "y \<in> Span R M (A - {y})" by auto
      thus False using vector_in_Span_imp_dep[of "A-{y}" y] assms lin_indep_not_dep y_def singletonI
        by (metis (no_types, lifting) DiffE Diff_empty Diff_insert0 S_def insert_Diff insert_subset)
    qed
    then show ?thesis
      using two_vectors_exchange[of "A - {y}" x] assms lin_indep_trunc by auto
next
  case False
  then show ?thesis
    using two_vectors_exchange[OF assms(1) _ False] assms lin_indep_trunc[of "insert x A"]
    by (metis Diff_idemp Diff_insert_absorb insert_subset lin_indep_not_dep zero_imp_dep)
qed



end