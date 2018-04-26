theory Sym_Groups
  imports Group Bij Main (* "HOL-Library.Permutations"*)
    
begin

section \<open>Symetric Groups\<close>

definition
  sym_group :: "nat \<Rightarrow> (nat \<Rightarrow> nat) monoid"
  where "sym_group n = BijGroup({1..n})"

definition
  inversions :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<times> nat) set"
  where "inversions n \<sigma> = {(x, y) \<in> ({1..n} \<times> {1..n}). x > y \<and> \<sigma> x < \<sigma> y}"

definition
  signature :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> int"
  where "signature n \<sigma> = (-1) ^ card (inversions n \<sigma>)"

syntax
  "_sym_group" :: "index \<Rightarrow> (nat \<Rightarrow> nat) monoid" ("(\<S>_)" [1000])
  "_signature" :: "index \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> int" ("(\<epsilon>_)" [1000])
translations
  "\<S>\<^bsub>n\<^esub>" \<rightleftharpoons> "CONST sym_group n"
  "\<epsilon>\<^bsub>n\<^esub>" \<rightleftharpoons> "CONST signature n"



subsection \<open>Prelimineries\<close>

lemma group_prop1: "group \<S>\<^bsub>n\<^esub>"
  by (simp add: group_BijGroup sym_group_def)

lemma group_prop2:
  "group \<lparr> carrier = {-1, 1}, mult = (op * ), one = 1 \<rparr>"
proof -
  have "group \<lparr> carrier = {-1, 1}, mult = (\<lambda>x. \<lambda>y. if x = y then 1 else -1), one = 1 \<rparr>"
    apply (intro groupI)
    apply simp_all
    by (blast)+
  moreover have "\<And>x y. \<lbrakk> x \<in> {-1, 1}; y \<in> {-1, 1} \<rbrakk> \<Longrightarrow> x * y = (if x = y then 1 else -1)"
    sorry
  ultimately show ?thesis sorry
qed

lemma group_prop3:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "\<And>x. x \<in> {1..n} \<Longrightarrow> \<sigma> ((inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>) x) = x"
proof -
  have inv_included: "(inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>) \<in> carrier \<S>\<^bsub>n\<^esub>"
    using group_prop1 assms by auto
  fix x assume x: "x \<in> {1..n}"
  have "\<sigma> ((inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>) x) = (compose {1..n} \<sigma> (inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>)) x"
    by (metis x compose_eq)
  also have " ... = (\<sigma> \<otimes>\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> (inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>)) x"
    using BijGroup_def inv_included assms sym_group_def
    by (smt monoid.select_convs(1) partial_object.select_convs(1) restrict_apply) 
  finally show "\<sigma> ((inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>) x) = x"
    by (smt BijGroup_def assms group.r_inv group_BijGroup monoid.select_convs(2)
        restrict_apply sym_group_def x)
qed

lemma ext_prop:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
    shows "\<sigma> \<in> extensional {1..n}"
  using assms unfolding sym_group_def BijGroup_def Bij_def by simp 

lemma bij_prop:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
    shows "bij_betw \<sigma> {1..n} {1..n}"
  using assms unfolding sym_group_def by (simp add: BijGroup_def Bij_def)

lemma inj_prop:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "\<And>x1 x2. \<lbrakk> x1 \<in> {1..n}; x2 \<in> {1..n} \<rbrakk> \<Longrightarrow> \<sigma> x1 = \<sigma> x2 \<Longrightarrow> x1 = x2"
  using bij_prop[OF assms(1)] bij_betw_def inj_on_def by metis

lemma surj_prop:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "\<sigma> ` {1..n} = {1..n}"
  using bij_prop[OF assms(1)] bij_betw_def by metis

lemma exp_prop1:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "\<sigma> (^)\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> m = restrict (\<sigma> ^^ m) {1..n}" using assms
proof (induction m)
  case 0 thus ?case
    using BijGroup_def group_def funpow_0 group_BijGroup monoid.nat_pow_0
          monoid.simps(2) restrict_ext sym_group_def by metis
next
  case (Suc m')
  have "\<sigma> (^)\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> (Suc m') = \<sigma> \<otimes>\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> (\<sigma> (^)\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> m')"
    by (smt Group.group_def Groups.add_ac(2) assms group.int_pow_1 group.int_pow_def2
            group_BijGroup monoid.nat_pow_Suc monoid.nat_pow_mult sym_group_def) 
  also have " ... = compose {1..n} \<sigma> (\<sigma> (^)\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> m')"
    by (smt BijGroup_def Group.group_def assms group_BijGroup monoid.nat_pow_closed
        monoid.simps(1) partial_object.select_convs(1) restrict_apply sym_group_def)
  also have " ... = compose {1..n} \<sigma> (restrict (\<sigma> ^^ m') {1..n})" using Suc by presburger 
  also have " ... = restrict (\<sigma> ^^ (Suc m')) {1..n}"
    by (smt comp_apply compose_def funpow.simps(2) restrict_apply restrict_ext) 
  finally show ?case .
qed

lemma exp_prop2:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "restrict (\<sigma> ^^ m) {1..n} \<in> carrier \<S>\<^bsub>n\<^esub>"
  using Group.group_def assms exp_prop1 group_BijGroup
        monoid.nat_pow_closed sym_group_def by fastforce

lemma exp_prop3:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "(\<sigma> ^^ m) ` {1..n} = {1..n}"
  by (metis assms exp_prop2 image_restrict_eq surj_prop)

lemma exp_prop4:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "\<And>x1 x2. \<lbrakk> x1 \<in> {1..n}; x2 \<in> {1..n} \<rbrakk> \<Longrightarrow> (\<sigma> ^^ m) x1 = (\<sigma> ^^ m) x2 \<Longrightarrow> x1 = x2"
  by (metis assms exp_prop2 inj_prop restrict_apply)
  
lemma exp_prop5:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>" "x \<in> {1..n}"
    and "i < j" "(\<sigma> ^^ i) x = (\<sigma> ^^ j) x"
  shows "(\<sigma> ^^ (j - i)) x = x" using assms
proof -
  have "(\<sigma> ^^ i) ((\<sigma> ^^ (j - i)) x) = (\<sigma> ^^ j) x"
    by (metis add_diff_inverse_nat assms(3) comp_apply
        dual_order.strict_trans funpow_add less_not_refl2)
  hence "(\<sigma> ^^ i) ((\<sigma> ^^ (j - i)) x) = (\<sigma> ^^ j) x" using assms(4) by simp
  thus ?thesis using exp_prop3 exp_prop4 assms imageI by metis
qed

lemma exp_prop6:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>" "x \<in> {1..n}"
    and "(\<sigma> ^^ k) x = x"
  shows "(\<sigma> ^^ (k * l)) x = x" using assms
proof (induction l)
  case 0 thus ?case by simp
next
  case (Suc l)
  have "(\<sigma> ^^ (k * (Suc l))) x = (\<sigma> ^^ k) ((\<sigma> ^^ (k * l)) x)"
    by (simp add: funpow_add)
  also have " ... = (\<sigma> ^^ k) x"
    using Suc.IH assms by auto
  also have " ... = x" by (simp add: assms(3)) 
  finally show ?case .
qed



subsection \<open>Cycles as Equivalence Classes\<close>

lemma cyclic_prop1:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>" "x \<in> {1..n}"
  shows "\<exists>n. (\<sigma> ^^ n) x = x \<and> n > 0"
proof (rule ccontr)
  assume Hyp: "\<nexists>n. (\<sigma> ^^ n) x = x \<and> 0 < n"
  have "\<And>i j. j > i \<Longrightarrow> (\<sigma> ^^ i) x \<noteq> (\<sigma> ^^ j) x"
  proof (rule ccontr)
    fix i j assume "i < j" "\<not> (\<sigma> ^^ i) x \<noteq> (\<sigma> ^^ j) x"
    hence "(\<sigma> ^^ (j - i)) x = x" using exp_prop5[OF assms(1) assms(2)] by simp
    thus False using Hyp \<open>i < j\<close> zero_less_diff by blast
  qed
  hence "\<And>i j. \<lbrakk> i \<ge> 0; j \<ge> 0 \<rbrakk> \<Longrightarrow> (\<sigma> ^^ i) x = (\<sigma> ^^ j) x \<Longrightarrow> i = j"
    using nat_neq_iff by meson
  moreover have "(\<lambda>i.(\<sigma> ^^ i) x) ` {i. i \<ge> 0} = {(\<sigma> ^^ i) x | i. i \<ge> 0}"
    by blast
  ultimately have
    "bij_betw (\<lambda>i.(\<sigma> ^^ i) x) {i. i \<ge> 0} {(\<sigma> ^^ i) x | i. i \<ge> 0}"
    by (metis (no_types, lifting) bij_betw_imageI inj_on_def mem_Collect_eq)
  (*note [[show_consts]]*)
  hence "infinite {(\<sigma> ^^ i) x | i. i \<ge> 0}"
    using bij_betw_finite by auto
  moreover have "{(\<sigma> ^^ i) x | i. i \<ge> 0} \<subseteq> {1..n}"
    using exp_prop3[OF assms(1)] assms(2) by blast
  hence "finite {(\<sigma> ^^ i) x | i. i \<ge> 0}" by (simp add: finite_subset)
  ultimately show False by simp
qed

corollary cyclic_prop2:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>" "x \<in> {1..n}"
  shows "\<And>m. \<exists>n. (\<sigma> ^^ n) x = x \<and> n > m"
proof -
  fix m
  obtain n l where "n > 0" "n * l > m" "(\<sigma> ^^ n) x = x"
    using cyclic_prop1[OF assms(1) assms(2)] split_div_lemma by blast
  thus "\<exists>n. (\<sigma> ^^ n) x = x \<and> n > m" using exp_prop6[OF assms(1-2)] by auto
qed

lemma cycle_refl:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>" "x \<in> {1..n}"
  shows "\<exists>k. (\<sigma> ^^ k) x = x"
  using assms cyclic_prop1 by blast

lemma cycle_sym:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
    and "x \<in> {1..n}" "y \<in> {1..n}"
    and "\<exists>i. (\<sigma> ^^ i) x = y"
  shows "\<exists>j. (\<sigma> ^^ j) y = x"
proof -
  obtain n i where n: "(\<sigma> ^^ n) x = x" "n > i"
               and i: "(\<sigma> ^^ i) x = y" using cyclic_prop2[OF assms(1-2)] assms(4) by blast
  have "x = (\<sigma> ^^ n) x" using n by simp
  also have " ... = (\<sigma> ^^ (n - i)) ((\<sigma> ^^ i) x)"
    by (smt Groups.add_ac(2) add_Suc_right add_diff_cancel_left'
        comp_eq_dest_lhs funpow_add less_imp_Suc_add n i)
  also have " ... = (\<sigma> ^^ (n - i)) y" using i by simp
  finally have "x = (\<sigma> ^^ (n - i)) y" .
  thus ?thesis by blast
qed

lemma cycle_trans:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
    and "x \<in> {1..n}" "y \<in> {1..n}" "z \<in> {1..n}"
    and "\<exists>i. (\<sigma> ^^ i) x = y" "\<exists>j. (\<sigma> ^^ j) y = z"
  shows "\<exists>k. (\<sigma> ^^ k) x = z"
proof -
  obtain i j where i: "(\<sigma> ^^ i) x = y" and j: "(\<sigma> ^^ j) y = z" using assms(5-6) by blast
  have "(\<sigma> ^^ (i + j)) x = (\<sigma> ^^ j) ((\<sigma> ^^ i) x)"
    by (metis add.commute comp_apply funpow_add)
  hence "(\<sigma> ^^ (i + j)) x = z" using i j by simp
  thus ?thesis by blast
qed

theorem equivalence_from_cycles:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "equivalence \<lparr> carrier = {1..n}, eq = (\<lambda>x. \<lambda>y. \<exists>i. (\<sigma> ^^ i) x = y) \<rparr>"
  using equivalenceI[where ?P = "(\<lambda>x. \<lambda>y. \<exists>i. (\<sigma> ^^ i) x = y)" and ?E = "{1..n}"]
        cycle_refl[OF assms] cycle_sym[OF assms] cycle_trans[OF assms] by blast

corollary partition_from_cycles:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "partition {1..n} {{(\<sigma> ^^ i) x | i. i \<ge> 0} | x. x \<in> {1..n}}"
proof -
  have "\<And>x. x \<in> {1..n} \<Longrightarrow> {(\<sigma> ^^ i) x | i. i \<ge> 0} = {y \<in> {1..n}. \<exists>i. (\<sigma> ^^ i) x = y}"
    using assms exp_prop3 by blast
  hence "{{(\<sigma> ^^ i) x | i. i \<ge> 0} | x. x \<in> {1..n}} =
         classes\<^bsub>\<lparr> carrier = {1..n}, eq = (\<lambda>x. \<lambda>y. \<exists>i. (\<sigma> ^^ i) x = y) \<rparr>\<^esub>"
    unfolding eq_classes_def eq_class_of_def by auto
  thus ?thesis
    using equivalence.partition_from_equivalence[OF equivalence_from_cycles[OF assms(1)]] by simp
qed



subsection \<open>Signature is a Homomorphism\<close>

lemma not_an_inversion:
  assumes "\<sigma> \<in> carrier \<S>\<^bsub>n\<^esub>"
    and "(x, y) \<in> {1..n} \<times> {1..n}" "x > y"
    and "(x, y) \<notin> inversions n \<sigma>" 
  shows "\<sigma> x > \<sigma> y"
proof (rule ccontr)
  assume "\<not> \<sigma> y < \<sigma> x"
  hence "\<sigma> y \<ge> \<sigma> x" by auto
  moreover have "\<sigma> y \<noteq> \<sigma> x"
    using inj_prop[OF assms(1)] assms(2-3) by blast
  ultimately have "\<sigma> y > \<sigma> x" by auto
  hence "(x, y) \<in> inversions n \<sigma>" using assms(2-3) inversions_def by blast
  thus False using assms(4) by simp
qed

lemma invs_of_comps:
  assumes "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "inversions n (\<sigma>2 \<circ> \<sigma>1) =
          {(x, y) \<in> {1..n} \<times> {1..n}. (x, y) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 y, \<sigma>1 x) \<notin> inversions n \<sigma>2} \<union>
          {(x, y) \<in> {1..n} \<times> {1..n}. (y, x) \<notin> inversions n \<sigma>1 \<and> (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2}"
        (is "inversions n (\<sigma>2 \<circ> \<sigma>1) = ?inv_\<sigma>1 \<union> ?inv_\<sigma>2")
proof
  show "inversions n (\<sigma>2 \<circ> \<sigma>1) \<subseteq> ?inv_\<sigma>1 \<union> ?inv_\<sigma>2"
  proof
    fix t assume t: "t \<in> inversions n (\<sigma>2 \<circ> \<sigma>1)"
    then obtain x y where xy: "x \<in> {1..n}" "y \<in> {1..n}" "x > y" "t = (x, y)"
      using inversions_def by auto
    hence "(\<sigma>2 \<circ> \<sigma>1) x < (\<sigma>2 \<circ> \<sigma>1) y"
      using t inversions_def[of n "\<sigma>2 \<circ> \<sigma>1"] by blast
    hence comp_inv: "\<sigma>2 (\<sigma>1 x) < \<sigma>2 (\<sigma>1 y)" by simp
    show "t \<in> ?inv_\<sigma>1 \<union> ?inv_\<sigma>2"
    proof (cases "t \<in> inversions n \<sigma>1")
      case True
      hence "\<sigma>1 x < \<sigma>1 y" using xy unfolding inversions_def by blast
      hence "(\<sigma>1 y, \<sigma>1 x) \<notin> inversions n \<sigma>2"
        using comp_inv inversions_def[of n \<sigma>2] by auto 
      thus ?thesis using True xy by blast
    next
      case False
      hence S0: "\<sigma>1 x > \<sigma>1 y"
        using xy inversions_def[of n \<sigma>1] t assms(1) not_an_inversion by auto
      moreover have "(\<sigma>1 x, \<sigma>1 y) \<in> {1..n} \<times> {1..n}"
        using xy assms(1) surj_prop by blast
      ultimately have "(\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2"
        using comp_inv inversions_def[of n \<sigma>2] by auto
      moreover have "(y, x) \<notin> inversions n \<sigma>1"
        using S0 inversions_def xy(3) by auto
      ultimately show ?thesis using xy by blast 
    qed
  qed

  show "?inv_\<sigma>1 \<union> ?inv_\<sigma>2 \<subseteq> inversions n (\<sigma>2 \<circ> \<sigma>1)"
  proof
    fix t assume "t \<in> ?inv_\<sigma>1 \<union> ?inv_\<sigma>2"
    from this have "t \<in> ?inv_\<sigma>1 \<or> t \<in> ?inv_\<sigma>2" by blast
    thus "t \<in> inversions n (\<sigma>2 \<circ> \<sigma>1)"
    proof
      assume t: "t \<in> ?inv_\<sigma>1"
      then obtain x y where xy: "x \<in> {1..n}" "y \<in> {1..n}" "x > y" "t = (x, y)"
        using inversions_def[of n \<sigma>1] by auto
      hence "\<sigma>1 x < \<sigma>1 y"
        using inversions_def[of n \<sigma>1] t by auto
      moreover have "(\<sigma>1 y, \<sigma>1 x) \<in> {1..n} \<times> {1..n}"
        using t xy assms surj_prop by blast
      moreover have "(\<sigma>1 y, \<sigma>1 x) \<notin> inversions n \<sigma>2"
        using t xy by auto
      ultimately have "\<sigma>2 (\<sigma>1 x) < \<sigma>2 (\<sigma>1 y)"
        using not_an_inversion[OF assms(2)] by blast
      thus ?thesis
        using inversions_def xy by auto
    next
      assume t: "t \<in> ?inv_\<sigma>2"
      then obtain x y where x:  "x \<in> {1..n}" "\<sigma>1 x \<in> {1..n}"
                        and y:  "y \<in> {1..n}" "\<sigma>1 y \<in> {1..n}"
                        and xy: "t = (x, y)"
        using inversions_def[of n \<sigma>2] by auto
      hence "\<sigma>1 x > \<sigma>1 y"
        using inversions_def[of n \<sigma>2] t by blast
      hence "x > y"
        using inversions_def[of n \<sigma>1] t x y xy case_prodI by fastforce
      moreover have "\<sigma>2 (\<sigma>1 x) < \<sigma>2 (\<sigma>1 y)"
        using inversions_def[of n \<sigma>2] t x y xy by blast
      ultimately show ?thesis
        using x y xy inversions_def[of n "\<sigma>2 \<circ> \<sigma>1"] by auto
    qed
  qed
qed

lemma disjoint_union:
  assumes "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows
    "{(x, y) \<in> {1..n} \<times> {1..n}. (x, y) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 y, \<sigma>1 x) \<notin> inversions n \<sigma>2} \<inter>
     {(x, y) \<in> {1..n} \<times> {1..n}. (y, x) \<notin> inversions n \<sigma>1 \<and> (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2} = {}"
     (is "?inv_\<sigma>1 \<inter> ?inv_\<sigma>2 = {}")
proof (rule ccontr)
  assume "?inv_\<sigma>1 \<inter> ?inv_\<sigma>2 \<noteq> {}"
  then obtain t where t: "t \<in> ?inv_\<sigma>1 \<inter> ?inv_\<sigma>2" by blast
  then obtain x y where x:  "x \<in> {1..n}" "\<sigma>1 x \<in> {1..n}"
                    and y:  "y \<in> {1..n}" "\<sigma>1 y \<in> {1..n}"
                    and xy: "t = (x, y)" "x > y"
    unfolding inversions_def by auto
  have "\<sigma>1 x < \<sigma>1 y"
    using inversions_def[of n \<sigma>1] t xy x y by blast
  moreover have "\<sigma>1 x > \<sigma>1 y"
    using inversions_def[of n \<sigma>2] t xy x y by blast
  ultimately show False by simp
qed

lemma swap_bij:
  fixes P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "A = {(x, y). P x y}" "B = {(x, y). P y x}"
  shows "bij_betw (\<lambda> (x, y). (y, x)) A B" (is "bij_betw ?f A B")
proof -
  have "\<And>t. t \<in> A \<Longrightarrow> ?f t \<in> B"
    by (simp add: assms prod.case_eq_if)
  hence "?f ` A \<subseteq> B" by blast
  moreover have "\<And>t. t \<in> B \<Longrightarrow> ?f t \<in> A \<and> ?f (?f t) = t"
    by (simp add: assms prod.case_eq_if)
  hence "\<And>t. t \<in> B \<Longrightarrow> \<exists>ta \<in> A. ?f ta = t" by blast
  ultimately have "?f ` A = B" by blast
  thus ?thesis using swap_inj_on unfolding bij_betw_def by simp 
qed

corollary card_inv_\<sigma>12:
  assumes "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows
    "card {(x, y) \<in> {1..n} \<times> {1..n}. (y, x) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2} =
     card {(x, y) \<in> {1..n} \<times> {1..n}. (x, y) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 y, \<sigma>1 x) \<in> inversions n \<sigma>2}"
  using swap_bij[where ?P = "\<lambda>x y. (x, y) \<in> {1..n} \<times> {1..n} \<and>
                                   (y, x) \<in> inversions n \<sigma>1 \<and>
                                   (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2"]
  by (smt Collect_cong bij_betw_same_card mem_Sigma_iff prod.case_eq_if)

lemma card_inv_\<sigma>1:
  assumes "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows
    "card {(x, y) \<in> {1..n} \<times> {1..n}. (x, y) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 y, \<sigma>1 x) \<notin> inversions n \<sigma>2} =
     card (inversions n \<sigma>1) -
     card {(x, y) \<in> {1..n} \<times> {1..n}. (x, y) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 y, \<sigma>1 x) \<in> inversions n \<sigma>2}"
    (is "card ?inv_\<sigma>1 = card (inversions n \<sigma>1) - card ?inv_\<sigma>12")
proof -
  have "?inv_\<sigma>1 = inversions n \<sigma>1 - ?inv_\<sigma>12"
    using Sigma_cong inversions_def by auto
  moreover have "?inv_\<sigma>12 \<subseteq> inversions n \<sigma>1" by blast
  moreover have "inversions n \<sigma>1 \<subseteq> {1..n} \<times> {1..n}"
    using SigmaI inversions_def by auto
  hence "finite (inversions n \<sigma>1)"
    by (simp add: finite_subset) 
  ultimately show ?thesis
    by (simp add: card_Diff_subset finite_subset) 
qed

lemma card_inv_\<sigma>2:
  assumes "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows
    "card {(x, y) \<in> {1..n} \<times> {1..n}. (y, x) \<notin> inversions n \<sigma>1 \<and> (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2} =
     card {(x, y) \<in> {1..n} \<times> {1..n}. (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2} -
     card {(x, y) \<in> {1..n} \<times> {1..n}. (y, x) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2}"
    (is "card ?inv_\<sigma>2 = card (?inv_\<sigma>2') - card ?inv_\<sigma>12")
proof -
  have "?inv_\<sigma>2 = ?inv_\<sigma>2' - ?inv_\<sigma>12"
    using Sigma_cong inversions_def by auto
  moreover have "?inv_\<sigma>2' \<subseteq> {1..n} \<times> {1..n}"
    using SigmaI inversions_def by auto
  hence "finite (?inv_\<sigma>2')"
    by (simp add: finite_subset)
  moreover have "?inv_\<sigma>12 \<subseteq> ?inv_\<sigma>2'" by blast
  ultimately show ?thesis 
    by (simp add: card_Diff_subset finite_subset) 
qed

lemma card_inv_\<sigma>2_rewrite:
  assumes "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "card (inversions n \<sigma>2) = 
         card {(x, y) \<in> {1..n} \<times> {1..n}. (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2}"
        (is "card (inversions n \<sigma>2) = card ?invs_\<sigma>2")
proof -
  let ?f = "\<lambda>(x, y). ((inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) x, (inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) y)"
  have inv_included: "inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>"
    by (simp add: assms(1) group_prop1)

  have "\<And>t1 t2. \<lbrakk> t1 \<in> inversions n \<sigma>2; t2 \<in> inversions n \<sigma>2 \<rbrakk> \<Longrightarrow> ?f t1 = ?f t2 \<Longrightarrow> t1 = t2"
  proof -
    fix t1 t2 assume "t1 \<in> inversions n \<sigma>2" "t2 \<in> inversions n \<sigma>2" and Eq: "?f t1 = ?f t2"
    then obtain x1 y1 x2 y2 where t1: "t1 = (x1, y1)" "(x1, y1) \<in> {1..n} \<times> {1..n}"
                              and t2: "t2 = (x2, y2)" "(x2, y2) \<in> {1..n} \<times> {1..n}"
      using inversions_def by auto
    have "(inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) x1 = (inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) x2"
      using Eq by (simp add: t1(1) t2(1))
    hence "x1 = x2"
      by (meson SigmaD1 assms(1) group.inv_closed group_prop1 inj_prop t1(2) t2(2))
    moreover have "(inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) y1 = (inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) y2"
      using Eq by (simp add: t1(1) t2(1))
    hence "y1 = y2"
      by (metis SigmaE assms(1) group.inv_closed group_prop1 inj_prop snd_conv t1(2) t2(2))
    ultimately show "t1 = t2" using t1 t2 by simp
  qed
  hence "inj_on ?f (inversions n \<sigma>2)" by (simp add: inj_onI)

  moreover have "\<And>t. t \<in> inversions n \<sigma>2 \<Longrightarrow> ?f t \<in> ?invs_\<sigma>2"
  proof -
    fix t assume t: "t \<in> inversions n \<sigma>2"
    then obtain x y where xy: "t = (x, y)" "(x, y) \<in> {1..n} \<times> {1..n}"
      using inversions_def by auto
    hence "(\<sigma>1 ((inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) x), \<sigma>1 ((inv\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1) y)) = (x, y)"
      using group_prop3 assms(1) by blast
    thus "?f t \<in> ?invs_\<sigma>2" using t xy surj_prop[OF inv_included] by auto
  qed
  hence "?f ` inversions n \<sigma>2 \<subseteq> ?invs_\<sigma>2" by (simp add: image_subsetI)

  moreover have "\<And>t. t \<in> ?invs_\<sigma>2 \<Longrightarrow> \<exists>t' \<in> inversions n \<sigma>2. ?f t' = t"
  proof -
    fix t assume "t \<in> ?invs_\<sigma>2"
    then obtain x y
      where xy: "t = (x, y)" "(x, y) \<in> {1..n} \<times> {1..n}" "(\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2" by blast
    hence "?f (\<sigma>1 x, \<sigma>1 y) = t"
      using SigmaD1 SigmaD2 assms(1) group.inv_inv group_prop1
            group_prop3 inv_included old.prod.case by metis
    thus "\<exists>t' \<in> inversions n \<sigma>2. ?f t' = t" using xy(3) by blast
  qed
  hence "?invs_\<sigma>2 \<subseteq> ?f ` inversions n \<sigma>2" by (smt image_iff subsetI)

  ultimately have "bij_betw ?f (inversions n \<sigma>2) ?invs_\<sigma>2" unfolding bij_betw_def by blast
  thus ?thesis using bij_betw_same_card by blast 
qed

lemma card_invs_of_comps:
  assumes "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
  shows "\<exists>k. card (inversions n (\<sigma>2 \<circ> \<sigma>1)) + 2 * k =
             card (inversions n \<sigma>1) + card (inversions n \<sigma>2)"
proof -
  define inv_\<sigma>12 where
  "inv_\<sigma>12 = {(x, y) \<in> {1..n} \<times> {1..n}. (x, y) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 y, \<sigma>1 x) \<in> inversions n \<sigma>2}"
  define inv_\<sigma>21 where
  "inv_\<sigma>21 = {(x, y) \<in> {1..n} \<times> {1..n}. (y, x) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2}"
  define inv_\<sigma>1 where
  "inv_\<sigma>1 = {(x, y) \<in> {1..n} \<times> {1..n}. (x, y) \<in> inversions n \<sigma>1 \<and> (\<sigma>1 y, \<sigma>1 x) \<notin> inversions n \<sigma>2}"
  define inv_\<sigma>2 where
  "inv_\<sigma>2 = {(x, y) \<in> {1..n} \<times> {1..n}. (y, x) \<notin> inversions n \<sigma>1 \<and> (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2}"
  have Finite1: "inversions n \<sigma>1 \<subseteq> {1..n} \<times> {1..n}"
    using inversions_def by auto
  have Finite2: "{(x, y) \<in> {1..n} \<times> {1..n}. (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2} \<subseteq> {1..n} \<times> {1..n}"
    using inversions_def by auto
  have "inversions n (\<sigma>2 \<circ> \<sigma>1) \<subseteq> {1..n} \<times> {1..n}"
    using inversions_def by auto
  hence "finite (inversions n (\<sigma>2 \<circ> \<sigma>1))" by (simp add: finite_subset)
  hence "card (inversions n (\<sigma>2 \<circ> \<sigma>1)) = card inv_\<sigma>1 + card inv_\<sigma>2"
    using invs_of_comps[OF assms] disjoint_union[OF assms]
          inv_\<sigma>1_def inv_\<sigma>2_def by (simp add: card_Un_disjoint)
  also have " ... = (card (inversions n \<sigma>1) - card inv_\<sigma>12) + card inv_\<sigma>2"
    using card_inv_\<sigma>1[OF assms] assms card_inv_\<sigma>12 inv_\<sigma>12_def inv_\<sigma>1_def by auto
  also have " ... = (card (inversions n \<sigma>1) - card inv_\<sigma>12) +
                    (card (inversions n \<sigma>2) - card inv_\<sigma>21)"
    using card_inv_\<sigma>2[OF assms] card_inv_\<sigma>2_rewrite[OF assms] assms
          card_inv_\<sigma>12 inv_\<sigma>12_def inv_\<sigma>1_def inv_\<sigma>21_def inv_\<sigma>2_def by simp
  also have "... = (card (inversions n \<sigma>1) - card inv_\<sigma>12) +
                   (card (inversions n \<sigma>2) - card inv_\<sigma>12)"
    using card_inv_\<sigma>12[OF assms] inv_\<sigma>21_def inv_\<sigma>12_def by simp
  finally have "card (inversions n (\<sigma>2 \<circ> \<sigma>1)) = (card (inversions n \<sigma>1) - card inv_\<sigma>12) +
                                                (card (inversions n \<sigma>2) - card inv_\<sigma>12)" .
  moreover have "inv_\<sigma>12 \<subseteq> inversions n \<sigma>1"
    using inv_\<sigma>12_def by blast  
  hence "card inv_\<sigma>12 \<le> card (inversions n \<sigma>1)"
    by (metis Finite1 card_mono finite_SigmaI finite_atLeastAtMost finite_subset)

  moreover have "inv_\<sigma>21 \<subseteq> {(x, y) \<in> {1..n} \<times> {1..n}. (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2}"
    using inv_\<sigma>21_def by blast
  hence "card inv_\<sigma>21 \<le> card {(x, y) \<in> {1..n} \<times> {1..n}. (\<sigma>1 x, \<sigma>1 y) \<in> inversions n \<sigma>2}"
    by (metis (no_types, lifting) Finite2 card_mono finite_SigmaI finite_atLeastAtMost finite_subset)
  hence "card inv_\<sigma>12 \<le> card (inversions n \<sigma>2)"
    using assms card_inv_\<sigma>12 card_inv_\<sigma>2_rewrite inv_\<sigma>12_def inv_\<sigma>21_def by auto

  ultimately have "card (inversions n (\<sigma>2 \<circ> \<sigma>1)) + 2 * card inv_\<sigma>12 =
                    card (inversions n \<sigma>1) + card (inversions n \<sigma>2)" by simp
  thus ?thesis by blast
qed 

theorem signature_is_hom:
  "group_hom \<S>\<^bsub>n\<^esub> \<lparr> carrier = {-1, 1}, mult = (op * ), one = 1 \<rparr> \<epsilon>\<^bsub>n\<^esub>"
proof -
  have "\<And>\<sigma>1 \<sigma>2. \<lbrakk> \<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>; \<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub> \<rbrakk> \<Longrightarrow>
                  (\<epsilon>\<^bsub>n\<^esub> (\<sigma>2 \<circ> \<sigma>1)) = (\<epsilon>\<^bsub>n\<^esub> \<sigma>1) * (\<epsilon>\<^bsub>n\<^esub> \<sigma>2)"
  proof -
    fix "\<sigma>1" "\<sigma>2" assume "\<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>" "\<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub>"
    then obtain k where k: "card (inversions n (\<sigma>2 \<circ> \<sigma>1)) + 2 * k =
                       card (inversions n \<sigma>1) + card (inversions n \<sigma>2)"
      using card_invs_of_comps by blast
    have "(\<epsilon>\<^bsub>n\<^esub> (\<sigma>2 \<circ> \<sigma>1)) = (-1) ^ (card (inversions n (\<sigma>2 \<circ> \<sigma>1)))"
      using signature_def by simp
    also have " ... = (-1) ^ (card (inversions n (\<sigma>2 \<circ> \<sigma>1)) + 2 * k)"
      by (simp add: power_add)
    also have " ... = (-1) ^ (card (inversions n \<sigma>1) + card (inversions n \<sigma>2))"
      using k by simp
    also have " ... = (-1) ^ (card (inversions n \<sigma>1)) * (-1) ^ (card (inversions n \<sigma>2))"
      by (simp add: power_add)
    also have " ... = (\<epsilon>\<^bsub>n\<^esub> \<sigma>1) * (\<epsilon>\<^bsub>n\<^esub> \<sigma>2)"
      using signature_def by simp
    finally show "(\<epsilon>\<^bsub>n\<^esub> (\<sigma>2 \<circ> \<sigma>1)) = (\<epsilon>\<^bsub>n\<^esub> \<sigma>1) * (\<epsilon>\<^bsub>n\<^esub> \<sigma>2)" .
  qed
  moreover have "\<And>\<sigma>. (inversions n) \<sigma> = (inversions n) (restrict \<sigma> {1..n})"
    unfolding inversions_def by auto
  hence "\<And>\<sigma>. (\<epsilon>\<^bsub>n\<^esub> \<sigma>) = (\<epsilon>\<^bsub>n\<^esub> (restrict \<sigma> {1..n}))"
    using signature_def by simp
  ultimately have "\<And>\<sigma>1 \<sigma>2. \<lbrakk> \<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>; \<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub> \<rbrakk> \<Longrightarrow>
                            (\<epsilon>\<^bsub>n\<^esub> (restrict (\<sigma>2 \<circ> \<sigma>1) {1..n})) = (\<epsilon>\<^bsub>n\<^esub> \<sigma>1) * (\<epsilon>\<^bsub>n\<^esub> \<sigma>2)" by auto
  hence "\<And>\<sigma>1 \<sigma>2. \<lbrakk> \<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>; \<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub> \<rbrakk> \<Longrightarrow>
                  (\<epsilon>\<^bsub>n\<^esub> (\<sigma>2 \<otimes>\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1)) = (\<epsilon>\<^bsub>n\<^esub> \<sigma>1) * (\<epsilon>\<^bsub>n\<^esub> \<sigma>2)"
    unfolding sym_group_def BijGroup_def compose_def apply simp
    by (metis (mono_tags, lifting) comp_apply restrict_ext)
  hence "\<And>\<sigma>1 \<sigma>2. \<lbrakk> \<sigma>1 \<in> carrier \<S>\<^bsub>n\<^esub>; \<sigma>2 \<in> carrier \<S>\<^bsub>n\<^esub> \<rbrakk> \<Longrightarrow>
        (\<epsilon>\<^bsub>n\<^esub> (\<sigma>2 \<otimes>\<^bsub>\<S>\<^bsub>n\<^esub>\<^esub> \<sigma>1)) = (\<epsilon>\<^bsub>n\<^esub> \<sigma>1) \<otimes>\<^bsub>\<lparr>carrier = {- 1, 1}, mult = op *, one = 1\<rparr>\<^esub> (\<epsilon>\<^bsub>n\<^esub> \<sigma>2)"
    by simp

  moreover have "\<And>\<sigma>. (\<epsilon>\<^bsub>n\<^esub> \<sigma>) \<in> {-1, 1}"
    using signature_def square_eq_1_iff by fastforce
  hence "(signature n): (carrier \<S>\<^bsub>n\<^esub>) \<rightarrow> carrier \<lparr> carrier = {-1, 1}, mult = (op * ), one = 1 \<rparr>"
    by simp

  moreover have "group \<S>\<^bsub>n\<^esub>"
    using group_prop1 by simp

  moreover have "group \<lparr>carrier = {- 1, 1}, mult = op *, one = 1\<rparr>"
    using group_prop2 by simp

  ultimately show ?thesis
    unfolding group_hom_def group_hom_axioms_def hom_def by simp
qed



subsection \<open>Cycle Decomposition\<close>

inductive is_cycle :: "(nat \<times> nat) list \<Rightarrow> bool"
where
  transp: "is_cycle [(i, j)]"
| dcycle: "is_cycle (Cons (i, j) cs) \<Longrightarrow> is_cycle (Cons (j, k) (Cons (i, j) cs))"

end