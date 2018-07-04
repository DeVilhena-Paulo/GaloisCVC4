(*  Title:      HOL/Algebra/Coset.thy
    Authors:    Florian Kammueller, L C Paulson, Stephan Hohe

With additional contributions from Martin Baillon and Paulo Emílio de Vilhena.
*)

theory Coset
imports Group
begin

section \<open>Cosets and Quotient Groups\<close>

definition
  r_coset    :: "[_, 'a set, 'a] \<Rightarrow> 'a set"    (infixl "#>\<index>" 60)
  where "H #>\<^bsub>G\<^esub> a = (\<Union>h\<in>H. {h \<otimes>\<^bsub>G\<^esub> a})"

definition
  l_coset    :: "[_, 'a, 'a set] \<Rightarrow> 'a set"    (infixl "<#\<index>" 60)
  where "a <#\<^bsub>G\<^esub> H = (\<Union>h\<in>H. {a \<otimes>\<^bsub>G\<^esub> h})"

definition
  RCOSETS  :: "[_, 'a set] \<Rightarrow> ('a set)set"   ("rcosets\<index> _" [81] 80)
  where "rcosets\<^bsub>G\<^esub> H = (\<Union>a\<in>carrier G. {H #>\<^bsub>G\<^esub> a})"

definition
  set_mult  :: "[_, 'a set ,'a set] \<Rightarrow> 'a set" (infixl "<#>\<index>" 60)
  where "H <#>\<^bsub>G\<^esub> K = (\<Union>h\<in>H. \<Union>k\<in>K. {h \<otimes>\<^bsub>G\<^esub> k})"

definition
  SET_INV :: "[_,'a set] \<Rightarrow> 'a set"  ("set'_inv\<index> _" [81] 80)
  where "set_inv\<^bsub>G\<^esub> H = (\<Union>h\<in>H. {inv\<^bsub>G\<^esub> h})"


locale normal = subgroup + group +
  assumes coset_eq: "(\<forall>x \<in> carrier G. H #> x = x <# H)"

abbreviation
  normal_rel :: "['a set, ('a, 'b) monoid_scheme] \<Rightarrow> bool"  (infixl "\<lhd>" 60) where
  "H \<lhd> G \<equiv> normal H G"

(*Next two lemmas contributed by Martin Baillon.*)

lemma l_coset_eq_set_mult:
  fixes G (structure)
  shows "x <# H = {x} <#> H"
  unfolding l_coset_def set_mult_def by simp

lemma r_coset_eq_set_mult:
  fixes G (structure)
  shows "H #> x = H <#> {x}"
  unfolding r_coset_def set_mult_def by simp

(* Next five lemmas contributed by Paulo Emílio de Vilhena.                    *)

lemma (in subgroup) rcosets_non_empty:
  assumes "R \<in> rcosets H"
  shows "R \<noteq> {}"
proof -
  obtain g where "g \<in> carrier G" "R = H #> g"
    using assms unfolding RCOSETS_def by blast
  hence "\<one> \<otimes> g \<in> R"
    using one_closed unfolding r_coset_def by blast
  thus ?thesis by blast
qed

lemma (in group) diff_neutralizes:
  assumes "subgroup H G" "R \<in> rcosets H"
  shows "\<And>r1 r2. \<lbrakk> r1 \<in> R; r2 \<in> R \<rbrakk> \<Longrightarrow> r1 \<otimes> (inv r2) \<in> H"
proof -
  fix r1 r2 assume r1: "r1 \<in> R" and r2: "r2 \<in> R"
  obtain g where g: "g \<in> carrier G" "R = H #> g"
    using assms unfolding RCOSETS_def by blast
  then obtain h1 h2 where h1: "h1 \<in> H" "r1 = h1 \<otimes> g"
                      and h2: "h2 \<in> H" "r2 = h2 \<otimes> g"
    using r1 r2 unfolding r_coset_def by blast
  hence "r1 \<otimes> (inv r2) = (h1 \<otimes> g) \<otimes> ((inv g) \<otimes> (inv h2))"
    using inv_mult_group is_group assms(1) g(1) subgroup.mem_carrier by fastforce
  also have " ... =  (h1 \<otimes> (g \<otimes> inv g) \<otimes> inv h2)"
    using h1 h2 assms(1) g(1) inv_closed m_closed monoid.m_assoc
          monoid_axioms subgroup.mem_carrier by smt
  finally have "r1 \<otimes> inv r2 = h1 \<otimes> inv h2"
    using assms(1) g(1) h1(1) subgroup.mem_carrier by fastforce
  thus "r1 \<otimes> inv r2 \<in> H" by (metis assms(1) h1(1) h2(1) subgroup_def)
qed

lemma mono_set_mult: "\<lbrakk> H \<subseteq> H'; K \<subseteq> K' \<rbrakk> \<Longrightarrow> H <#>\<^bsub>G\<^esub> K \<subseteq> H' <#>\<^bsub>G\<^esub> K'"
  unfolding set_mult_def by (simp add: UN_mono)


subsection \<open>Stable Operations for Subgroups\<close>

lemma set_mult_consistent [simp]:
  "N <#>\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> K = N <#>\<^bsub>G\<^esub> K"
  unfolding set_mult_def by simp

lemma r_coset_consistent [simp]:
  "I #>\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> h = I #>\<^bsub>G\<^esub> h"
  unfolding r_coset_def by simp

lemma l_coset_consistent [simp]:
  "h <#\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> I = h <#\<^bsub>G\<^esub> I"
  unfolding l_coset_def by simp

subsection \<open>Basic Properties of set multiplication\<close>

lemma (in group) setmult_subset_G:
  assumes "H \<subseteq> carrier G" "K \<subseteq> carrier G"
  shows "H <#> K \<subseteq> carrier G" using assms
  by (auto simp add: set_mult_def subsetD)

lemma (in monoid) set_mult_closed:
  assumes "H \<subseteq> carrier G" "K \<subseteq> carrier G"
  shows "H <#> K \<subseteq> carrier G"
  using assms by (auto simp add: set_mult_def subsetD)

(* Next lemma contributed by Martin Baillon.*)
lemma (in group) set_mult_assoc:
  assumes "M \<subseteq> carrier G" "H \<subseteq> carrier G" "K \<subseteq> carrier G"
  shows "(M <#> H) <#> K = M <#> (H <#> K)"
proof
  show "(M <#> H) <#> K \<subseteq> M <#> (H <#> K)"
  proof
    fix x assume "x \<in> (M <#> H) <#> K"
    then obtain m h k where x: "m \<in> M" "h \<in> H" "k \<in> K" "x = (m \<otimes> h) \<otimes> k"
      unfolding set_mult_def by blast
    hence "x = m \<otimes> (h \<otimes> k)"
      using assms m_assoc by blast
    thus "x \<in> M <#> (H <#> K)"
      unfolding set_mult_def using x by blast
  qed
next
  show "M <#> (H <#> K) \<subseteq> (M <#> H) <#> K"
  proof
    fix x assume "x \<in> M <#> (H <#> K)"
    then obtain m h k where x: "m \<in> M" "h \<in> H" "k \<in> K" "x = m \<otimes> (h \<otimes> k)"
      unfolding set_mult_def by blast
    hence "x = (m \<otimes> h) \<otimes> k"
      using assms m_assoc rev_subsetD by metis
    thus "x \<in> (M <#> H) <#> K"
      unfolding set_mult_def using x by blast
  qed
qed



subsection \<open>Basic Properties of Cosets\<close>

lemma (in group) coset_mult_assoc:
  assumes "M \<subseteq> carrier G" "g \<in> carrier G" "h \<in> carrier G"
  shows "(M #> g) #> h = M #> (g \<otimes> h)"
  using assms by (force simp add: r_coset_def m_assoc)

lemma (in group) coset_assoc:
  assumes "x \<in> carrier G" "y \<in> carrier G" "H \<subseteq> carrier G"
  shows "x <# (H #> y) = (x <# H) #> y"
  using set_mult_assoc[of "{x}" H "{y}"]
  by (simp add: l_coset_eq_set_mult r_coset_eq_set_mult assms)

lemma (in group) coset_mult_one [simp]: "M \<subseteq> carrier G ==> M #> \<one> = M"
by (force simp add: r_coset_def)

lemma (in group) coset_mult_inv1:
  assumes "M #> (x \<otimes> (inv y)) = M"
    and "x \<in> carrier G" "y \<in> carrier G" "M \<subseteq> carrier G"
  shows "M #> x = M #> y" using assms
  by (metis coset_mult_assoc group.inv_solve_right is_group subgroup_def subgroup_self)

lemma (in group) coset_mult_inv2:
  assumes "M #> x = M #> y"
    and "x \<in> carrier G"  "y \<in> carrier G" "M \<subseteq> carrier G"
  shows "M #> (x \<otimes> (inv y)) = M " using assms
  by (metis group.coset_mult_assoc group.coset_mult_one inv_closed is_group r_inv)

lemma (in group) coset_join1:
  assumes "H #> x = H"
    and "x \<in> carrier G" "subgroup H G"
  shows "x \<in> H"
  using assms r_coset_def l_one subgroup.one_closed sym by fastforce

lemma (in group) solve_equation:
  assumes "subgroup H G" "x \<in> H" "y \<in> H"
  shows "\<exists>h \<in> H. y = h \<otimes> x"
proof -
  have "y = (y \<otimes> (inv x)) \<otimes> x" using assms
    by (simp add: m_assoc subgroup.mem_carrier)
  moreover have "y \<otimes> (inv x) \<in> H" using assms
    by (simp add: subgroup_def)
  ultimately show ?thesis by blast
qed

lemma (in group) repr_independence:
  assumes "y \<in> H #> x" "x \<in> carrier G" "subgroup H G"
  shows "H #> x = H #> y" using assms
by (auto simp add: r_coset_def m_assoc [symmetric]
                   subgroup.subset [THEN subsetD]
                   subgroup.m_closed solve_equation)

lemma (in group) coset_join2:
  assumes "x \<in> carrier G" "subgroup H G" "x \<in> H"
  shows "H #> x = H" using assms
  \<comment> \<open>Alternative proof is to put @{term "x=\<one>"} in \<open>repr_independence\<close>.\<close>
by (force simp add: subgroup.m_closed r_coset_def solve_equation)

lemma (in group) coset_join3:
  assumes "x \<in> carrier G" "subgroup H G" "x \<in> H"
  shows "x <# H = H"
proof
  have "\<And>h. h \<in> H \<Longrightarrow> x \<otimes> h \<in> H" using assms
    by (simp add: subgroup.m_closed)
  thus "x <# H \<subseteq> H" unfolding l_coset_def by blast
next
  have "\<And>h. h \<in> H \<Longrightarrow> x \<otimes> ((inv x) \<otimes> h) = h"
    by (smt assms inv_closed l_one m_assoc r_inv subgroup.mem_carrier)
  moreover have "\<And>h. h \<in> H \<Longrightarrow> (inv x) \<otimes> h \<in> H"
    by (simp add: assms subgroup.m_closed subgroup.m_inv_closed)
  ultimately show "H \<subseteq> x <# H" unfolding l_coset_def by blast
qed

lemma (in monoid) r_coset_subset_G:
  "\<lbrakk> H \<subseteq> carrier G; x \<in> carrier G \<rbrakk> \<Longrightarrow> H #> x \<subseteq> carrier G"
by (auto simp add: r_coset_def)

lemma (in group) rcosI:
  "\<lbrakk> h \<in> H; H \<subseteq> carrier G; x \<in> carrier G \<rbrakk> \<Longrightarrow> h \<otimes> x \<in> H #> x"
by (auto simp add: r_coset_def)

lemma (in group) rcosetsI:
     "\<lbrakk>H \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow> H #> x \<in> rcosets H"
by (auto simp add: RCOSETS_def)

lemma (in group) rcos_self:
  "\<lbrakk> x \<in> carrier G; subgroup H G \<rbrakk> \<Longrightarrow> x \<in> H #> x"
  by (metis l_one rcosI subgroup_def)

text (in group) \<open>Opposite of @{thm [source] "repr_independence"}\<close>
lemma (in group) repr_independenceD:
  assumes "subgroup H G" "y \<in> carrier G"
    and "H #> x = H #> y"
  shows "y \<in> H #> x"
  using assms by (simp add: rcos_self)

text \<open>Elements of a right coset are in the carrier\<close>
lemma (in subgroup) elemrcos_carrier:
  assumes "group G" "a \<in> carrier G"
    and "a' \<in> H #> a"
  shows "a' \<in> carrier G"
  by (meson assms group.is_monoid monoid.r_coset_subset_G subset subsetCE)

lemma (in subgroup) rcos_const:
  assumes "group G" "h \<in> H"
  shows "H #> h = H"
  using group.coset_join2[OF assms(1), of h H]
  by (simp add: assms(2) subgroup_axioms)

lemma (in subgroup) rcos_module_imp:
  assumes "group G" "x \<in> carrier G"
    and "x' \<in> H #> x"
  shows "(x' \<otimes> inv x) \<in> H"
proof -
  obtain h where h: "h \<in> H" "x' = h \<otimes> x"
    using assms(3) unfolding r_coset_def by blast
  hence "x' \<otimes> inv x = h"
    by (metis assms elemrcos_carrier group.inv_solve_right mem_carrier)
  thus ?thesis using h by blast
qed

lemma (in subgroup) rcos_module_rev:
  assumes "group G" "x \<in> carrier G" "x' \<in> carrier G"
    and "(x' \<otimes> inv x) \<in> H"
  shows "x' \<in> H #> x"
proof -
  obtain h where h: "h \<in> H" "x' \<otimes> inv x = h"
    using assms(4) unfolding r_coset_def by blast
  hence "x' = h \<otimes> x"
    by (metis assms group.inv_solve_right mem_carrier)
  thus ?thesis using h unfolding r_coset_def by blast
qed

text \<open>Module property of right cosets\<close>
lemma (in subgroup) rcos_module:
  assumes "group G" "x \<in> carrier G" "x' \<in> carrier G"
  shows "(x' \<in> H #> x) = (x' \<otimes> inv x \<in> H)"
  using rcos_module_rev rcos_module_imp assms by blast

text \<open>Right cosets are subsets of the carrier.\<close>
lemma (in subgroup) rcosets_carrier:
  assumes "group G" "X \<in> rcosets H"
  shows "X \<subseteq> carrier G"
  using assms elemrcos_carrier singletonD
  subset_eq unfolding RCOSETS_def by force


text \<open>Multiplication of general subsets\<close>

lemma (in comm_group) mult_subgroups:
  assumes "subgroup H G" and "subgroup K G"
  shows "subgroup (H <#> K) G"
proof (rule subgroup.intro)
  show "H <#> K \<subseteq> carrier G"
    by (simp add: setmult_subset_G assms subgroup.subset)
next
  have "\<one> \<otimes> \<one> \<in> H <#> K"
    unfolding set_mult_def using assms subgroup.one_closed by blast
  thus "\<one> \<in> H <#> K" by simp
next
  show "\<And>x. x \<in> H <#> K \<Longrightarrow> inv x \<in> H <#> K"
  proof -
    fix x assume "x \<in> H <#> K"
    then obtain h k where hk: "h \<in> H" "k \<in> K" "x = h \<otimes> k"
      unfolding set_mult_def by blast
    hence "inv x = (inv k) \<otimes> (inv h)"
      by (meson inv_mult_group assms subgroup.mem_carrier)
    hence "inv x = (inv h) \<otimes> (inv k)"
      by (metis hk inv_mult assms subgroup.mem_carrier)
    thus "inv x \<in> H <#> K"
      unfolding set_mult_def using hk assms
      by (metis (no_types, lifting) UN_iff singletonI subgroup_def)
  qed
next
  show "\<And>x y. x \<in> H <#> K \<Longrightarrow> y \<in> H <#> K \<Longrightarrow> x \<otimes> y \<in> H <#> K"
  proof -
    fix x y assume "x \<in> H <#> K" "y \<in> H <#> K"
    then obtain h1 k1 h2 k2 where h1k1: "h1 \<in> H" "k1 \<in> K" "x = h1 \<otimes> k1"
                              and h2k2: "h2 \<in> H" "k2 \<in> K" "y = h2 \<otimes> k2"
      unfolding set_mult_def by blast
    hence "x \<otimes> y = (h1 \<otimes> k1) \<otimes> (h2 \<otimes> k2)" by simp
    also have " ... = h1 \<otimes> (k1 \<otimes> h2) \<otimes> k2"
      by (smt h1k1 h2k2 m_assoc m_closed assms subgroup.mem_carrier)
    also have " ... = h1 \<otimes> (h2 \<otimes> k1) \<otimes> k2"
      by (metis (no_types, hide_lams) assms m_comm h1k1(2) h2k2(1) subgroup.mem_carrier)
    finally have "x \<otimes> y  = (h1 \<otimes> h2) \<otimes> (k1 \<otimes> k2)"
      by (smt assms h1k1 h2k2 m_assoc monoid.m_closed monoid_axioms subgroup.mem_carrier)
    thus "x \<otimes> y \<in> H <#> K" unfolding set_mult_def
      using subgroup.m_closed[OF assms(1) h1k1(1) h2k2(1)]
            subgroup.m_closed[OF assms(2) h1k1(2) h2k2(2)] by blast
  qed
qed

lemma (in subgroup) lcos_module_rev:
  assumes "group G" "x \<in> carrier G" "x' \<in> carrier G"
    and "(inv x \<otimes> x') \<in> H"
  shows "x' \<in> x <# H"
proof -
  obtain h where h: "h \<in> H" "inv x \<otimes> x' = h"
    using assms(4) unfolding l_coset_def by blast
  hence "x' = x \<otimes> h"
    by (metis assms group.inv_solve_left mem_carrier)
  thus ?thesis using h unfolding l_coset_def by blast
qed


subsection \<open>Normal subgroups\<close>

lemma normal_imp_subgroup: "H \<lhd> G \<Longrightarrow> subgroup H G"
  by (simp add: normal_def subgroup_def)

lemma (in group) normalI:
  "subgroup H G \<Longrightarrow> (\<forall>x \<in> carrier G. H #> x = x <# H) \<Longrightarrow> H \<lhd> G"
  by (simp add: normal_def normal_axioms_def is_group)

lemma (in normal) inv_op_closed1:
  assumes "x \<in> carrier G" and "h \<in> H"
  shows "(inv x) \<otimes> h \<otimes> x \<in> H"
proof -
  have "h \<otimes> x \<in> x <# H"
    using assms coset_eq assms(1) unfolding r_coset_def by blast
  then obtain h' where "h' \<in> H" "h \<otimes> x = x \<otimes> h'"
    unfolding l_coset_def by blast
  thus ?thesis by (metis assms inv_closed l_inv l_one m_assoc mem_carrier)
qed

lemma (in normal) inv_op_closed2:
  assumes "x \<in> carrier G" and "h \<in> H"
  shows "x \<otimes> h \<otimes> (inv x) \<in> H"
  using assms inv_op_closed1 by (metis inv_closed inv_inv)


text\<open>Alternative characterization of normal subgroups\<close>
lemma (in group) normal_inv_iff:
     "(N \<lhd> G) =
      (subgroup N G \<and> (\<forall>x \<in> carrier G. \<forall>h \<in> N. x \<otimes> h \<otimes> (inv x) \<in> N))"
      (is "_ = ?rhs")
proof
  assume N: "N \<lhd> G"
  show ?rhs
    by (blast intro: N normal.inv_op_closed2 normal_imp_subgroup)
next
  assume ?rhs
  hence sg: "subgroup N G"
    and closed: "\<And>x. x\<in>carrier G \<Longrightarrow> \<forall>h\<in>N. x \<otimes> h \<otimes> inv x \<in> N" by auto
  hence sb: "N \<subseteq> carrier G" by (simp add: subgroup.subset)
  show "N \<lhd> G"
  proof (intro normalI [OF sg], simp add: l_coset_def r_coset_def, clarify)
    fix x
    assume x: "x \<in> carrier G"
    show "(\<Union>h\<in>N. {h \<otimes> x}) = (\<Union>h\<in>N. {x \<otimes> h})"
    proof
      show "(\<Union>h\<in>N. {h \<otimes> x}) \<subseteq> (\<Union>h\<in>N. {x \<otimes> h})"
      proof clarify
        fix n
        assume n: "n \<in> N"
        show "n \<otimes> x \<in> (\<Union>h\<in>N. {x \<otimes> h})"
        proof
          from closed [of "inv x"]
          show "inv x \<otimes> n \<otimes> x \<in> N" by (simp add: x n)
          show "n \<otimes> x \<in> {x \<otimes> (inv x \<otimes> n \<otimes> x)}"
            by (simp add: x n m_assoc [symmetric] sb [THEN subsetD])
        qed
      qed
    next
      show "(\<Union>h\<in>N. {x \<otimes> h}) \<subseteq> (\<Union>h\<in>N. {h \<otimes> x})"
      proof clarify
        fix n
        assume n: "n \<in> N"
        show "x \<otimes> n \<in> (\<Union>h\<in>N. {h \<otimes> x})"
        proof
          show "x \<otimes> n \<otimes> inv x \<in> N" by (simp add: x n closed)
          show "x \<otimes> n \<in> {x \<otimes> n \<otimes> inv x \<otimes> x}"
            by (simp add: x n m_assoc sb [THEN subsetD])
        qed
      qed
    qed
  qed
qed

corollary (in group) normal_invI:
  assumes "subgroup N G" and "\<And>x h. \<lbrakk> x \<in> carrier G; h \<in> N \<rbrakk> \<Longrightarrow> x \<otimes> h \<otimes> inv x \<in> N"
  shows "N \<lhd> G"
  using assms normal_inv_iff by blast

corollary (in group) normal_invE:
  assumes "N \<lhd> G"
  shows "subgroup N G" and "\<And>x h. \<lbrakk> x \<in> carrier G; h \<in> N \<rbrakk> \<Longrightarrow> x \<otimes> h \<otimes> inv x \<in> N"
  using assms normal_inv_iff apply blast
  by (simp add: assms normal.inv_op_closed2)


lemma (in group) one_is_normal :
   "{\<one>} \<lhd> G"
proof(intro normal_invI )
  show "subgroup {\<one>} G"
    by (simp add: subgroup_def)
  show "\<And>x h. x \<in> carrier G \<Longrightarrow> h \<in> {\<one>} \<Longrightarrow> x \<otimes> h \<otimes> inv x \<in> {\<one>}" by simp
qed


subsection\<open>More Properties of Left Cosets\<close>

lemma (in group) l_repr_independence:
  assumes "y \<in> x <# H" "x \<in> carrier G" "subgroup H G"
  shows "x <# H = y <# H"
proof -
  obtain h' where h': "h' \<in> H" "y = x \<otimes> h'"
    using assms(1) unfolding l_coset_def by blast
  hence "\<And> h. h \<in> H \<Longrightarrow> x \<otimes> h = y \<otimes> ((inv h') \<otimes> h)"
    by (smt assms(2-3) inv_closed inv_solve_right m_assoc m_closed subgroup.mem_carrier)
  hence "\<And> xh. xh \<in> x <# H \<Longrightarrow> xh \<in> y <# H"
    unfolding l_coset_def by (metis (no_types, lifting) UN_iff assms(3) h'(1) subgroup_def)
  moreover have "\<And> h. h \<in> H \<Longrightarrow> y \<otimes> h = x \<otimes> (h' \<otimes> h)"
    using h' by (meson assms(2) assms(3) m_assoc subgroup.mem_carrier)
  hence "\<And> yh. yh \<in> y <# H \<Longrightarrow> yh \<in> x <# H"
    unfolding l_coset_def using subgroup.m_closed[OF assms(3) h'(1)] by blast
  ultimately show ?thesis by blast
qed

lemma (in group) lcos_m_assoc:
  "\<lbrakk> M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G \<rbrakk> \<Longrightarrow> g <# (h <# M) = (g \<otimes> h) <# M"
by (force simp add: l_coset_def m_assoc)

lemma (in group) lcos_mult_one: "M \<subseteq> carrier G \<Longrightarrow> \<one> <# M = M"
by (force simp add: l_coset_def)

lemma (in group) l_coset_subset_G:
  "\<lbrakk> H \<subseteq> carrier G; x \<in> carrier G \<rbrakk> \<Longrightarrow> x <# H \<subseteq> carrier G"
by (auto simp add: l_coset_def subsetD)

lemma (in group) l_coset_carrier:
  "\<lbrakk> y \<in> x <# H; x \<in> carrier G; subgroup H G \<rbrakk> \<Longrightarrow> y \<in> carrier G"
  by (auto simp add: l_coset_def m_assoc  subgroup.subset [THEN subsetD] subgroup.m_closed)

lemma (in group) l_coset_swap:
  assumes "y \<in> x <# H" "x \<in> carrier G" "subgroup H G"
  shows "x \<in> y <# H"
  using assms(2) l_repr_independence[OF assms] subgroup.one_closed[OF assms(3)]
  unfolding l_coset_def by fastforce

lemma (in group) subgroup_mult_id:
  assumes "subgroup H G"
  shows "H <#> H = H"
proof
  show "H <#> H \<subseteq> H"
    unfolding set_mult_def using subgroup.m_closed[OF assms] by (simp add: UN_subset_iff)
  show "H \<subseteq> H <#> H"
  proof
    fix x assume x: "x \<in> H" thus "x \<in> H <#> H" unfolding set_mult_def
      using subgroup.m_closed[OF assms subgroup.one_closed[OF assms] x] subgroup.one_closed[OF assms]
      by (smt UN_iff assms coset_join3 l_coset_def subgroup.mem_carrier)
  qed
qed


subsubsection \<open>Set of Inverses of an \<open>r_coset\<close>.\<close>

lemma (in normal) rcos_inv:
  assumes x:     "x \<in> carrier G"
  shows "set_inv (H #> x) = H #> (inv x)"
proof (simp add: r_coset_def SET_INV_def x inv_mult_group, safe)
  fix h
  assume h: "h \<in> H"
  show "inv x \<otimes> inv h \<in> (\<Union>j\<in>H. {j \<otimes> inv x})"
  proof
    show "inv x \<otimes> inv h \<otimes> x \<in> H"
      by (simp add: inv_op_closed1 h x)
    show "inv x \<otimes> inv h \<in> {inv x \<otimes> inv h \<otimes> x \<otimes> inv x}"
      by (simp add: h x m_assoc)
  qed
  show "h \<otimes> inv x \<in> (\<Union>j\<in>H. {inv x \<otimes> inv j})"
  proof
    show "x \<otimes> inv h \<otimes> inv x \<in> H"
      by (simp add: inv_op_closed2 h x)
    show "h \<otimes> inv x \<in> {inv x \<otimes> inv (x \<otimes> inv h \<otimes> inv x)}"
      by (simp add: h x m_assoc [symmetric] inv_mult_group)
  qed
qed


subsubsection \<open>Theorems for \<open><#>\<close> with \<open>#>\<close> or \<open><#\<close>.\<close>

lemma (in group) setmult_rcos_assoc:
  "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow>
    H <#> (K #> x) = (H <#> K) #> x"
  using set_mult_assoc[of H K "{x}"] by (simp add: r_coset_eq_set_mult)

lemma (in group) rcos_assoc_lcos:
  "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow>
   (H #> x) <#> K = H <#> (x <# K)"
  using set_mult_assoc[of H "{x}" K]
  by (simp add: l_coset_eq_set_mult r_coset_eq_set_mult)

lemma (in normal) rcos_mult_step1:
  "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow>
   (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
  by (simp add: setmult_rcos_assoc r_coset_subset_G
                subset l_coset_subset_G rcos_assoc_lcos)

lemma (in normal) rcos_mult_step2:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
by (insert coset_eq, simp add: normal_def)

lemma (in normal) rcos_mult_step3:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H <#> (H #> x)) #> y = H #> (x \<otimes> y)"
by (simp add: setmult_rcos_assoc coset_mult_assoc
              subgroup_mult_id normal.axioms subset normal_axioms)

lemma (in normal) rcos_sum:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = H #> (x \<otimes> y)"
by (simp add: rcos_mult_step1 rcos_mult_step2 rcos_mult_step3)

lemma (in normal) rcosets_mult_eq: "M \<in> rcosets H \<Longrightarrow> H <#> M = M"
  \<comment> \<open>generalizes \<open>subgroup_mult_id\<close>\<close>
  by (auto simp add: RCOSETS_def subset
        setmult_rcos_assoc subgroup_mult_id normal.axioms normal_axioms)


subsubsection\<open>An Equivalence Relation\<close>

definition
  r_congruent :: "[('a,'b)monoid_scheme, 'a set] \<Rightarrow> ('a*'a)set"  ("rcong\<index> _")
  where "rcong\<^bsub>G\<^esub> H = {(x,y). x \<in> carrier G \<and> y \<in> carrier G \<and> inv\<^bsub>G\<^esub> x \<otimes>\<^bsub>G\<^esub> y \<in> H}"


lemma (in subgroup) equiv_rcong:
   assumes "group G"
   shows "equiv (carrier G) (rcong H)"
proof -
  interpret group G by fact
  show ?thesis
  proof (intro equivI)
    show "refl_on (carrier G) (rcong H)"
      by (auto simp add: r_congruent_def refl_on_def)
  next
    show "sym (rcong H)"
    proof (simp add: r_congruent_def sym_def, clarify)
      fix x y
      assume [simp]: "x \<in> carrier G" "y \<in> carrier G"
         and "inv x \<otimes> y \<in> H"
      hence "inv (inv x \<otimes> y) \<in> H" by simp
      thus "inv y \<otimes> x \<in> H" by (simp add: inv_mult_group)
    qed
  next
    show "trans (rcong H)"
    proof (simp add: r_congruent_def trans_def, clarify)
      fix x y z
      assume [simp]: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
         and "inv x \<otimes> y \<in> H" and "inv y \<otimes> z \<in> H"
      hence "(inv x \<otimes> y) \<otimes> (inv y \<otimes> z) \<in> H" by simp
      hence "inv x \<otimes> (y \<otimes> inv y) \<otimes> z \<in> H"
        by (simp add: m_assoc del: r_inv Units_r_inv)
      thus "inv x \<otimes> z \<in> H" by simp
    qed
  qed
qed

text\<open>Equivalence classes of \<open>rcong\<close> correspond to left cosets.
  Was there a mistake in the definitions? I'd have expected them to
  correspond to right cosets.\<close>

(* CB: This is correct, but subtle.
   We call H #> a the right coset of a relative to H.  According to
   Jacobson, this is what the majority of group theory literature does.
   He then defines the notion of congruence relation ~ over monoids as
   equivalence relation with a ~ a' & b ~ b' \<Longrightarrow> a*b ~ a'*b'.
   Our notion of right congruence induced by K: rcong K appears only in
   the context where K is a normal subgroup.  Jacobson doesn't name it.
   But in this context left and right cosets are identical.
*)

lemma (in subgroup) l_coset_eq_rcong:
  assumes "group G"
  assumes a: "a \<in> carrier G"
  shows "a <# H = (rcong H) `` {a}"
proof -
  interpret group G by fact
  show ?thesis by (force simp add: r_congruent_def l_coset_def m_assoc [symmetric] a )
qed


subsubsection\<open>Two Distinct Right Cosets are Disjoint\<close>

lemma (in group) rcos_equation:
  assumes "subgroup H G"
  assumes p: "ha \<otimes> a = h \<otimes> b" "a \<in> carrier G" "b \<in> carrier G" "h \<in> H" "ha \<in> H" "hb \<in> H"
  shows "hb \<otimes> a \<in> (\<Union>h\<in>H. {h \<otimes> b})"
proof -
  interpret subgroup H G by fact
  from p show ?thesis apply (rule_tac UN_I [of "hb \<otimes> ((inv ha) \<otimes> h)"])
    apply blast by (simp add: inv_solve_left m_assoc)
qed

lemma (in group) rcos_disjoint:
  assumes "subgroup H G"
  assumes p: "a \<in> rcosets H" "b \<in> rcosets H" "a\<noteq>b"
  shows "a \<inter> b = {}"
proof -
  interpret subgroup H G by fact
  from p show ?thesis
    apply (simp add: RCOSETS_def r_coset_def)
    apply (blast intro: rcos_equation assms sym)
    done
qed


subsection \<open>Further lemmas for \<open>r_congruent\<close>\<close>

text \<open>The relation is a congruence\<close>

lemma (in normal) congruent_rcong:
  shows "congruent2 (rcong H) (rcong H) (\<lambda>a b. a \<otimes> b <# H)"
proof (intro congruent2I[of "carrier G" _ "carrier G" _] equiv_rcong is_group)
  fix a b c
  assume abrcong: "(a, b) \<in> rcong H"
    and ccarr: "c \<in> carrier G"

  from abrcong
      have acarr: "a \<in> carrier G"
        and bcarr: "b \<in> carrier G"
        and abH: "inv a \<otimes> b \<in> H"
      unfolding r_congruent_def
      by fast+

  note carr = acarr bcarr ccarr

  from ccarr and abH
      have "inv c \<otimes> (inv a \<otimes> b) \<otimes> c \<in> H" by (rule inv_op_closed1)
  moreover
      from carr and inv_closed
      have "inv c \<otimes> (inv a \<otimes> b) \<otimes> c = (inv c \<otimes> inv a) \<otimes> (b \<otimes> c)"
      by (force cong: m_assoc)
  moreover
      from carr and inv_closed
      have "\<dots> = (inv (a \<otimes> c)) \<otimes> (b \<otimes> c)"
      by (simp add: inv_mult_group)
  ultimately
      have "(inv (a \<otimes> c)) \<otimes> (b \<otimes> c) \<in> H" by simp
  from carr and this
     have "(b \<otimes> c) \<in> (a \<otimes> c) <# H"
     by (simp add: lcos_module_rev[OF is_group])
  from carr and this and is_subgroup
     show "(a \<otimes> c) <# H = (b \<otimes> c) <# H" by (intro l_repr_independence, simp+)
next
  fix a b c
  assume abrcong: "(a, b) \<in> rcong H"
    and ccarr: "c \<in> carrier G"

  from ccarr have "c \<in> Units G" by simp
  hence cinvc_one: "inv c \<otimes> c = \<one>" by (rule Units_l_inv)

  from abrcong
      have acarr: "a \<in> carrier G"
       and bcarr: "b \<in> carrier G"
       and abH: "inv a \<otimes> b \<in> H"
      by (unfold r_congruent_def, fast+)

  note carr = acarr bcarr ccarr

  from carr and inv_closed
     have "inv a \<otimes> b = inv a \<otimes> (\<one> \<otimes> b)" by simp
  also from carr and inv_closed
      have "\<dots> = inv a \<otimes> (inv c \<otimes> c) \<otimes> b" by simp
  also from carr and inv_closed
      have "\<dots> = (inv a \<otimes> inv c) \<otimes> (c \<otimes> b)" by (force cong: m_assoc)
  also from carr and inv_closed
      have "\<dots> = inv (c \<otimes> a) \<otimes> (c \<otimes> b)" by (simp add: inv_mult_group)
  finally
      have "inv a \<otimes> b = inv (c \<otimes> a) \<otimes> (c \<otimes> b)" .
  from abH and this
      have "inv (c \<otimes> a) \<otimes> (c \<otimes> b) \<in> H" by simp

  from carr and this
     have "(c \<otimes> b) \<in> (c \<otimes> a) <# H"
     by (simp add: lcos_module_rev[OF is_group])
  from carr and this and is_subgroup
     show "(c \<otimes> a) <# H = (c \<otimes> b) <# H" by (intro l_repr_independence, simp+)
qed


subsection \<open>Order of a Group and Lagrange's Theorem\<close>

definition
  order :: "('a, 'b) monoid_scheme \<Rightarrow> nat"
  where "order S = card (carrier S)"

lemma (in monoid) order_gt_0_iff_finite: "0 < order G \<longleftrightarrow> finite (carrier G)"
by(auto simp add: order_def card_gt_0_iff)

lemma (in group) rcosets_part_G:
  assumes "subgroup H G"
  shows "\<Union>(rcosets H) = carrier G"
proof -
  interpret subgroup H G by fact
  show ?thesis
    apply (rule equalityI)
    apply (force simp add: RCOSETS_def r_coset_def)
    apply (auto simp add: RCOSETS_def intro: rcos_self assms)
    done
qed

lemma (in group) cosets_finite:
     "\<lbrakk>c \<in> rcosets H;  H \<subseteq> carrier G;  finite (carrier G)\<rbrakk> \<Longrightarrow> finite c"
apply (auto simp add: RCOSETS_def)
apply (simp add: r_coset_subset_G [THEN finite_subset])
done

text\<open>The next two lemmas support the proof of \<open>card_cosets_equal\<close>.\<close>
lemma (in group) inj_on_f:
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> inv a) (H #> a)"
apply (rule inj_onI)
apply (subgoal_tac "x \<in> carrier G \<and> y \<in> carrier G")
 prefer 2 apply (blast intro: r_coset_subset_G [THEN subsetD])
apply (simp add: subsetD)
done

lemma (in group) inj_on_g:
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> a) H"
by (force simp add: inj_on_def subsetD)

(* ************************************************************************** *)

lemma (in group) card_cosets_equal:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G"
  shows "\<exists>f. bij_betw f H R"
proof -
  obtain g where g: "g \<in> carrier G" "R = H #> g"
    using assms(1) unfolding RCOSETS_def by blast

  let ?f = "\<lambda>h. h \<otimes> g"
  have "\<And>r. r \<in> R \<Longrightarrow> \<exists>h \<in> H. ?f h = r"
  proof -
    fix r assume "r \<in> R"
    then obtain h where "h \<in> H" "r = h \<otimes> g"
      using g unfolding r_coset_def by blast
    thus "\<exists>h \<in> H. ?f h = r" by blast
  qed
  hence "R \<subseteq> ?f ` H" by blast
  moreover have "?f ` H \<subseteq> R"
    using g unfolding r_coset_def by blast
  ultimately show ?thesis using inj_on_g unfolding bij_betw_def
    using assms(2) g(1) by auto
qed

corollary (in group) card_rcosets_equal:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G"
  shows "card H = card R"
  using card_cosets_equal assms bij_betw_same_card by blast

corollary (in group) rcosets_finite:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G" "finite H"
  shows "finite R"
  using card_cosets_equal assms bij_betw_finite is_group by blast

(* ************************************************************************** *)

lemma (in group) rcosets_subset_PowG:
     "subgroup H G  \<Longrightarrow> rcosets H \<subseteq> Pow(carrier G)"
  using rcosets_part_G by auto

proposition (in group) lagrange_finite:
     "\<lbrakk>finite(carrier G); subgroup H G\<rbrakk>
      \<Longrightarrow> card(rcosets H) * card(H) = order(G)"
apply (simp (no_asm_simp) add: order_def rcosets_part_G [symmetric])
apply (subst mult.commute)
apply (rule card_partition)
   apply (simp add: rcosets_subset_PowG [THEN finite_subset])
  apply (simp add: rcosets_part_G)
  apply (simp add: card_rcosets_equal subgroup.subset)
apply (simp add: rcos_disjoint)
done

theorem (in group) lagrange:
  assumes "subgroup H G"
  shows "card (rcosets H) * card H = order G"
proof (cases "finite (carrier G)")
  case True thus ?thesis using lagrange_finite assms by simp
next
  case False note inf_G = this
  thus ?thesis
  proof (cases "finite H")
    case False thus ?thesis using inf_G  by (simp add: order_def)
  next
    case True note finite_H = this
    have "infinite (rcosets H)"
    proof (rule ccontr)
      assume "\<not> infinite (rcosets H)"
      hence finite_rcos: "finite (rcosets H)" by simp
      hence "card (\<Union>(rcosets H)) = (\<Sum>R\<in>(rcosets H). card R)"
        using card_Union_disjoint[of "rcosets H"] finite_H rcos_disjoint[OF assms(1)]
              rcosets_finite[where ?H = H] by (simp add: assms subgroup.subset)
      hence "order G = (\<Sum>R\<in>(rcosets H). card R)"
        by (simp add: assms order_def rcosets_part_G)
      hence "order G = (\<Sum>R\<in>(rcosets H). card H)"
        using card_rcosets_equal by (simp add: assms subgroup.subset)
      hence "order G = (card H) * (card (rcosets H))" by simp
      hence "order G \<noteq> 0" using finite_rcos finite_H assms ex_in_conv
                                rcosets_part_G subgroup.one_closed by fastforce
      thus False using inf_G order_gt_0_iff_finite by blast
    qed
    thus ?thesis using inf_G by (simp add: order_def)
  qed
qed


subsection \<open>Quotient Groups: Factorization of a Group\<close>

definition
  FactGroup :: "[('a,'b) monoid_scheme, 'a set] \<Rightarrow> ('a set) monoid" (infixl "Mod" 65)
    \<comment> \<open>Actually defined for groups rather than monoids\<close>
   where "FactGroup G H = \<lparr>carrier = rcosets\<^bsub>G\<^esub> H, mult = set_mult G, one = H\<rparr>"

lemma (in normal) setmult_closed:
     "\<lbrakk>K1 \<in> rcosets H; K2 \<in> rcosets H\<rbrakk> \<Longrightarrow> K1 <#> K2 \<in> rcosets H"
by (auto simp add: rcos_sum RCOSETS_def)

lemma (in normal) setinv_closed:
     "K \<in> rcosets H \<Longrightarrow> set_inv K \<in> rcosets H"
by (auto simp add: rcos_inv RCOSETS_def)

lemma (in normal) rcosets_assoc:
     "\<lbrakk>M1 \<in> rcosets H; M2 \<in> rcosets H; M3 \<in> rcosets H\<rbrakk>
      \<Longrightarrow> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)"
  by (simp add: group.set_mult_assoc is_group rcosets_carrier)

lemma (in subgroup) subgroup_in_rcosets:
  assumes "group G"
  shows "H \<in> rcosets H"
proof -
  interpret group G by fact
  from _ subgroup_axioms have "H #> \<one> = H"
    by (rule coset_join2) auto
  then show ?thesis
    by (auto simp add: RCOSETS_def)
qed

lemma (in normal) rcosets_inv_mult_group_eq:
     "M \<in> rcosets H \<Longrightarrow> set_inv M <#> M = H"
by (auto simp add: RCOSETS_def rcos_inv rcos_sum subgroup.subset normal.axioms normal_axioms)

theorem (in normal) factorgroup_is_group:
  "group (G Mod H)"
apply (simp add: FactGroup_def)
apply (rule groupI)
    apply (simp add: setmult_closed)
   apply (simp add: normal_imp_subgroup subgroup_in_rcosets [OF is_group])
  apply (simp add: restrictI setmult_closed rcosets_assoc)
 apply (simp add: normal_imp_subgroup
                  subgroup_in_rcosets rcosets_mult_eq)
apply (auto dest: rcosets_inv_mult_group_eq simp add: setinv_closed)
done

lemma mult_FactGroup [simp]: "X \<otimes>\<^bsub>(G Mod H)\<^esub> X' = X <#>\<^bsub>G\<^esub> X'"
  by (simp add: FactGroup_def)

lemma (in normal) inv_FactGroup:
     "X \<in> carrier (G Mod H) \<Longrightarrow> inv\<^bsub>G Mod H\<^esub> X = set_inv X"
apply (rule group.inv_equality [OF factorgroup_is_group])
apply (simp_all add: FactGroup_def setinv_closed rcosets_inv_mult_group_eq)
done

text\<open>The coset map is a homomorphism from @{term G} to the quotient group
  @{term "G Mod H"}\<close>
lemma (in normal) r_coset_hom_Mod:
  "(\<lambda>a. H #> a) \<in> hom G (G Mod H)"
  by (auto simp add: FactGroup_def RCOSETS_def Pi_def hom_def rcos_sum)


subsection\<open>The First Isomorphism Theorem\<close>

text\<open>The quotient by the kernel of a homomorphism is isomorphic to the
  range of that homomorphism.\<close>

definition
  kernel :: "('a, 'm) monoid_scheme \<Rightarrow> ('b, 'n) monoid_scheme \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> 'a set"
    \<comment> \<open>the kernel of a homomorphism\<close>
  where "kernel G H h = {x. x \<in> carrier G \<and> h x = \<one>\<^bsub>H\<^esub>}"

lemma (in group_hom) subgroup_kernel: "subgroup (kernel G H h) G"
apply (rule subgroup.intro)
apply (auto simp add: kernel_def group.intro is_group)
done

text\<open>The kernel of a homomorphism is a normal subgroup\<close>
lemma (in group_hom) normal_kernel: "(kernel G H h) \<lhd> G"
apply (simp add: G.normal_inv_iff subgroup_kernel)
apply (simp add: kernel_def)
done

lemma (in group_hom) FactGroup_nonempty:
  assumes X: "X \<in> carrier (G Mod kernel G H h)"
  shows "X \<noteq> {}"
proof -
  from X
  obtain g where "g \<in> carrier G"
             and "X = kernel G H h #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  thus ?thesis
   by (auto simp add: kernel_def r_coset_def image_def intro: hom_one)
qed


lemma (in group_hom) FactGroup_the_elem_mem:
  assumes X: "X \<in> carrier (G Mod (kernel G H h))"
  shows "the_elem (h`X) \<in> carrier H"
proof -
  from X
  obtain g where g: "g \<in> carrier G"
             and "X = kernel G H h #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence "h ` X = {h g}" by (auto simp add: kernel_def r_coset_def g intro!: imageI)
  thus ?thesis by (auto simp add: g)
qed

lemma (in group_hom) FactGroup_hom:
     "(\<lambda>X. the_elem (h`X)) \<in> hom (G Mod (kernel G H h)) H"
apply (simp add: hom_def FactGroup_the_elem_mem normal.factorgroup_is_group [OF normal_kernel] group.axioms monoid.m_closed)
proof (intro ballI)
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel G H h)"
     and X': "X' \<in> carrier (G Mod kernel G H h)"
  then
  obtain g and g'
           where "g \<in> carrier G" and "g' \<in> carrier G"
             and "X = kernel G H h #> g" and "X' = kernel G H h #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h x = h g" "\<forall>x\<in>X'. h x = h g'"
    and Xsub: "X \<subseteq> carrier G" and X'sub: "X' \<subseteq> carrier G"
    by (force simp add: kernel_def r_coset_def image_def)+
  hence "h ` (X <#> X') = {h g \<otimes>\<^bsub>H\<^esub> h g'}" using X X'
    by (auto dest!: FactGroup_nonempty intro!: image_eqI
             simp add: set_mult_def
                       subsetD [OF Xsub] subsetD [OF X'sub])
  then show "the_elem (h ` (X <#> X')) = the_elem (h ` X) \<otimes>\<^bsub>H\<^esub> the_elem (h ` X')"
    by (auto simp add: all FactGroup_nonempty X X' the_elem_image_unique)
qed


text\<open>Lemma for the following injectivity result\<close>
lemma (in group_hom) FactGroup_subset:
     "\<lbrakk>g \<in> carrier G; g' \<in> carrier G; h g = h g'\<rbrakk>
      \<Longrightarrow>  kernel G H h #> g \<subseteq> kernel G H h #> g'"
apply (clarsimp simp add: kernel_def r_coset_def)
apply (rename_tac y)
apply (rule_tac x="y \<otimes> g \<otimes> inv g'" in exI)
apply (simp add: G.m_assoc)
done

lemma (in group_hom) FactGroup_inj_on:
     "inj_on (\<lambda>X. the_elem (h ` X)) (carrier (G Mod kernel G H h))"
proof (simp add: inj_on_def, clarify)
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel G H h)"
     and X': "X' \<in> carrier (G Mod kernel G H h)"
  then
  obtain g and g'
           where gX: "g \<in> carrier G"  "g' \<in> carrier G"
              "X = kernel G H h #> g" "X' = kernel G H h #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h x = h g" "\<forall>x\<in>X'. h x = h g'"
    by (force simp add: kernel_def r_coset_def image_def)+
  assume "the_elem (h ` X) = the_elem (h ` X')"
  hence h: "h g = h g'"
    by (simp add: all FactGroup_nonempty X X' the_elem_image_unique)
  show "X=X'" by (rule equalityI) (simp_all add: FactGroup_subset h gX)
qed

text\<open>If the homomorphism @{term h} is onto @{term H}, then so is the
homomorphism from the quotient group\<close>
lemma (in group_hom) FactGroup_onto:
  assumes h: "h ` carrier G = carrier H"
  shows "(\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h) = carrier H"
proof
  show "(\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h) \<subseteq> carrier H"
    by (auto simp add: FactGroup_the_elem_mem)
  show "carrier H \<subseteq> (\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h)"
  proof
    fix y
    assume y: "y \<in> carrier H"
    with h obtain g where g: "g \<in> carrier G" "h g = y"
      by (blast elim: equalityE)
    hence "(\<Union>x\<in>kernel G H h #> g. {h x}) = {y}"
      by (auto simp add: y kernel_def r_coset_def)
    with g show "y \<in> (\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h)"
      apply (auto intro!: bexI image_eqI simp add: FactGroup_def RCOSETS_def)
      apply (subst the_elem_image_unique)
      apply auto
      done
  qed
qed


text\<open>If @{term h} is a homomorphism from @{term G} onto @{term H}, then the
 quotient group @{term "G Mod (kernel G H h)"} is isomorphic to @{term H}.\<close>
theorem (in group_hom) FactGroup_iso_set:
  "h ` carrier G = carrier H
   \<Longrightarrow> (\<lambda>X. the_elem (h`X)) \<in> iso (G Mod (kernel G H h)) H"
by (simp add: iso_def FactGroup_hom FactGroup_inj_on bij_betw_def
              FactGroup_onto)

corollary (in group_hom) FactGroup_iso :
  "h ` carrier G = carrier H
   \<Longrightarrow> (G Mod (kernel G H h))\<cong> H"
  using FactGroup_iso_set unfolding is_iso_def by auto


(* Next two lemmas contributed by Paulo Emílio de Vilhena. *)

lemma (in group_hom) trivial_hom_iff:
  "(h ` (carrier G) = { \<one>\<^bsub>H\<^esub> }) = (kernel G H h = carrier G)"
  unfolding kernel_def using one_closed by force

lemma (in group_hom) trivial_ker_imp_inj:
  assumes "kernel G H h = { \<one> }"
  shows "inj_on h (carrier G)"
proof (rule inj_onI)
  fix g1 g2 assume A: "g1 \<in> carrier G" "g2 \<in> carrier G" "h g1 = h g2"
  hence "h (g1 \<otimes> (inv g2)) = \<one>\<^bsub>H\<^esub>" by simp
  hence "g1 \<otimes> (inv g2) = \<one>"
    using A assms unfolding kernel_def by blast
  thus "g1 = g2"
    using A G.inv_equality G.inv_inv by blast
qed


(* Next subsection contributed by Martin Baillon. *)

subsection \<open>Theorems about Factor Groups and Direct product\<close>

lemma (in group) DirProd_normal :
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "H \<times> N \<lhd> G \<times>\<times> K"
proof (intro group.normal_invI[OF DirProd_group[OF group_axioms assms(1)]])
  show sub : "subgroup (H \<times> N) (G \<times>\<times> K)"
    using DirProd_subgroups[OF group_axioms normal_imp_subgroup[OF assms(2)]assms(1)
         normal_imp_subgroup[OF assms(3)]].
  show "\<And>x h. x \<in> carrier (G\<times>\<times>K) \<Longrightarrow> h \<in> H\<times>N \<Longrightarrow> x \<otimes>\<^bsub>G\<times>\<times>K\<^esub> h \<otimes>\<^bsub>G\<times>\<times>K\<^esub> inv\<^bsub>G\<times>\<times>K\<^esub> x \<in> H\<times>N"
  proof-
    fix x h assume xGK : "x \<in> carrier (G \<times>\<times> K)" and hHN : " h \<in> H \<times> N"
    hence hGK : "h \<in> carrier (G \<times>\<times> K)" using subgroup.subset[OF sub] by auto
    from xGK obtain x1 x2 where x1x2 :"x1 \<in> carrier G" "x2 \<in> carrier K" "x = (x1,x2)"
      unfolding DirProd_def by fastforce
    from hHN obtain h1 h2 where h1h2 : "h1 \<in> H" "h2 \<in> N" "h = (h1,h2)"
      unfolding DirProd_def by fastforce
    hence h1h2GK : "h1 \<in> carrier G" "h2 \<in> carrier K"
      using normal_imp_subgroup subgroup.subset assms apply blast+.
    have "inv\<^bsub>G \<times>\<times> K\<^esub> x = (inv\<^bsub>G\<^esub> x1,inv\<^bsub>K\<^esub> x2)"
      using inv_DirProd[OF group_axioms assms(1) x1x2(1)x1x2(2)] x1x2 by auto
    hence "x \<otimes>\<^bsub>G \<times>\<times> K\<^esub> h \<otimes>\<^bsub>G \<times>\<times> K\<^esub> inv\<^bsub>G \<times>\<times> K\<^esub> x = (x1 \<otimes> h1 \<otimes> inv x1,x2 \<otimes>\<^bsub>K\<^esub> h2 \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x2)"
      using h1h2 x1x2 h1h2GK by auto
    moreover have "x1 \<otimes> h1 \<otimes> inv x1 \<in> H" "x2 \<otimes>\<^bsub>K\<^esub> h2 \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x2 \<in> N"
      using normal_invE group.normal_invE[OF assms(1)] assms x1x2 h1h2 apply auto.
    hence "(x1 \<otimes> h1 \<otimes> inv x1, x2 \<otimes>\<^bsub>K\<^esub> h2 \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x2)\<in> H \<times> N" by auto
    ultimately show " x \<otimes>\<^bsub>G \<times>\<times> K\<^esub> h \<otimes>\<^bsub>G \<times>\<times> K\<^esub> inv\<^bsub>G \<times>\<times> K\<^esub> x \<in> H \<times> N" by auto
  qed
qed

lemma (in group) FactGroup_DirProd_multiplication_iso_set :
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "(\<lambda> (X, Y). X \<times> Y) \<in> iso  ((G Mod H) \<times>\<times> (K Mod N)) (G \<times>\<times> K Mod H \<times> N)"

proof-
  have R :"(\<lambda>(X, Y). X \<times> Y) \<in> carrier (G Mod H) \<times> carrier (K Mod N) \<rightarrow> carrier (G \<times>\<times> K Mod H \<times> N)"
    unfolding r_coset_def Sigma_def DirProd_def FactGroup_def RCOSETS_def apply simp by blast
  moreover have "(\<forall>x\<in>carrier (G Mod H). \<forall>y\<in>carrier (K Mod N). \<forall>xa\<in>carrier (G Mod H).
                \<forall>ya\<in>carrier (K Mod N). (x <#> xa) \<times> (y <#>\<^bsub>K\<^esub> ya) =  x \<times> y <#>\<^bsub>G \<times>\<times> K\<^esub> xa \<times> ya)"
    unfolding set_mult_def by force
  moreover have "(\<forall>x\<in>carrier (G Mod H). \<forall>y\<in>carrier (K Mod N). \<forall>xa\<in>carrier (G Mod H).
                 \<forall>ya\<in>carrier (K Mod N).  x \<times> y = xa \<times> ya \<longrightarrow> x = xa \<and> y = ya)"
    unfolding  FactGroup_def using times_eq_iff subgroup.rcosets_non_empty
    by (metis assms(2) assms(3) normal_def partial_object.select_convs(1))
  moreover have "(\<lambda>(X, Y). X \<times> Y) ` (carrier (G Mod H) \<times> carrier (K Mod N)) =
                                     carrier (G \<times>\<times> K Mod H \<times> N)"
    unfolding image_def  apply auto using R apply force
    unfolding DirProd_def FactGroup_def RCOSETS_def r_coset_def by force
  ultimately show ?thesis
    unfolding iso_def hom_def bij_betw_def inj_on_def by simp
qed

corollary (in group) FactGroup_DirProd_multiplication_iso_1 :
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "  ((G Mod H) \<times>\<times> (K Mod N)) \<cong> (G \<times>\<times> K Mod H \<times> N)"
  unfolding is_iso_def using FactGroup_DirProd_multiplication_iso_set assms by auto

corollary (in group) FactGroup_DirProd_multiplication_iso_2 :
  assumes "group K"
    and "H \<lhd> G"
    and "N \<lhd> K"
  shows "(G \<times>\<times> K Mod H \<times> N) \<cong> ((G Mod H) \<times>\<times> (K Mod N))"
  using FactGroup_DirProd_multiplication_iso_1 group.iso_sym assms
        DirProd_group[OF normal.factorgroup_is_group normal.factorgroup_is_group]
  by blast

subsubsection "More Lemmas about set multiplication"

(*A group multiplied by a subgroup stays the same*)
lemma (in group) set_mult_carrier_idem:
  assumes "subgroup H G"
  shows "(carrier G) <#> H = carrier G"
proof
  show "(carrier G)<#>H \<subseteq> carrier G"
    unfolding set_mult_def using subgroup.subset assms by blast
next
  have " (carrier G) #>  \<one> = carrier G" unfolding set_mult_def r_coset_def group_axioms by simp
  moreover have "(carrier G) #>  \<one> \<subseteq> (carrier G) <#> H" unfolding set_mult_def r_coset_def
    using assms subgroup.one_closed[OF assms] by blast
  ultimately show "carrier G \<subseteq> (carrier G) <#> H" by simp
qed

(*Same lemma as above, but everything is included in a subgroup*)
lemma (in group) set_mult_subgroup_idem:
  assumes HG: "subgroup H G" and NG: "subgroup N (G \<lparr> carrier := H \<rparr>)"
  shows "H <#> N = H"
  using group.set_mult_carrier_idem[OF subgroup.subgroup_is_group[OF HG group_axioms] NG] by simp

(*A normal subgroup is commutative with set_mult*)
lemma (in group) commut_normal:
  assumes "subgroup H G" and "N\<lhd>G"
  shows "H<#>N = N<#>H"
proof-
  have aux1: "{H <#> N} = {\<Union>h\<in>H. h <# N }" unfolding set_mult_def l_coset_def by auto
  also have "... = {\<Union>h\<in>H. N #> h }" using assms normal.coset_eq subgroup.mem_carrier by fastforce
  moreover have aux2: "{N <#> H} = {\<Union>h\<in>H. N #> h }"unfolding set_mult_def r_coset_def by auto
  ultimately show "H<#>N = N<#>H" by simp
qed

(*Same lemma as above, but everything is included in a subgroup*)
lemma (in group) commut_normal_subgroup:
  assumes "subgroup H G" and "N \<lhd> (G\<lparr> carrier := H \<rparr>)"
    and "subgroup K (G \<lparr> carrier := H \<rparr>)"
  shows "K <#> N = N <#> K"
  using group.commut_normal[OF subgroup.subgroup_is_group[OF assms(1) group_axioms] assms(3,2)] by simp



subsubsection "Lemmas about intersection and normal subgroups"

lemma (in group) normal_inter:
  assumes "subgroup H G"
    and "subgroup K G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
  shows " (H1\<inter>K)\<lhd>(G\<lparr>carrier:= (H\<inter>K)\<rparr>)"
proof-
  define HK and H1K and GH and GHK
    where "HK = H\<inter>K" and "H1K=H1\<inter>K" and "GH =G\<lparr>carrier := H\<rparr>" and "GHK = (G\<lparr>carrier:= (H\<inter>K)\<rparr>)"
  show "H1K\<lhd>GHK"
  proof (intro group.normal_invI[of GHK H1K])
    show "Group.group GHK"
      using GHK_def subgroups_Inter_pair subgroup_imp_group assms by blast

  next
    have  H1K_incl:"subgroup H1K (G\<lparr>carrier:= (H\<inter>K)\<rparr>)"
    proof(intro subgroup_incl)
      show "subgroup H1K G"
        using assms normal_imp_subgroup subgroups_Inter_pair incl_subgroup H1K_def by blast
    next
      show "subgroup (H\<inter>K) G" using HK_def subgroups_Inter_pair assms by auto
    next
      have "H1 \<subseteq> (carrier (G\<lparr>carrier:=H\<rparr>))"
        using  assms(3) normal_imp_subgroup subgroup.subset by blast
      also have "... \<subseteq> H" by simp
      thus "H1K \<subseteq>H\<inter>K"
        using H1K_def calculation by auto
    qed
    thus "subgroup H1K GHK" using GHK_def by simp
  next
    show "\<And> x h. x\<in>carrier GHK \<Longrightarrow> h\<in>H1K \<Longrightarrow> x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x\<in> H1K"
    proof-
      have invHK: "\<lbrakk>y\<in>HK\<rbrakk> \<Longrightarrow> inv\<^bsub>GHK\<^esub> y = inv\<^bsub>GH\<^esub> y"
        using m_inv_consistent assms HK_def GH_def GHK_def subgroups_Inter_pair by simp
      have multHK : "\<lbrakk>x\<in>HK;y\<in>HK\<rbrakk> \<Longrightarrow>  x \<otimes>\<^bsub>(G\<lparr>carrier:=HK\<rparr>)\<^esub> y =  x \<otimes> y"
        using HK_def by simp
      fix x assume p: "x\<in>carrier GHK"
      fix h assume p2 : "h:H1K"
      have "carrier(GHK)\<subseteq>HK"
        using GHK_def HK_def by simp
      hence xHK:"x\<in>HK" using p by auto
      hence invx:"inv\<^bsub>GHK\<^esub> x = inv\<^bsub>GH\<^esub> x"
        using invHK assms GHK_def HK_def GH_def m_inv_consistent subgroups_Inter_pair by simp
      have "H1\<subseteq>carrier(GH)"
        using assms GH_def normal_imp_subgroup subgroup.subset by blast
      hence hHK:"h\<in>HK"
        using p2 H1K_def HK_def GH_def by auto
      hence xhx_egal : "x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub>x =  x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x"
        using invx invHK multHK GHK_def GH_def by auto
      have xH:"x\<in>carrier(GH)"
        using xHK HK_def GH_def by auto
      have hH:"h\<in>carrier(GH)"
        using hHK HK_def GH_def by auto
      have  "(\<forall>x\<in>carrier (GH). \<forall>h\<in>H1.  x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> H1)"
        using assms normal_invE GH_def normal.inv_op_closed2 by fastforce
      hence INCL_1 : "x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> H1"
        using  xH H1K_def p2 by blast
      have " x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> HK"
        using assms HK_def subgroups_Inter_pair hHK xHK
        by (metis GH_def inf.cobounded1 subgroup_def subgroup_incl)
      hence " x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> K" using HK_def by simp
      hence " x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> H1K" using INCL_1 H1K_def by auto
      thus  "x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x \<in> H1K" using xhx_egal by simp
    qed
  qed
qed


lemma (in group) normal_inter_subgroup:
  assumes "subgroup H G"
    and "N \<lhd> G"
  shows "(N\<inter>H) \<lhd> (G\<lparr>carrier := H\<rparr>)"
proof -
  define K where "K = carrier G"
  have "G\<lparr>carrier := K\<rparr> =  G" using K_def by auto
  moreover have "subgroup K G" using K_def subgroup_self by blast
  moreover have "normal N (G \<lparr>carrier :=K\<rparr>)" using assms K_def by simp
  ultimately have "N \<inter> H \<lhd> G\<lparr>carrier := K \<inter> H\<rparr>"
    using normal_inter[of K H N] assms(1) by blast
  moreover have "K \<inter> H = H" using K_def assms subgroup.subset by blast
  ultimately show "normal (N\<inter>H) (G\<lparr>carrier := H\<rparr>)" by auto
qed


end
