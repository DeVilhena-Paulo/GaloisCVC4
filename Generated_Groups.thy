theory Generated_Groups
  imports Group

begin

inductive_set
  generate :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for G and H where
    one:  "\<one>\<^bsub>G\<^esub> \<in> generate G H"
  | incl: "h \<in> H \<Longrightarrow> h \<in> generate G H"
  | inv:  "h \<in> H \<Longrightarrow> inv\<^bsub>G\<^esub> h \<in> generate G H"
  | eng:  "h1 \<in> generate G H \<Longrightarrow> h2 \<in> generate G H \<Longrightarrow> h1 \<otimes>\<^bsub>G\<^esub> h2 \<in> generate G H"

lemma (in group) generate_in_carrier:
  assumes "H \<subseteq> carrier G"
  shows "h \<in> generate G H \<Longrightarrow> h \<in> carrier G"
  apply (induction rule: generate.induct) using assms by blast+

lemma (in group) generate_m_inv_closed:
  assumes "H \<subseteq> carrier G"
  shows "h \<in> generate G H \<Longrightarrow> (inv h) \<in> generate G H"
proof (induction rule: generate.induct)
  case one thus ?case by (simp add: generate.one)
next
  case (incl h) thus ?case using generate.inv[OF incl(1), of G] by simp
next
  case (inv h) thus ?case using assms generate.incl by fastforce
next
  case (eng h1 h2)
  hence "inv (h1 \<otimes> h2) = (inv h2) \<otimes> (inv h1)"
    by (meson assms generate_in_carrier group.inv_mult_group is_group subgroup_imp_subset)
  thus ?case using generate.eng[OF eng(4) eng(3)] by simp
qed

lemma (in group) generate_is_subgroup:
  assumes "H \<subseteq> carrier G"
  shows "subgroup (generate G H) G"
proof (intro subgroupI)
  show "generate G H \<subseteq> carrier G" using generate_in_carrier[OF assms] by blast
  show "generate G H \<noteq> {}"        using generate.one by auto
  show "\<And>h. h \<in> generate G H \<Longrightarrow> inv h \<in> generate G H"
    using generate_m_inv_closed[OF assms] by blast
  show "\<And>h1 h2. \<lbrakk> h1 \<in> generate G H; h2 \<in> generate G H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 \<in> generate G H"
    by (simp add: generate.eng) 
qed

lemma (in group) generate_min_subgroup1:
  assumes "H \<subseteq> carrier G"
    and "subgroup E G" "H \<subseteq> E"
  shows "generate G H \<subseteq> E"
proof
  fix h show "h \<in> generate G H \<Longrightarrow> h \<in> E"
  proof (induct rule: generate.induct)
    case one  thus ?case using subgroup.one_closed[OF assms(2)] by simp 
    case incl thus ?case using assms(3) by blast
    case inv  thus ?case using subgroup.m_inv_closed[OF assms(2)] assms(3) by blast
  next
    case eng thus ?case using subgroup.m_closed[OF assms(2)] by simp 
  qed
qed

lemma (in group) generateI:
  assumes "H \<subseteq> carrier G"
    and "subgroup E G" "H \<subseteq> E"
    and "\<And>K. \<lbrakk> subgroup K G; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = generate G H"
proof
  show "E \<subseteq> generate G H"
    using assms generate_is_subgroup generate.incl by (metis subset_iff)
  show "generate G H \<subseteq> E"
    using generate_min_subgroup1[OF assms(1-3)] by simp
qed

lemma (in group) generateE:
  assumes "H \<subseteq> carrier G" and "E = generate G H"
  shows "subgroup E G" and "H \<subseteq> E" and "\<And>K. \<lbrakk> subgroup K G; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
proof -
  show "subgroup E G" using assms generate_is_subgroup by simp
  show "H \<subseteq> E" using assms(2) by (simp add: generate.incl subsetI)
  show "\<And>K. subgroup K G \<Longrightarrow> H \<subseteq> K \<Longrightarrow> E \<subseteq> K"
    using assms generate_min_subgroup1 by auto
qed

lemma (in group) generate_min_subgroup2:
  assumes "H \<subseteq> carrier G"
  shows "generate G H = \<Inter>{K. subgroup K G \<and> H \<subseteq> K}"
proof
  have "subgroup (generate G H) G \<and> H \<subseteq> generate G H"
    by (simp add: assms generateE(2) generate_is_subgroup)
  thus "\<Inter>{K. subgroup K G \<and> H \<subseteq> K} \<subseteq> generate G H" by blast
next
  have "\<And>K. subgroup K G \<and> H \<subseteq> K \<Longrightarrow> generate G H \<subseteq> K"
    by (simp add: assms generate_min_subgroup1)
  thus "generate G H \<subseteq> \<Inter>{K. subgroup K G \<and> H \<subseteq> K}" by blast
qed



end