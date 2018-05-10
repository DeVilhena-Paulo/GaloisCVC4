theory Solvable_Groups
  imports Group Coset Generated_Groups
    
begin

inductive solvable_seq :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> bool" for G where
unity:       "solvable_seq G { \<one>\<^bsub>G\<^esub> }" |
extension: "\<lbrakk> solvable_seq G K; K \<subset> H; subgroup H G; K \<lhd> (G \<lparr> carrier := H \<rparr>);
              comm_group ((G \<lparr> carrier := H \<rparr>) Mod K) \<rbrakk> \<Longrightarrow> solvable_seq G H"

definition
  solvable :: "('a, 'b) monoid_scheme \<Rightarrow> bool"
  where "solvable G \<longleftrightarrow> solvable_seq G (carrier G)"


subsection \<open>Solvable Groups and Derived Subgroups\<close>

text \<open>We show that a group G is solvable iff the subgroup (derived G ^^ n) (carrier G)
      is trivial for a sufficiently large n\<close>

lemma (in group) solvable_imp_subgroup:
  assumes "solvable_seq G H"
  shows "subgroup H G" using assms
proof (induction)
  case unity thus ?case
    using generate_empty generate_is_subgroup by force 
next
  case extension thus ?case by simp
qed

lemma (in group) augment_solvable_seq:
  assumes "subgroup H G"
    and "solvable_seq G (derived G H)"
  shows "solvable_seq G H"
proof (cases)
  assume "derived G H = H" thus ?thesis
    unfolding solvable_def using assms by simp
next
  assume "derived G H \<noteq> H"
  thus ?thesis unfolding solvable_def
    using solvable_seq.extension[OF assms(2), of H] assms(1)
          derived_quot_of_subgroup_is_comm_group[of H, OF assms(1)]
          derived_incl[OF assms(1)] derived_subgroup_is_normal[OF assms(1)] by simp
qed

theorem (in group) trivial_derived_seq_imp_solvable:
  assumes "subgroup H G" and "((derived G) ^^ n) H = { \<one> }"
  shows "solvable_seq G H" using assms
proof (induction n arbitrary: H)
  case 0 hence "H = { \<one> }" by simp thus ?case by (simp add: unity)
next
  case (Suc n)
  hence "(derived G ^^ n) (derived G H) = { \<one> }"
    by (simp add: funpow_swap1)
  moreover have "subgroup (derived G H) G" unfolding derived_def
    using Suc.prems(1) derived_set_incl generate_is_subgroup order.trans subgroup_imp_subset
    by (metis (no_types, lifting))
  ultimately have "solvable_seq G (derived G H)" by (simp add: Suc.IH)
  thus ?case by (simp add: Suc.prems(1) augment_solvable_seq)
qed

theorem (in group) solvable_imp_trivial_derived_seq:
  assumes "solvable_seq G H" and "subgroup H G"
  shows "\<exists>n. (derived G ^^ n) H = { \<one> }"
proof -
  { fix K H assume A: "K \<subseteq> H" "K \<lhd> (G \<lparr> carrier := H \<rparr>)" "subgroup K G" "subgroup H G"
                      "comm_group ((G \<lparr> carrier := H \<rparr>) Mod K)"
    have "derived G H \<subseteq> K"
    proof -
      have "derived_set G H \<subseteq> K"
      proof
        fix h assume "h \<in> derived_set G H"
        then obtain h1 h2 where h12: "h1 \<in> H" "h2 \<in> H" "h = h1 \<otimes> h2 \<otimes> inv h1 \<otimes> inv h2" by blast

        hence K_h12: "(K #> (h1 \<otimes> h2)) \<in> carrier ((G \<lparr> carrier := H \<rparr>) Mod K)"
          unfolding FactGroup_def RCOSETS_def r_coset_def apply simp by (metis A(4) subgroup_def)
        have K_h1: "K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h1 \<in> carrier ((G \<lparr> carrier := H \<rparr>) Mod K)"
          unfolding FactGroup_def RCOSETS_def r_coset_def apply simp using h12(1) by blast
        have K_h2: "K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h2 \<in> carrier ((G \<lparr> carrier := H \<rparr>) Mod K)"
          unfolding FactGroup_def RCOSETS_def r_coset_def apply simp using h12(2) by blast

        hence "K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> (h1 \<otimes> h2) =
              (K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h1) <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> (K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h2)"
          using normal.rcos_sum[OF A(2),of h1 h2] h12(1-2) by simp
        also have " ... =
              (K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h2) <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> (K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h1)"
          using comm_groupE(4)[OF A(5) K_h1 K_h2] by simp
        finally have "K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> (h1 \<otimes> h2) = K #>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> (h2 \<otimes> h1)"
          using normal.rcos_sum[OF A(2),of h2 h1] h12(1-2) by simp

        moreover have "h1 \<otimes> h2 \<in> H" using h12 A(4) subgroupE(4) by blast
        moreover have "h2 \<otimes> h1 \<in> H" using h12 A(4) subgroupE(4) by blast
        ultimately have "K #> (h1 \<otimes> h2) = K #> (h2 \<otimes> h1)"
          using subgroup_rcos_equality[OF A(4) A(1)] by auto

        then obtain k where k: "k \<in> K" "\<one> \<otimes> (h1 \<otimes> h2) = k \<otimes> (h2 \<otimes> h1)"
          using subgroup.one_closed[OF A(3)] unfolding r_coset_def by blast
        hence "(h1 \<otimes> h2) \<otimes> (inv h1 \<otimes> inv h2) = k"
          by (smt A(1) A(4) h12(1-2) inv_mult_group inv_solve_right
              l_one m_closed subgroup.mem_carrier subsetCE)
        hence "h = k" using h12
          by (meson A(4) \<open>h1 \<otimes> h2 \<in> H\<close> inv_closed m_assoc subgroup.mem_carrier)
        thus "h \<in> K" using k(1) by simp
      qed
      thus ?thesis unfolding derived_def by (meson A(3) generateE(3) order.trans subgroupE(1))
    qed } note aux_lemma = this

  show "\<exists>n. (derived G ^^ n) H = { \<one> }" using assms
  proof (induct H rule: solvable_seq.induct)
    case unity have "(derived G ^^ 0) { \<one> } = { \<one> }" by simp thus ?case by blast 
  next
    case (extension K H)
    then obtain n where n: "(derived G ^^ n) K = { \<one> }"
      using solvable_imp_subgroup extension by blast
    have "derived G H \<subseteq> K" using solvable_imp_subgroup extension aux_lemma by blast
    hence "(derived G ^^ n) (derived G H) \<subseteq> (derived G ^^ n) K"
      using mono_derived solvable_imp_subgroup extension.hyps(4)
      by (simp add: extension.hyps(1) subgroup_imp_subset) 
    hence "(derived G ^^ (Suc n)) H \<subseteq> { \<one> }"
      by (metis funpow_simps_right(2) n o_apply)
    moreover have "\<one> \<in> derived G ((derived G ^^ n) H)"
      unfolding derived_def using generate.one by auto
    hence "{ \<one> } \<subseteq> (derived G ^^ (Suc n)) H" by simp
    ultimately show ?case by blast
  qed
qed

theorem (in group) solvable_iff_trivial_derived_seq:
  "solvable G \<longleftrightarrow> (\<exists>n. (derived G ^^ n) (carrier G) = { \<one> })"
  unfolding solvable_def
  using solvable_imp_trivial_derived_seq subgroup_self
        trivial_derived_seq_imp_solvable by blast 


subsection \<open>Short Exact Sequences\<close>

text \<open>Even if we don't talk about short exact sequences explicitly,
      we are going to show that given an injective homomorphism from a group H to a group G,
      in order to prove that a group G isn't solvable, it suffices to prove that H isn't neither\<close>

lemma (in group_hom) generate_of_img:
  assumes "K \<subseteq> carrier G"
  shows "generate H (h ` K) = h ` (generate G K)"
proof
  have img_in_carrier: "h ` K \<subseteq> carrier H"
    by (meson assms group_hom.hom_closed group_hom_axioms image_subsetI subsetCE)

  show "generate H (h ` K) \<subseteq> h ` generate G K"
  proof
    fix x assume "x \<in> generate H (h ` K)"
    then obtain r where r: "elts r \<subseteq> (h ` K)" "norm H r = x"
      using H.generate_repr_iff img_in_carrier by auto
    from \<open>elts r \<subseteq> (h ` K)\<close> have "norm H r \<in> h ` generate G K"
    proof (induct r rule: repr.induct)
      case One
      have "\<one>\<^bsub>G\<^esub> \<in> generate G K" using generate.one[of G] by simp
      hence "h \<one>\<^bsub>G\<^esub> \<in> h ` generate G K" by blast
      thus ?case by simp
    next
      case (Inv x) hence "x \<in> h ` K" by simp
      then obtain k where k: "k \<in> K" "x = h k" by blast
      hence "inv\<^bsub>H\<^esub> x = h (inv k)" using assms by auto
      thus ?case using k by (simp add: generate.inv)
    next
      case (Leaf x) hence "x \<in> h ` K" by simp
      then obtain k where "k \<in> K" "x = h k" by blast
      thus ?case by (simp add: generate.incl)
    next
      case (Mult x1 x2) hence A: "elts x1 \<union> elts x2 \<subseteq> h ` K" by simp
      have "norm H x1 \<in> h ` (generate G K)" using A Mult by simp
      moreover have "norm H x2 \<in> h ` (generate G K)" using A Mult by simp
      ultimately obtain k1 k2 where k1: "k1 \<in> generate G K" "norm H x1 = h k1"
                                and k2: "k2 \<in> generate G K" "norm H x2 = h k2" by blast
      hence "norm H (Mult x1 x2) = h (k1 \<otimes> k2)"
        using G.generate_in_carrier assms by auto
      thus ?case using k1 k2 by (simp add: generate.eng) 
    qed
    thus "x \<in> h ` generate G K" using r by simp
  qed

next
  show "h ` generate G K \<subseteq> generate H (h ` K)"
  proof
    fix x assume "x \<in> h ` generate G K"
    then obtain r where r: "elts r \<subseteq> K" "x = h (norm G r)" using G.generate_repr_iff assms by auto
    from \<open>elts r \<subseteq> K\<close> have "h (norm G r) \<in> generate H (h ` K)"
    proof (induct r rule: repr.induct)
      case One thus ?case by (simp add: generate.one) 
    next
      case (Inv x) hence A: "x \<in> K" by simp
      hence "h (norm G (Inv x)) = inv\<^bsub>H\<^esub> (h x)" using assms by auto
      moreover have "h x \<in> generate H (h ` K)" using A by (simp add: generate.incl)
      ultimately show ?case by (simp add: A generate.inv)
    next
      case (Leaf x) thus ?case by (simp add: generate.incl)
    next
      case (Mult x1 x2) hence A: "elts x1 \<union> elts x2 \<subseteq> K" by simp
      have "norm G x1 \<in> carrier G"
        by (meson A G.generateE(1) G.generate_repr_iff Un_subset_iff assms subgroup.mem_carrier)
      moreover have "norm G x2 \<in> carrier G"
        by (meson A G.generateE(1) G.generate_repr_iff Un_subset_iff assms subgroup.mem_carrier)
      ultimately have "h (norm G (Mult x1 x2)) = h (norm G x1) \<otimes>\<^bsub>H\<^esub> h (norm G x2)" by simp
      thus ?case using Mult A by (simp add: generate.eng) 
    qed
    thus "x \<in> generate H (h ` K)" using r by simp
  qed
qed

lemma (in group_hom) derived_of_img:
  assumes "K \<subseteq> carrier G"
  shows "(derived H ^^ n) (h ` K) = h ` ((derived G ^^ n) K)"
proof -
  { fix K assume A: "K \<subseteq> carrier G"
    have "derived H (h ` K) = h ` (derived G K)"
    proof -
      have "derived_set H (h ` K) = h ` (derived_set G K)"
      proof
        show "derived_set H (h ` K) \<subseteq> h ` derived_set G K"
        proof
          fix x assume "x \<in> derived_set H (h ` K)"
          then obtain k1 k2
            where k12: "k1 \<in> K" "k2 \<in> K"
              and "x = (h k1) \<otimes>\<^bsub>H\<^esub> (h k2) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h k1) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub>(h k2)" by blast
          hence "x = h (k1 \<otimes> k2 \<otimes> inv k1 \<otimes> inv k2)"
            by (smt G.inv_closed G.m_closed A hom_inv hom_mult subsetCE)
          thus "x \<in> h ` (derived_set G K)" using k12 by blast
        qed
      next
        show "h ` derived_set G K \<subseteq> derived_set H (h ` K)"
        proof
          fix x assume " x \<in> h ` derived_set G K"
          then obtain k1 k2 where k12: "k1 \<in> K" "k2 \<in> K"
                              and "x = h (k1 \<otimes> k2 \<otimes> inv k1 \<otimes> inv k2)" by blast
          hence "x = (h k1) \<otimes>\<^bsub>H\<^esub> (h k2) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h k1) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub>(h k2)"
            by (smt G.inv_closed G.m_closed A hom_inv hom_mult subsetCE)
          thus "x \<in> derived_set H (h ` K)" using k12 by blast
        qed
      qed
      thus ?thesis unfolding derived_def using generate_of_img
        by (simp add: G.derived_set_in_carrier A)
    qed } note aux_lemma = this

  from \<open>K \<subseteq> carrier G\<close> show ?thesis
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    have "(derived H ^^ Suc n) (h ` K) = (derived H) ((derived H ^^ n) (h ` K))" by simp
    also have " ... = (derived H) (h ` ((derived G ^^ n) K))" using Suc by simp
    also have " ... = h ` ((derived G) ((derived G ^^ n) K))"
      using aux_lemma[of "(derived G ^^ n) K"] G.exp_of_derived_in_carrier[OF Suc(2),of n] by linarith
    also have " ... = h ` ((derived G ^^ (Suc n)) K)" by simp
    finally show ?case . 
  qed
qed

theorem (in group_hom) solvable_img_imp_solvable:
  assumes "subgroup I G"
    and "inj_on h I"
    and "solvable_seq H (h ` I)"
  shows "solvable_seq G I"
proof -
  { fix n I assume A: "subgroup I G" "inj_on h I"
    hence "inj_on h ((derived G ^^ n) I)"
    proof -
      have "(derived G  ^^ n) I \<subseteq> I"
      proof (induction n)
        case 0 thus ?case by simp
      next
        case (Suc n)
        hence "(derived G) ((derived G ^^ n) I) \<subseteq> (derived G) I"
          using G.mono_derived[of I "(derived G ^^ n) I" 1,
                               OF subgroup_imp_subset[OF A(1)] Suc] by simp
        thus ?case using A(1) G.derived_incl by auto
      qed
      thus ?thesis using A(2) inj_on_subset by blast
    qed } note aux_lemma = this

  obtain n where "(derived H ^^ n) (h ` I) = { \<one>\<^bsub>H\<^esub> }"
    using H.solvable_imp_subgroup H.solvable_imp_trivial_derived_seq assms(3) by blast
  hence "h ` ((derived G ^^ n) I) = { \<one>\<^bsub>H\<^esub> }"
    by (metis derived_of_img assms(1) subgroup_imp_subset)
  moreover have "inj_on h ((derived G ^^ n) I)"
    using aux_lemma[OF assms(1-2), of n] by simp
  hence "\<And>x. \<lbrakk> x \<in> ((derived G ^^ n) I); h x = \<one>\<^bsub>H\<^esub> \<rbrakk> \<Longrightarrow> x = \<one>"
    by (metis G.exp_of_derived_is_subgroup assms(1) hom_one inj_on_eq_iff subgroup_def)
  ultimately have "(derived G ^^ n) I = { \<one> }" by blast
  thus ?thesis
    using G.trivial_derived_seq_imp_solvable[OF assms(1), of n] by simp
qed

corollary (in group_hom) not_solvable:
  assumes "inj_on h (carrier G)"
    and "\<not> solvable G"
  shows "\<not> solvable H"
proof -
  { fix I J assume A: "subgroup I H" "subgroup J H" "I \<subseteq> J" "solvable_seq H J"
    have "solvable_seq H I"
    proof -
      obtain n where n: "(derived H ^^ n) J = { \<one>\<^bsub>H\<^esub> }"
        using A(4) H.solvable_imp_subgroup H.solvable_imp_trivial_derived_seq by blast
      have "(derived H ^^ n) I \<subseteq> (derived H ^^ n) J"
        using A by (simp add: H.mono_derived H.subgroupE(1))
      hence "(derived H ^^ n) I \<subseteq> { \<one>\<^bsub>H\<^esub> }" using n by simp
      hence "(derived H ^^ n) I = { \<one>\<^bsub>H\<^esub> }"
        by (simp add: A(1) H.exp_of_derived_is_subgroup H.subgroupE(2) subset_singleton_iff)
      thus ?thesis
        using A(1) H.trivial_derived_seq_imp_solvable by blast 
    qed } note aux_lemma = this

  show ?thesis
  proof (rule ccontr)
    assume "\<not> \<not> solvable H"
    hence "solvable_seq H (carrier H)" unfolding solvable_def by simp
    hence "solvable_seq H (h ` (carrier G))"
      using aux_lemma[of "h ` (carrier G)" "carrier H"]
      by (metis G.generateI G.subgroupE(1) G.subgroup_self H.generateE(1)
          H.subgroup_self generate_of_img hom_closed image_subsetI)
    hence "solvable_seq G (carrier G)"
      using G.subgroup_self assms(1) solvable_img_imp_solvable by blast
    hence "solvable G" unfolding solvable_def by simp
    thus False using assms(2) by simp
  qed
qed

end