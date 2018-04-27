theory Papillon
  imports Coset Group_Action
begin

subsection "fundamental lemmas"


lemma (in group) normal_inv_imp :
  assumes "subgroup N G"
and "(\<forall>x\<in>carrier G. \<forall>h\<in>N. x \<otimes> h \<otimes> inv x \<in> N)"
shows "N\<lhd>G"
proof-
  show ?thesis using normal_inv_iff assms by blast
qed

lemma (in group) normal_inv_imp2 :
  assumes"N\<lhd>G" 
shows "subgroup N G" 
and "(\<forall>x\<in>carrier G. \<forall>h\<in>N. x \<otimes> h \<otimes> inv x \<in> N)"
proof-
  show "subgroup N G" using normal_inv_iff assms by blast
next
  show "(\<forall>x\<in>carrier G. \<forall>h\<in>N. x \<otimes> h \<otimes> inv x \<in> N)"using normal_inv_iff assms by blast
qed

text "Lemmas about subgroups"


(*A subgroup included in another subgroup is as subgroup of the subgroup*)
lemma (in group) subgroup_incl :
  assumes "subgroup I G"
    and "subgroup J G"
    and "I\<subseteq>J"
  shows "subgroup I (G\<lparr>carrier:=J\<rparr>)"using assms subgroup_inv_equality
  by (auto simp add: subgroup_def)

(*A subgroup of a subgroup is a subgroup of the group*)
lemma (in group) incl_subgroup :
  assumes "subgroup J G"
    and "subgroup I (G\<lparr>carrier:=J\<rparr>)"
  shows "subgroup I G" unfolding subgroup_def
proof
  have H1: "I \<subseteq> carrier (G\<lparr>carrier:=J\<rparr>)" using assms(2) subgroup_imp_subset by blast
  also have H2: "...\<subseteq>J" by simp
  also  have "...\<subseteq>(carrier G)"  by (simp add: assms(1) subgroup_imp_subset)
  finally have H: "I \<subseteq> carrier G" by simp
  have "(\<And>x y. \<lbrakk>x \<in> I ; y \<in> I\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> I)" using assms(2) by (auto simp add: subgroup_def)
  thus  "I \<subseteq> carrier G \<and> (\<forall>x y. x \<in> I \<longrightarrow> y \<in> I \<longrightarrow> x \<otimes> y \<in> I)"  using H by blast
  have K: "\<one> \<in> I" using assms(2) by (auto simp add: subgroup_def)
  have "(\<And>x. x \<in> I \<Longrightarrow> inv x \<in> I)" using assms  subgroup.m_inv_closed H
    by (metis H1 H2  subgroup_inv_equality subsetCE)
  thus "\<one> \<in> I \<and> (\<forall>x. x \<in> I \<longrightarrow> inv x \<in> I)" using K by blast
qed

text "Lemmas about set_mult"


lemma (in group) set_mult_subgroup_idem :
  assumes "subgroup H G"
  shows "(carrier G)<#>H = carrier G"
proof
  show "(carrier G)<#>H \<subseteq> carrier G" unfolding set_mult_def using subgroup_imp_subset assms by blast
next
  have " (carrier G) #>  \<one> = carrier G" unfolding set_mult_def r_coset_def group_axioms by simp
  moreover have "(carrier G) #>  \<one> \<subseteq> (carrier G) <#> H" unfolding set_mult_def r_coset_def
    using assms subgroup.one_closed[OF assms] by blast
  ultimately show "carrier G \<subseteq> (carrier G) <#> H" by simp
qed


lemma (in group) set_mult_idem :
  assumes "subgroup H G"
and "K1 \<subseteq> H"
and "K2 \<subseteq> H"
shows "K1<#>\<^bsub>(G\<lparr>carrier:=H\<rparr>)\<^esub>K2 = K1<#>K2"
proof 
  show "K1 <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> K2 \<subseteq> K1 <#> K2"
  proof
    fix h assume Hyph : "h\<in>K1<#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>K2"
    then obtain k1 k2 where Hyp : "k1\<in>K1 \<and> k2\<in>K2 \<and> k1\<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>k2 = h" unfolding set_mult_def by blast
    hence "k1\<in>H" using assms by blast
    moreover have  "k2\<in>H" using Hyp assms by blast
    ultimately have EGAL : "k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2 = k1 \<otimes>\<^bsub>G\<^esub> k2" by simp
    have "k1 \<otimes>\<^bsub>G\<^esub> k2 \<in> K1<#>K2" unfolding  set_mult_def using Hyp by blast
    hence "k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2 \<in> K1<#>K2" using EGAL by auto
    thus "h \<in> K1<#>K2 " using Hyp by blast
  qed
  show "K1 <#> K2 \<subseteq> K1 <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> K2"
  proof
    fix h assume Hyph : "h\<in>K1<#>K2"
    then obtain k1 k2 where Hyp : "k1\<in>K1 \<and> k2\<in>K2 \<and> k1\<otimes>k2 = h" unfolding set_mult_def by blast
    hence k1H: "k1\<in>H" using assms by blast
    have  k2H: "k2\<in>H" using Hyp assms by blast
    have EGAL : "k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2 = k1 \<otimes>\<^bsub>G\<^esub> k2" using k1H k2H by simp
    have "k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2 \<in> K1<#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>K2" unfolding  set_mult_def using Hyp by blast
    hence "k1 \<otimes> k2 \<in> K1<#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>K2" using EGAL by auto
    thus "h \<in> K1<#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>K2 " using Hyp by blast
  qed
qed

(*A normal subgroup is commutative with set_mult*)
lemma (in group) commut_normal :
  assumes "subgroup H G"
    and "N\<lhd>G"
  shows "H<#>N = N<#>H" 
proof-
  have aux1 : "{H <#> N} = {\<Union>h\<in>H. h <# N }" unfolding set_mult_def l_coset_def by auto
  also have "... = {\<Union>h\<in>H. N #> h }" using assms normal.coset_eq subgroup.mem_carrier by fastforce
  moreover have aux2 : "{N <#> H} = {\<Union>h\<in>H. N #> h }"unfolding set_mult_def r_coset_def by auto
  ultimately show "H<#>N = N<#>H" by simp
qed

(*Same lemma as above, but everything is included in a subgroup*)
lemma (in group) commut_normal_subgroup :
  assumes "subgroup H G"
    and "N\<lhd>(G\<lparr>carrier:=H\<rparr>)"
    and "subgroup K (G\<lparr>carrier:=H\<rparr>)"
  shows "K<#>N = N<#>K"
proof-
  have "N \<subseteq> carrier (G\<lparr>carrier := H\<rparr>)" using assms normal_imp_subgroup subgroup_imp_subset by blast
  hence NH : "N \<subseteq> H" by simp
  have "K \<subseteq> carrier(G\<lparr>carrier := H\<rparr>)" using subgroup_imp_subset assms by blast
  hence KH : "K \<subseteq> H" by simp
  have Egal : "K <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N = N <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> K"
  using group.commut_normal[where ?G = "G\<lparr>carrier :=H\<rparr>", of K N,OF subgroup_imp_group[OF assms(1)]
               assms(3) assms(2)] by auto
  also have "... = N <#> K" using set_mult_idem[of H N K, OF assms(1) NH KH] by auto
  moreover have "K <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N = K <#> N"
    using set_mult_idem[of H K N, OF assms(1) KH NH] by auto
  ultimately show "K<#>N = N<#>K" by auto
qed



text "Lemmas about intersection and normal subgroups"



lemma (in group) normal_inter:
  assumes "subgroup H G"
    and "subgroup K G"
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
  shows " (H1\<inter>K)\<lhd>(G\<lparr>carrier:= (H\<inter>K)\<rparr>)" 
proof-
  define HK and H1K and GH and GHK
    where "HK = H\<inter>K" and "H1K=H1\<inter>K" and "GH =G\<lparr>carrier := H\<rparr>" and "GHK = (G\<lparr>carrier:= (H\<inter>K)\<rparr>)"
  show "H1K\<lhd>GHK"
  proof (intro group.normal_inv_imp[of GHK H1K])
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
            using  assms(3) normal_imp_subgroup subgroup_imp_subset by blast
          also have "... \<subseteq> H" by simp
          thus "H1K \<subseteq>H\<inter>K" 
            using H1K_def calculation by auto
        qed
        thus "subgroup H1K GHK" using GHK_def by simp

  next
    have "\<And> x h. x\<in>carrier GHK \<Longrightarrow> h\<in>H1K \<Longrightarrow> x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x\<in> H1K"
        proof-
          have invHK: "\<lbrakk>y\<in>HK\<rbrakk> \<Longrightarrow> inv\<^bsub>GHK\<^esub> y = inv\<^bsub>GH\<^esub> y"
            using subgroup_inv_equality assms HK_def GH_def GHK_def subgroups_Inter_pair by simp
          have multHK : "\<lbrakk>x\<in>HK;y\<in>HK\<rbrakk> \<Longrightarrow>  x \<otimes>\<^bsub>(G\<lparr>carrier:=HK\<rparr>)\<^esub> y =  x \<otimes> y"
            using HK_def by simp
          fix x assume p: "x\<in>carrier GHK"
            fix h assume p2 : "h:H1K"
            have "carrier(GHK)\<subseteq>HK"
              using GHK_def HK_def by simp
            hence xHK:"x\<in>HK" using p by auto
            hence invx:"inv\<^bsub>GHK\<^esub> x = inv\<^bsub>GH\<^esub> x"
              using invHK assms GHK_def HK_def GH_def subgroup_inv_equality subgroups_Inter_pair by simp

            have "H1\<subseteq>carrier(GH)"
              using assms GH_def normal_imp_subgroup subgroup_imp_subset by blast
            hence hHK:"h\<in>HK" 
              using p2 H1K_def HK_def GH_def by auto
            hence xhx_egal : "x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub>x =  x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x"
              using invx invHK multHK GHK_def GH_def by auto
            have xH:"x\<in>carrier(GH)" 
              using xHK HK_def GH_def by auto 
            have hH:"h\<in>carrier(GH)"
              using hHK HK_def GH_def by auto 
            have  "(\<forall>x\<in>carrier (GH). \<forall>h\<in>H1.  x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> H1)"
              using assms normal_inv_imp2 GH_def normal.inv_op_closed2 by fastforce
            hence INCL_1 : "x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> H1"
              using  xH H1K_def p2 by blast
            have " x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> HK"
              using assms HK_def subgroups_Inter_pair hHK xHK
              by (metis GH_def inf.cobounded1 subgroup_def subgroup_incl)
            hence " x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> K" using HK_def by simp
            hence " x \<otimes>\<^bsub>GH\<^esub> h \<otimes>\<^bsub>GH\<^esub> inv\<^bsub>GH\<^esub> x \<in> H1K" using INCL_1 H1K_def by auto
            thus  "x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x \<in> H1K" using xhx_egal by simp
        qed
        thus "\<forall>x\<in>carrier GHK. \<forall>h\<in>H1K. x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x \<in> H1K" by auto
    qed
qed


lemma (in group) normal_inter_subgroup :
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
  moreover have "K \<inter> H = H" using K_def assms subgroup_imp_subset by blast
  ultimately show "normal (N\<inter>H) (G\<lparr>carrier := H\<rparr>)" by auto
qed



(*
proof (intro group.normal_inv_imp)
  show "Group.group (G\<lparr>carrier := H\<rparr>)" using assms subgroup_imp_group by auto
  have "subgroup (N \<inter> H) (G)" using assms normal_imp_subgroup subgroups_Inter_pair by blast
  moreover have " (N \<inter> H) \<subseteq> H" by simp
  ultimately show "subgroup (N \<inter> H) (G\<lparr>carrier := H\<rparr>)" using subgroup_incl assms by blast
  have "\<And>x h. x \<in>carrier (G\<lparr>carrier := H\<rparr>) \<Longrightarrow> h\<in>N \<inter> H \<Longrightarrow>
               x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>  inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x \<in> N \<inter> H"
  proof
    fix x h assume xcarrier : "x \<in> carrier (G\<lparr>carrier := H\<rparr>)" and hNH : "h\<in>N \<inter> H"
    have xH : "x \<in> H" using xcarrier by simp
    moreover have hH: "h \<in> H" using hNH by simp
    ultimately have "x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h = x \<otimes> h" by auto
    moreover have " inv\<^bsub>G\<lparr>carrier :=H\<rparr>\<^esub> x =  inv x"
      using xH by (simp add: assms normalizer_imp_subgroup subgroup_imp_subset subgroup_inv_equality)
    ultimately  have xhxegal: "x \<otimes>\<^bsub>G\<lparr>carrier:= H\<rparr>\<^esub> h
                \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x = x \<otimes> h \<otimes> inv x"
      using  hH by simp
    have " x \<otimes> h \<otimes> inv x \<in> N"
      using assms hNH xH subgroup_imp_subset[of H] normal.inv_op_closed2[of N G x h] by auto
    thus " x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x \<in> N"
      using xhxegal by auto
    have " x \<otimes> h \<otimes> inv x \<in> H"
      using assms hNH xH by (simp add: subgroup.m_closed subgroup.m_inv_closed) 
    thus "x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x \<in> H"
      using xhxegal by auto
  qed
  thus "\<forall>x\<in>carrier (G\<lparr>carrier := H\<rparr>). \<forall>h\<in>N \<inter> H.
         x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> h \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x \<in> N \<inter> H "
    by auto
qed

*)




subsection \<open>Second Isomorphism Theorem\<close>




lemma (in group) subgroup_in_normalizer: 
  assumes "subgroup H G"
  shows "normal H (G\<lparr>carrier:= (normalizer G H)\<rparr>)"
proof(intro group.normal_inv_imp)
  show "Group.group (G\<lparr>carrier := normalizer G H\<rparr>)"
    by (simp add: assms group.normalizer_imp_subgroup is_group subgroup_imp_group subgroup_imp_subset)
  have K:"H \<subseteq> (normalizer G H)" unfolding normalizer_def
  proof
    fix x assume xH: "x \<in> H"
    from xH have xG : "x \<in> carrier G" using subgroup_imp_subset assms by auto
    have "x <# H = H"
      by (metis \<open>x \<in> H\<close> assms group.lcos_mult_one is_group
         l_repr_independence one_closed subgroup_imp_subset)
    moreover have "H #> inv x = H" 
      by (simp add: xH assms is_group subgroup.rcos_const subgroup.m_inv_closed)
    ultimately have "x <# H #> (inv x) = H" by simp
    thus " x \<in> stabilizer G (\<lambda>g. \<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) H"
      using assms xG subgroup_imp_subset unfolding stabilizer_def by auto
  qed
  thus "subgroup H (G\<lparr>carrier:= (normalizer G H)\<rparr>)"
    using subgroup_incl normalizer_imp_subgroup assms by (simp add: subgroup_imp_subset)
    have  " \<And>x h. x \<in> carrier (G\<lparr>carrier := normalizer G H\<rparr>) \<Longrightarrow> h \<in> H \<Longrightarrow>
             x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h
               \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x \<in> H"
    proof-
    fix x h assume xnorm : "x \<in> carrier (G\<lparr>carrier := normalizer G H\<rparr>)" and hH : "h \<in> H"
    have xnormalizer:"x \<in> normalizer G H" using xnorm by simp
    moreover have hnormalizer:"h \<in> normalizer G H" using hH K by auto
    ultimately have "x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h = x \<otimes> h" by simp
    moreover have " inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x =  inv x"
      using xnormalizer
      by (simp add: assms normalizer_imp_subgroup subgroup_imp_subset subgroup_inv_equality)
    ultimately  have xhxegal: "x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h
                \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x
                  = x \<otimes>h \<otimes> inv x"
      using  hnormalizer by simp
    have  "x \<otimes>h \<otimes> inv x \<in> (x <# H #> inv x)" using hH xnormalizer assms
      by (smt inv_closed is_group l_coset_subset_G m_closed normalizer_imp_subgroup
       rcosI subgroup.lcos_module_rev subgroup.mem_carrier subgroup_imp_subset transpose_inv)
    moreover have "x <# H #> inv x = H"
      using xnormalizer assms subgroup_imp_subset[OF assms]
      unfolding normalizer_def stabilizer_def by auto
    ultimately have "x \<otimes>h \<otimes> inv x \<in> H" by simp
    thus  " x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h
               \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x \<in> H"
      using xhxegal hH xnorm by simp
  qed
  thus "\<forall>x\<in>carrier (G\<lparr>carrier := normalizer G H\<rparr>). \<forall>h\<in>H.
       x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub>
                                         inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x \<in> H " by simp
qed





lemma (in group) mult_norm_subgroup :
  assumes "normal N G"
    and "subgroup H G"
  shows "subgroup (N<#>H) G" unfolding subgroup_def
proof-
  have  A :"N <#> H \<subseteq> carrier G"
    using assms  set_mult_closed by (simp add: normal_imp_subgroup subgroup_imp_subset)

  have B :"\<And> x y. \<lbrakk>x \<in> (N <#> H); y \<in> (N <#> H)\<rbrakk> \<Longrightarrow> (x \<otimes> y) \<in> (N<#>H)"
  proof-
    fix x y assume B1a: "x \<in> (N <#> H)"  and B1b: "y \<in> (N <#> H)"
    obtain n1 h1 where B2:"n1 \<in> N \<and> h1 \<in> H \<and> n1\<otimes>h1 = x"
      using set_mult_def B1a by (metis (no_types, lifting) UN_E singletonD)
    obtain n2 h2 where B3:"n2 \<in> N \<and> h2 \<in> H \<and> n2\<otimes>h2 = y"
      using set_mult_def B1b by (metis (no_types, lifting) UN_E singletonD)
    have B4:"N #> h1 = h1 <# N"
      using normalI B2 assms normal.coset_eq subgroup_imp_subset by blast
    hence B5: "h1\<otimes>n2 \<in> N #> h1" 
      using B2 B3 assms l_coset_def by fastforce
    obtain y2 where y2_def:"y2 \<in> N" and y2_prop:"y2\<otimes>h1 = h1\<otimes>n2" 
      using B5 singletonD by (metis (no_types, lifting) UN_E r_coset_def) 
    have B6: " x\<otimes>y =  n1 \<otimes> y2 \<otimes> h1 \<otimes> h2" using y2_def B2 B3
      by (smt assms y2_prop m_assoc m_closed normal_imp_subgroup subgroup.mem_carrier)
    have B7 :"n1 \<otimes> y2 \<in>N"
      using B2 y2_def assms normal_imp_subgroup by (metis subgroup_def)
    have "h1 \<otimes> h2 \<in>H" using B2 B3 assms by (simp add: subgroup.m_closed)
    hence "(n1 \<otimes> y2) \<otimes> (h1 \<otimes> h2) \<in>(N<#>H) "
      using B7  unfolding set_mult_def by auto
    hence "n1 \<otimes> y2 \<otimes> h1 \<otimes> h2 \<in>(N<#>H)"
      using m_assoc B2 B3 assms  normal_imp_subgroup by (metis B7 subgroup.mem_carrier)
    thus "x \<otimes> y \<in> N <#> H" using B6 by auto
  qed
  have C :"\<And> x. x\<in>(N<#>H)  \<Longrightarrow> (inv x)\<in>(N<#>H)"

  proof-
    fix x assume C1 : "x \<in> (N<#>H)"
    obtain n h where C2:"n \<in> N \<and> h \<in> H \<and> n\<otimes>h = x"
      using set_mult_def C1 by (metis (no_types, lifting) UN_E singletonD)
    have C3 :"inv(n\<otimes>h) = inv(h)\<otimes>inv(n)"
      by (meson C2  assms inv_mult_group normal_imp_subgroup subgroup.mem_carrier)
    hence "... \<otimes>h \<in> N"
      using assms C2
      by (meson normal.inv_op_closed1 normal_def subgroup.m_inv_closed subgroup.mem_carrier)
    hence  C4:"(inv h \<otimes> inv n \<otimes> h) \<otimes> inv h \<in> (N<#>H)" 
      using   C2 assms subgroup.m_inv_closed[of H G h] unfolding set_mult_def by auto
    have "inv h \<otimes> inv n \<otimes> h \<otimes> inv h = inv h \<otimes> inv n"
      using  subgroup_imp_subset[OF assms(2)] 
      by (metis A C1 C2 C3 inv_closed inv_solve_right m_closed subsetCE)
    thus "inv(x)\<in>N<#>H" using C4 C2 C3 by simp
  qed

  have D : "\<one> \<in> N <#> H"
  proof-
    have D1 : "\<one> \<in> N"
      using assms by (simp add: normal_def subgroup.one_closed)
     have D2 :"\<one> \<in> H"
      using assms by (simp add: subgroup.one_closed)
    thus "\<one> \<in> (N <#> H)"
      using set_mult_def D1 assms by fastforce
  qed
  thus "(N <#> H \<subseteq> carrier G \<and> (\<forall>x y. x \<in> N <#> H \<longrightarrow> y \<in> N <#> H \<longrightarrow> x \<otimes> y \<in> N <#> H)) \<and>
    \<one> \<in> N <#> H \<and> (\<forall>x. x \<in> N <#> H \<longrightarrow> inv x \<in> N <#> H)" using A B C D assms by blast
qed
    

lemma (in group) mult_norm_subgroup_subset :
  assumes "normal N (G\<lparr>carrier:=K\<rparr>)"
  assumes "subgroup H (G\<lparr>carrier:=K\<rparr>)"
  assumes "subgroup K G"
  shows  "subgroup (N<#>H) (G\<lparr>carrier:=K\<rparr>)"
proof-
  have Hyp:"subgroup (N <#>\<^bsub>G\<lparr>carrier := K\<rparr>\<^esub> H) (G\<lparr>carrier := K\<rparr>)"
    using group.mult_norm_subgroup[where ?G = "G\<lparr>carrier := K\<rparr>"] assms subgroup_imp_group by auto
  have "H \<subseteq> carrier(G\<lparr>carrier := K\<rparr>)" using assms subgroup_imp_subset by blast
  also have "... \<subseteq> K" by simp
  finally have Incl1:"H \<subseteq> K" by simp
  have "N \<subseteq> carrier(G\<lparr>carrier := K\<rparr>)" using assms normal_imp_subgroup subgroup_imp_subset by blast
  also have "... \<subseteq> K" by simp
  finally have Incl2:"N \<subseteq> K" by simp
  have "(N <#>\<^bsub>G\<lparr>carrier := K\<rparr>\<^esub> H) = (N <#> H)"
    using set_mult_idem[of K] assms Incl1 Incl2 by simp
  thus "subgroup (N<#>H) (G\<lparr>carrier:=K\<rparr>)" using Hyp by auto
qed


(*  "h ` carrier G = carrier H
   \<Longrightarrow> (\<lambda>X. the_elem (h`X)) \<in> (G Mod (kernel G H h)) \<cong> H"*)

lemma (in group) normal_intersection_hom:
  assumes "subgroup H G"
and "normal N G"
shows "group_hom (G\<lparr>carrier := H\<rparr>) ((G\<lparr>carrier := N <#> H\<rparr>) Mod N) (\<lambda>g. N #> g)"
  sorry

lemma (in group) normal_intersection_hom_kernel:
  assumes "subgroup H G"
and "normal N G"
shows "kernel (G\<lparr>carrier := H\<rparr>) ((G\<lparr>carrier := N <#> H\<rparr>) Mod H) (\<lambda>g. N #> g) = N \<inter> H"
  sorry

lemma (in group) subgroup_of_normal_set_mult :
  assumes "normal N G"
and "subgroup H G"
shows "subgroup H (G\<lparr>carrier := N <#> H\<rparr>)"
  sorry


lemma (in group) normal_in_normal_set_mult :
  assumes "normal N G"
and "subgroup H G"
shows "normal N (G\<lparr>carrier := N <#> H\<rparr>)"
  sorry


proposition (in group) weak_snd_iso_thme :
  assumes "subgroup  H G" 
    and "N\<lhd>G"
  shows "(G\<lparr>carrier := N<#>H\<rparr> Mod N \<cong> G\<lparr>carrier:=H\<rparr> Mod (N\<inter>H))\<noteq> {} "
proof-
  define f where "f = op #> N"
  have GroupNH : "Group.group (G\<lparr>carrier := N<#>H\<rparr>)"
    using subgroup_imp_group assms mult_norm_subgroup by simp
  have  HcarrierNH :"H \<subseteq> carrier(G\<lparr>carrier := N<#>H\<rparr>)"
    using assms subgroup_of_normal_set_mult subgroup_imp_subset by blast
  hence HNH :"H \<subseteq> N<#>H" by simp
  have op_hom : "f \<in> hom (G\<lparr>carrier := H\<rparr>) (G\<lparr>carrier := N <#> H\<rparr> Mod N)" unfolding hom_def
  proof
    have "\<And>x . x \<in> carrier (G\<lparr>carrier :=H\<rparr>) \<Longrightarrow>
       op #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N x \<in>  carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
    proof-
      fix x assume  "x \<in> carrier (G\<lparr>carrier :=H\<rparr>)"
      hence xH : "x \<in> H" by simp
      hence "op #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N x \<in> rcosets\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N"
        using HcarrierNH RCOSETS_def[where ?G = "G\<lparr>carrier := N <#> H\<rparr>"] by blast
      thus "op #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N x \<in>  carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
        unfolding FactGroup_def by simp
    qed
    hence "op #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N \<in> carrier (G\<lparr>carrier :=H\<rparr>) \<rightarrow>
            carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)" by auto
    hence "f \<in> carrier (G\<lparr>carrier :=H\<rparr>) \<rightarrow> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      unfolding r_coset_def f_def  by simp
    moreover have "\<And>x y. x\<in>carrier (G\<lparr>carrier := H\<rparr>) \<Longrightarrow> y\<in>carrier (G\<lparr>carrier := H\<rparr>) \<Longrightarrow>
                  f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y)"
    proof-
      fix x y assume "x\<in>carrier (G\<lparr>carrier := H\<rparr>)" "y\<in>carrier (G\<lparr>carrier := H\<rparr>)"
      hence xHyH :"x \<in> H" "y \<in> H" by auto
      have Nxeq :"N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x = N #>x" unfolding r_coset_def by simp
      have Nyeq :"N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y = N #>y" unfolding r_coset_def by simp

      have "x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y =x \<otimes>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y" by simp
      hence "N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y
             = N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x \<otimes>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y" by simp
      also have "... = (N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> x) <#>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub>
                       (N #>\<^bsub>G\<lparr>carrier := N<#>H\<rparr>\<^esub> y)"
        using normal.rcos_sum[OF normal_in_normal_set_mult[OF assms(2) assms(1)], of x y]
             xHyH assms HcarrierNH by auto
      finally show "f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y)"
        unfolding  FactGroup_def r_coset_def f_def  using Nxeq Nyeq  by auto
    qed
    hence "(\<forall>x\<in>carrier (G\<lparr>carrier := H\<rparr>). \<forall>y\<in>carrier (G\<lparr>carrier := H\<rparr>).
           f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y))" by blast
    ultimately show  " f \<in> carrier (G\<lparr>carrier := H\<rparr>) \<rightarrow> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N) \<and>
    (\<forall>x\<in>carrier (G\<lparr>carrier := H\<rparr>). \<forall>y\<in>carrier (G\<lparr>carrier := H\<rparr>).
     f (x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y) =  f(x) \<otimes>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub> f(y))"
      by auto
  qed
  hence homomorphism : "group_hom (G\<lparr>carrier := H\<rparr>) (G\<lparr>carrier := N <#> H\<rparr> Mod N) f"
    unfolding group_hom_def group_hom_axioms_def using subgroup_imp_group[OF assms(1)]
             normal.factorgroup_is_group[OF normal_in_normal_set_mult[OF assms(2) assms(1)]] by auto
  moreover have im_f :  "(f  ` carrier(G\<lparr>carrier:=H\<rparr>)) = carrier(G\<lparr>carrier := N <#> H\<rparr> Mod N)"
  proof
    show  "f ` carrier (G\<lparr>carrier := H\<rparr>) \<subseteq> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      using op_hom unfolding hom_def using funcset_image by blast
  next
    show "carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N) \<subseteq> f ` carrier (G\<lparr>carrier := H\<rparr>)"
    proof
      fix x assume p : " x \<in> carrier (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      hence "x \<in> \<Union>{y. \<exists>x\<in>carrier (G\<lparr>carrier := N <#> H\<rparr>). y = {N #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> x}}"
        unfolding FactGroup_def RCOSETS_def by auto
      hence hyp :"\<exists>y. \<exists>h\<in>carrier (G\<lparr>carrier := N <#> H\<rparr>). y = {N #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> h} \<and> x \<in> y"
        using Union_iff by blast
      from hyp obtain nh where nhNH:"nh \<in>carrier (G\<lparr>carrier := N <#> H\<rparr>)"
                          and "x \<in> {N #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> nh}"
        by blast
      hence K: "x = op #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N nh" by simp
      have "nh \<in> N <#> H" using nhNH by simp
      from this obtain n h where nN : "n \<in> N" and hH : " h \<in> H" and nhnh: "n \<otimes> h = nh"
        unfolding set_mult_def by blast
      have  "x = op #>\<^bsub>G\<lparr>carrier := N <#> H\<rparr>\<^esub> N (n \<otimes> h)" using K nhnh by simp
      hence  "x = op #> N (n \<otimes> h)" using K nhnh unfolding r_coset_def by auto
      also have "... = (N #> n) #>h"
        using coset_mult_assoc hH nN assms subgroup_imp_subset normal_imp_subgroup
        by (metis subgroup.mem_carrier)
      finally have "x = op #> N h"
        using coset_join2[of n N] nN assms by (simp add: normal_imp_subgroup subgroup.mem_carrier)
      thus "x \<in> f ` carrier (G\<lparr>carrier := H\<rparr>)" using hH unfolding f_def by simp
    qed
  qed
  moreover have ker_f :"kernel (G\<lparr>carrier := H\<rparr>) (G\<lparr>carrier := N<#>H\<rparr> Mod N) f  = N\<inter>H"
    unfolding kernel_def f_def
    proof-
      have "{x \<in> carrier (G\<lparr>carrier := H\<rparr>). N #> x = \<one>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub>} =
            {x \<in> carrier (G\<lparr>carrier := H\<rparr>). N #> x = N}" unfolding FactGroup_def by simp
      also have "... = {x \<in> carrier (G\<lparr>carrier := H\<rparr>). x \<in> N}"
        using coset_join1
        by (metis (no_types, lifting) assms group.subgroup_self incl_subgroup is_group
          normal_imp_subgroup subgroup.mem_carrier subgroup.rcos_const subgroup_imp_group)
      also have "... =N \<inter> (carrier(G\<lparr>carrier := H\<rparr>))" by auto
      finally show "{x \<in> carrier (G\<lparr>carrier := H\<rparr>). N#>x = \<one>\<^bsub>G\<lparr>carrier := N <#> H\<rparr> Mod N\<^esub>} = N \<inter> H"
        by simp
    qed
    ultimately have "(\<lambda>X. the_elem (f`X)) \<in>  (G\<lparr>carrier := H\<rparr> Mod N \<inter> H) \<cong> (G\<lparr>carrier := N <#> H\<rparr> Mod N)"
      using group_hom.FactGroup_iso[OF homomorphism im_f] by auto
    hence "inv_into (carrier (G\<lparr>carrier := H\<rparr> Mod N \<inter> H)) (\<lambda>X. the_elem (f`X)) \<in>
                      G\<lparr>carrier := N <#> H\<rparr> Mod N \<cong> G\<lparr>carrier := H\<rparr> Mod N \<inter> H"
      by (simp add: group.iso_sym assms normal.factorgroup_is_group normal_inter_subgroup)
    thus "G\<lparr>carrier := N <#> H\<rparr> Mod N \<cong> G\<lparr>carrier := H\<rparr> Mod N \<inter> H \<noteq> {}" by auto
qed


theorem (in group) snd_iso_thme :
  assumes "subgroup H G"
    and "subgroup N G"
    and "subgroup H (G\<lparr>carrier:= (normalizer G N)\<rparr>)"
  shows "(G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong> (G\<lparr>carrier:= H\<rparr> Mod (H\<inter>N)) \<noteq> {}"
proof-
  have "G\<lparr>carrier := normalizer G N, carrier := H\<rparr>
       = G\<lparr>carrier := H\<rparr>"  by simp
  hence "G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H =
         G\<lparr>carrier := H\<rparr> Mod N \<inter> H" by auto
  moreover have "G\<lparr>carrier := normalizer G N,
                    carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> =
                G\<lparr>carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr>" by simp
  hence "G\<lparr>carrier := normalizer G N,
          carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N =
          G\<lparr>carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N" by auto
  hence "G\<lparr>carrier := normalizer G N,
          carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N  \<cong>
         G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H =
          (G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong>
         G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H" unfolding iso_def
using group.weak_snd_iso_thme[OF subgroup_imp_group[OF normalizer_imp_subgroup[OF
subgroup_imp_subset[OF assms(2)]]] assms(3) subgroup_in_normalizer[OF assms(2)]]
 
  

  sorry

theorem (in group) snd_iso_thme_recip :
  assumes "subgroup H G"
    and "subgroup N G"
    and "subgroup H (G\<lparr>carrier:= (normalizer G N)\<rparr>)"
  shows "(G\<lparr>carrier:= H<#>N\<rparr> Mod N)  \<cong> (G\<lparr>carrier:= H\<rparr> Mod (H\<inter>N)) \<noteq> {}"
  using snd_iso_thme[OF assms]
  by (metis assms(2) assms(3) commut_normal_subgroup group.subgroup_in_normalizer
      is_group normalizer_imp_subgroup subgroup_imp_subset)



lemma (in group) distinc :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>" 
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(H\<inter>K)\<lhd> (G\<lparr>carrier:=(normalizer G (H1<#>(H\<inter>K1))) \<rparr>)"
  sorry








lemma (in group) idem_set_mult_subgroup :
  assumes "subgroup H G"
    and "subgroup N (G\<lparr>carrier:=H\<rparr>)"
  shows "H<#>N = H" 
proof-
  define GH where "GH = G\<lparr>carrier:=H\<rparr>"
  have GHgroup : "Group.group GH" using subgroup_imp_group assms GH_def by simp
  have "subgroup N GH" using assms GH_def by simp
  have EGAL:"H<#>\<^bsub>G\<lparr>carrier:=H\<rparr>\<^esub>N = H<#>N" 
  proof (intro set_mult_idem)
    show "subgroup H G " using assms by auto
    have "N\<subseteq>carrier(G\<lparr>carrier:=H\<rparr>)" using assms subgroup_imp_subset by blast
    thus "N\<subseteq>H" by simp
    show "H\<subseteq>H" by auto
  qed
  have "carrier(GH)<#>\<^bsub>GH\<^esub>N = carrier(GH)"
    using group.set_mult_subgroup_idem assms GH_def GHgroup by blast
  hence "H<#>\<^bsub>G\<lparr>carrier:=H\<rparr>\<^esub>N = H" using GH_def by auto
  thus "H<#>N = H" using EGAL by auto
qed









lemma (in group) preliminary :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>" 
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows " (H\<inter>K) \<inter> (H1<#>(H\<inter>K1)) = (H1\<inter>K)<#>(H\<inter>K1)"
  sorry

lemma (in group) distin :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(H1<#>(H\<inter>K1)) \<lhd> G\<lparr>carrier:=(H1<#>(H\<inter>K))\<rparr>  \<and> (K1<#>(K\<inter>H1)) \<lhd> G\<lparr>carrier:=(K1<#>(H\<inter>K))\<rparr> "
  sorry





proposition (in group)  Zassenhaus_1 :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>" 
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod (H1<#>(H\<inter>K1)))  \<cong> (G\<lparr>carrier:= (H\<inter>K)\<rparr> Mod  ((H1\<inter>K)<#>(H\<inter>K1))) \<noteq> {}"
proof-
  define N  and N1 where "N = (H\<inter>K)" and "N1 =H1<#>(H\<inter>K1)"
  have normal_N_N1 : "normal N (G\<lparr>carrier:=(normalizer G N1)\<rparr>)"
    by (simp add: N1_def N_def assms distinc)
  have Hp:"(G\<lparr>carrier:= N<#>N1\<rparr> Mod N1)  \<cong> (G\<lparr>carrier:= N\<rparr> Mod (N\<inter>N1)) \<noteq> {}"
  by (metis N1_def N_def assms incl_subgroup inf_le1 mult_norm_subgroup_subset
        normal_N_N1 normal_imp_subgroup snd_iso_thme_recip subgroup_incl subgroups_Inter_pair)
  have H_simp: "N<#>N1 = H1<#> (H\<inter>K)"
  proof-
    have H1_incl_G : "H1 \<subseteq> carrier G"
      using assms normal_imp_subgroup incl_subgroup subgroup_imp_subset by blast
    have K1_incl_G :"K1 \<subseteq> carrier G"
      using assms normal_imp_subgroup incl_subgroup subgroup_imp_subset by blast
    have "N<#>N1=  (H\<inter>K)<#> (H1<#>(H\<inter>K1))" by (auto simp add: N_def N1_def)
    also have "... = ((H\<inter>K)<#>H1) <#>(H\<inter>K1)"
      using set_mult_assoc[where ?M = "H\<inter>K"] K1_incl_G H1_incl_G assms
      by (simp add: inf.coboundedI2 subgroup_imp_subset)
    also have "... = (H1<#>(H\<inter>K))<#>(H\<inter>K1)" 
      using commut_normal_subgroup assms subgroup_incl subgroups_Inter_pair by auto
    also have "... =  H1 <#> ((H\<inter>K)<#>(H\<inter>K1))"
      using set_mult_assoc K1_incl_G H1_incl_G assms
      by (simp add: inf.coboundedI2 subgroup_imp_subset)
    also have " ((H\<inter>K)<#>(H\<inter>K1)) = (H\<inter>K)"
    proof (intro idem_set_mult_subgroup[where ?H = "H\<inter>K" and ?N="H\<inter>K1",
             OF subgroups_Inter_pair[OF assms(1) assms(3)]])
      show "subgroup (H \<inter> K1) (G\<lparr>carrier := H \<inter> K\<rparr>)"
        using subgroup_incl [where ?I = "H\<inter>K1" and ?J = "H\<inter>K",
                             OF subgroups_Inter_pair[OF assms(1)
                             incl_subgroup[of K K1, OF assms(3) normal_imp_subgroup[OF assms(4)]]]
                            subgroups_Inter_pair[OF assms(1) assms(3)]]
        using  normal_imp_subgroup assms by (metis inf_commute normal_inter)
    qed
    hence " H1 <#> ((H\<inter>K)<#>(H\<inter>K1)) =  H1 <#> ((H\<inter>K))" 
      by simp
    thus "N <#> N1 = H1 <#> H \<inter> K"
      by (simp add: calculation)
  qed

  have "N\<inter>N1 = (H1\<inter>K)<#>(H\<inter>K1)" 
    using preliminary assms N_def N1_def by simp 
  thus  "(G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod N1)  \<cong> (G\<lparr>carrier:= N\<rparr> Mod  ((H1\<inter>K)<#>(H\<inter>K1))) \<noteq> {}"
    using H_simp Hp by auto
qed

theorem (in group) Zassenhaus :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>" 
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod (H1<#>(H\<inter>K1)))  \<cong> 
         (G\<lparr>carrier:= K1 <#> (H\<inter>K)\<rparr> Mod (K1<#>(K\<inter>H1)))  \<noteq> {}"
proof-
  define HK Gmod1 Gmod2 Gmod3 Gmod4  where "HK = K\<inter>H"
                         and "Gmod1 = (G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod (H1<#>(H\<inter>K1))) "
                         and "Gmod2 = (G\<lparr>carrier:= K1 <#> (K\<inter>H)\<rparr> Mod (K1<#>(K\<inter>H1)))"
                         and "Gmod3 = (G\<lparr>carrier:= (H\<inter>K)\<rparr> Mod  ((H1\<inter>K)<#>(H\<inter>K1)))"
                         and "Gmod4 = (G\<lparr>carrier:= (K\<inter>H)\<rparr> Mod  ((K1\<inter>H)<#>(K\<inter>H1)))"
  have H1 :  "Gmod1  \<cong> Gmod3 \<noteq> {}"
    using Zassenhaus_1 assms Gmod1_def Gmod3_def  by auto
  have H2 :  "Gmod2  \<cong>  Gmod4 \<noteq> {}"
    using Zassenhaus_1 assms Gmod2_def Gmod4_def  by auto
  have Egal:"Gmod3 = Gmod4"
  proof-
    have permut1: "H\<inter>K = K\<inter>H" by blast
    hence permut2: "H1\<inter>K = K\<inter>H1" by blast
    hence  "H\<inter>K1 = K1\<inter>H" by blast
    hence Hp : "Gmod3 =
                G\<lparr>carrier:= (K\<inter>H)\<rparr> Mod ((K\<inter>H1)<#>(K1\<inter>H))"
      by (simp add: Gmod3_def permut1 permut2)
    have "(K\<inter>H1)<#>(K1\<inter>H) =(K1\<inter>H)<#>(K\<inter>H1)"
    proof (intro commut_normal_subgroup[of HK ])
      show  "subgroup HK G" using assms subgroups_Inter_pair HK_def by auto
    next
      show "K1 \<inter> H \<lhd> G\<lparr>carrier := HK\<rparr>" 
        using normal_inter  HK_def assms by blast
    next
      have "subgroup H1 G" using normal_imp_subgroup assms incl_subgroup by blast
      thus "subgroup (K \<inter> H1) (G\<lparr>carrier := HK\<rparr>)"
        using subgroup_incl by (simp add: HK_def assms inf_commute normal_imp_subgroup normal_inter) 
    qed
    thus  "Gmod3  = Gmod4" using Hp Gmod4_def by simp
    qed
    obtain g where "g\<in>Gmod2  \<cong>  Gmod4" using H2 by blast
    note g_def=this
    define  h where "h = (inv_into (carrier(Gmod2)) g)"
    from g_def have h_def: "h\<in> (Gmod4 \<cong>  Gmod2)"
      using  assms by (simp add: Gmod4_def Gmod2_def group.iso_sym distin h_def normal.factorgroup_is_group)

    obtain f where "f\<in>Gmod1  \<cong>  Gmod3" using H1 by blast
    hence  "(compose (carrier(Gmod1)) h f) \<in> Gmod1 \<cong> Gmod2" using Egal h_def
      by (simp add: Gmod1_def assms group.distin group.iso_trans is_group normal.factorgroup_is_group)
    hence  "Gmod1 \<cong> Gmod2 \<noteq> {}" by auto
    thus ?thesis 
      using Gmod1_def Gmod2_def  by (simp add: inf_commute)
  qed

