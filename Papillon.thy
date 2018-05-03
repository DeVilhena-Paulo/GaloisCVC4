theory Papillon
  imports Coset Group_Action
begin

subsection "fundamental lemmas"




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


lemma (in group) set_mult_same_law :
  assumes "subgroup H G"
and "K1 \<subseteq> H"
and "K2 \<subseteq> H"
shows "K1<#>\<^bsub>(G\<lparr>carrier:=H\<rparr>)\<^esub>K2 = K1<#>K2"
proof 
  show "K1 <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> K2 \<subseteq> K1 <#> K2"
  proof
    fix h assume Hyph : "h\<in>K1<#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>K2"
    then obtain k1 k2 where Hyp : "k1\<in>K1 \<and> k2\<in>K2 \<and> k1\<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>k2 = h"
      unfolding set_mult_def by blast
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


(*A group multiplied by a subgroup stays the same*)
lemma (in group) set_mult_carrier_idem :
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

(*Same lemma as above, but everything is included in a subgroup*)
lemma (in group) set_mult_subgroup_idem :
  assumes "subgroup H G"
    and "subgroup N (G\<lparr>carrier:=H\<rparr>)"
  shows "H<#>N = H"
  using group.set_mult_carrier_idem[OF subgroup_imp_group] subgroup_imp_subset assms
  by (metis monoid.cases_scheme order_refl partial_object.simps(1)
      partial_object.update_convs(1) set_mult_same_law)

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
  also have "... = N <#> K" using set_mult_same_law[of H N K, OF assms(1) NH KH] by auto
  moreover have "K <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N = K <#> N"
    using set_mult_same_law[of H K N, OF assms(1) KH NH] by auto
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
            using  assms(3) normal_imp_subgroup subgroup_imp_subset by blast
          also have "... \<subseteq> H" by simp
          thus "H1K \<subseteq>H\<inter>K" 
            using H1K_def calculation by auto
        qed
        thus "subgroup H1K GHK" using GHK_def by simp

  next
    show "\<And> x h. x\<in>carrier GHK \<Longrightarrow> h\<in>H1K \<Longrightarrow> x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x\<in> H1K"
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
proof (intro group.normal_invI)
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



text \<open>Lemmas about normalizer\<close>


lemma (in group) subgroup_in_normalizer: 
  assumes "subgroup H G"
  shows "normal H (G\<lparr>carrier:= (normalizer G H)\<rparr>)"
proof(intro group.normal_invI)
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
  show  " \<And>x h. x \<in> carrier (G\<lparr>carrier := normalizer G H\<rparr>) \<Longrightarrow> h \<in> H \<Longrightarrow>
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
    have  "x \<otimes>h \<otimes> inv x \<in> (x <# H #> inv x)"
      unfolding l_coset_def r_coset_def using hH  by auto
    moreover have "x <# H #> inv x = H"
      using xnormalizer assms subgroup_imp_subset[OF assms]
      unfolding normalizer_def stabilizer_def by auto
    ultimately have "x \<otimes>h \<otimes> inv x \<in> H" by simp
    thus  " x \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> h
               \<otimes>\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := normalizer G H\<rparr>\<^esub> x \<in> H"
      using xhxegal hH xnorm by simp
  qed
qed


lemma (in group) normal_imp_subgroup_normalizer :
  assumes "subgroup H G"
and "N \<lhd> (G\<lparr>carrier := H\<rparr>)"
shows "subgroup H (G\<lparr>carrier := normalizer G N\<rparr>)" 
proof-
  have N_carrierG : "N \<subseteq> carrier(G)"
    using assms normal_imp_subgroup subgroup_imp_subset
    by (smt monoid.cases_scheme order_trans partial_object.simps(1) partial_object.update_convs(1))
  {have "H \<subseteq> normalizer G N" unfolding normalizer_def stabilizer_def
    proof
    fix x assume xH : "x \<in> H"
    hence xcarrierG : "x \<in> carrier(G)" using assms subgroup_imp_subset  by auto
    have "   N #> x = x <# N" using assms xH
      unfolding r_coset_def l_coset_def normal_def normal_axioms_def subgroup_imp_group by auto
    hence "x <# N #> inv x =(N #> x) #> inv x"
      by simp
    also have "... = N #> \<one>"
      using  assms r_inv xcarrierG coset_mult_assoc[OF N_carrierG] by simp  
    finally have "x <# N #> inv x = N" by (simp add: N_carrierG)
    thus "x \<in> {g \<in> carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) N = N}"
      using xcarrierG by (simp add : N_carrierG)
  qed}
  thus "subgroup H (G\<lparr>carrier := normalizer G N\<rparr>)"
    using subgroup_incl[OF assms(1) normalizer_imp_subgroup]
         assms normal_imp_subgroup subgroup_imp_subset
    by (metis  group.incl_subgroup is_group)
qed


subsection \<open>Second Isomorphism Theorem\<close>


lemma (in group) mult_norm_subgroup :
  assumes "normal N G"
    and "subgroup H G"
  shows "subgroup (N<#>H) G" unfolding subgroup_def
proof-
  have  A :"N <#> H \<subseteq> carrier G"
    using assms  setmult_subset_G by (simp add: normal_imp_subgroup subgroup_imp_subset)

  have B :"\<And> x y. \<lbrakk>x \<in> (N <#> H); y \<in> (N <#> H)\<rbrakk> \<Longrightarrow> (x \<otimes> y) \<in> (N<#>H)"
  proof-
    fix x y assume B1a: "x \<in> (N <#> H)"  and B1b: "y \<in> (N <#> H)"
    obtain n1 h1 where B2:"n1 \<in> N \<and> h1 \<in> H \<and> n1\<otimes>h1 = x"
      using set_mult_def B1a by (metis (no_types, lifting) UN_E singletonD)
    obtain n2 h2 where B3:"n2 \<in> N \<and> h2 \<in> H \<and> n2\<otimes>h2 = y"
      using set_mult_def B1b by (metis (no_types, lifting) UN_E singletonD)
    have "N #> h1 = h1 <# N"
      using normalI B2 assms normal.coset_eq subgroup_imp_subset by blast
    hence "h1\<otimes>n2 \<in> N #> h1" 
      using B2 B3 assms l_coset_def by fastforce
    from this obtain y2 where y2_def:"y2 \<in> N" and y2_prop:"y2\<otimes>h1 = h1\<otimes>n2" 
      using singletonD by (metis (no_types, lifting) UN_E r_coset_def) 
    have " x\<otimes>y =  n1 \<otimes> y2 \<otimes> h1 \<otimes> h2" using y2_def B2 B3
      by (smt assms y2_prop m_assoc m_closed normal_imp_subgroup subgroup.mem_carrier)
    moreover have B4 :"n1 \<otimes> y2 \<in>N"
      using B2 y2_def assms normal_imp_subgroup by (metis subgroup_def)
    moreover have "h1 \<otimes> h2 \<in>H" using B2 B3 assms by (simp add: subgroup.m_closed)
    hence "(n1 \<otimes> y2) \<otimes> (h1 \<otimes> h2) \<in>(N<#>H) "
      using B4  unfolding set_mult_def by auto
    hence "n1 \<otimes> y2 \<otimes> h1 \<otimes> h2 \<in>(N<#>H)"
      using m_assoc B2 B3 assms  normal_imp_subgroup by (metis B4 subgroup.mem_carrier)
    ultimately show  "x \<otimes> y \<in> N <#> H" by auto
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
    

lemma (in group) mult_norm_sub_in_sub :
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
    using set_mult_same_law[of K] assms Incl1 Incl2 by simp
  thus "subgroup (N<#>H) (G\<lparr>carrier:=K\<rparr>)" using Hyp by auto
qed


lemma (in group) subgroup_of_normal_set_mult :
  assumes "normal N G"
and "subgroup H G"
shows "subgroup H (G\<lparr>carrier := N <#> H\<rparr>)"
proof-
  have "\<one> \<in> N" using normal_imp_subgroup assms(1) subgroup_def by blast
  hence "\<one> <# H \<subseteq> N <#> H" unfolding set_mult_def l_coset_def by blast
  hence H_incl : "H \<subseteq> N <#> H"
    by (metis assms(2) lcos_mult_one subgroup_def)
  show "subgroup H (G\<lparr>carrier := N <#> H\<rparr>)"
  using subgroup_incl[OF assms(2) mult_norm_subgroup[OF assms(1) assms(2)] H_incl] .
qed


lemma (in group) normal_in_normal_set_mult :
  assumes "normal N G"
and "subgroup H G"
shows "normal N (G\<lparr>carrier := N <#> H\<rparr>)"
proof-
  have "\<one> \<in> H" using  assms(2) subgroup_def by blast
  hence "N #> \<one>  \<subseteq> N <#> H" unfolding set_mult_def r_coset_def by blast
  hence N_incl : "N \<subseteq> N <#> H"
    by (metis assms(1) normal_imp_subgroup coset_mult_one subgroup_def)
  thus "normal N (G\<lparr>carrier := N <#> H\<rparr>)"
    using normal_inter_subgroup[OF mult_norm_subgroup[OF assms] assms(1)]
    by (simp add : inf_absorb1)
qed


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
         G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H" 
    using set_mult_same_law[OF  normalizer_imp_subgroup[OF subgroup_imp_subset[OF assms(2)]], of N H] 
          subgroup_imp_subset[OF assms(3)]
          subgroup_imp_subset[OF normal_imp_subgroup[OF subgroup_in_normalizer[OF assms(2)]]]
    by simp
  ultimately have "G\<lparr>carrier := normalizer G N,
                    carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N  \<cong>
                  G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H =
                 (G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong>  G\<lparr>carrier := H\<rparr> Mod N \<inter> H" by auto
  moreover have "G\<lparr>carrier := normalizer G N,
                    carrier := N <#>\<^bsub>G\<lparr>carrier := normalizer G N\<rparr>\<^esub> H\<rparr> Mod N  \<cong>
                  G\<lparr>carrier := normalizer G N, carrier := H\<rparr> Mod N \<inter> H \<noteq> {}"
    using group.weak_snd_iso_thme[OF subgroup_imp_group[OF normalizer_imp_subgroup[OF
          subgroup_imp_subset[OF assms(2)]]] assms(3) subgroup_in_normalizer[OF assms(2)]]
    by simp
  moreover have "H\<inter>N = N\<inter>H" using assms  by auto
  ultimately show "(G\<lparr>carrier:= N<#>H\<rparr> Mod N)  \<cong>  G\<lparr>carrier := H\<rparr> Mod H \<inter> N \<noteq> {}" by auto
qed
 

corollary (in group) snd_iso_thme_recip :
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
  shows "subgroup (H\<inter>K) (G\<lparr>carrier:=(normalizer G (H1<#>(H\<inter>K1))) \<rparr>)"
proof (intro subgroup_incl[OF subgroups_Inter_pair[OF assms(1) assms(3)]])
  show "subgroup (normalizer G (H1 <#> H \<inter> K1)) G"
    using normalizer_imp_subgroup assms normal_imp_subgroup subgroup_imp_subset
    by (metis group.incl_subgroup is_group setmult_subset_G subgroups_Inter_pair)
next
  show "H \<inter> K \<subseteq> normalizer G (H1 <#> H \<inter> K1)" unfolding normalizer_def stabilizer_def
  proof
    fix x assume xHK : "x \<in> H \<inter> K"
    hence xG : "{x} \<subseteq> carrier G" "{inv x} \<subseteq> carrier G"
      using subgroup_imp_subset assms inv_closed xHK by auto
    have allG : "H \<subseteq> carrier G" "K \<subseteq> carrier G" "H1 \<subseteq> carrier G"  "K1 \<subseteq> carrier G"
      using assms subgroup_imp_subset normal_imp_subgroup incl_subgroup apply blast+ .
    have HK1_normal: "H\<inter>K1 \<lhd> (G\<lparr>carrier :=  H \<inter> K\<rparr>)" using normal_inter[OF assms(3)assms(1)assms(4)]
      by (simp add : inf_commute)
    have "H \<inter> K \<subseteq> normalizer G (H \<inter> K1)"
      using subgroup_imp_subset[OF normal_imp_subgroup_normalizer[OF subgroups_Inter_pair[OF
            assms(1)assms(3)]HK1_normal]] by auto
    hence "x <# (H \<inter> K1) #> inv x = (H \<inter> K1)"
      using xHK subgroup_imp_subset[OF subgroups_Inter_pair[OF assms(1) incl_subgroup[OF assms(3)
                                                            normal_imp_subgroup[OF assms(4)]]]]
      unfolding normalizer_def stabilizer_def by auto
    moreover have "H \<subseteq>  normalizer G H1"
      using subgroup_imp_subset[OF normal_imp_subgroup_normalizer[OF assms(1)assms(2)]] by auto
    hence "x <# H1 #> inv x = H1"
      using xHK subgroup_imp_subset[OF  incl_subgroup[OF assms(1) normal_imp_subgroup[OF assms(2)]]]
      unfolding normalizer_def stabilizer_def by auto
    ultimately have "H1 <#> H \<inter> K1 = (x <# H1 #> inv x) <#> (x <#  H \<inter> K1 #> inv x)" by auto
    also have "... = ({x} <#> H1) <#> {inv x} <#> ({x} <#>  H \<inter> K1 <#> {inv x})"
      by (simp add : r_coset_eq_set_mult l_coset_eq_set_mult)
    also have "... = ({x} <#> H1 <#> {inv x} <#> {x}) <#>  (H \<inter> K1 <#> {inv x})"
      by (smt Int_lower1 allG xG set_mult_assoc subset_trans setmult_subset_G)
    also have "... = ({x} <#> H1 <#> {\<one>}) <#>  (H \<inter> K1 <#> {inv x})"
      using allG xG coset_mult_assoc by (simp add: r_coset_eq_set_mult setmult_subset_G)
    also have "... =({x} <#> H1) <#>  (H \<inter> K1 <#> {inv x})"
      using coset_mult_one r_coset_eq_set_mult[of G H1 \<one>] set_mult_assoc[OF xG(1) allG(3)] allG
      by auto
    also have "... = {x} <#> (H1 <#> H \<inter> K1) <#> {inv x}"
      using allG xG set_mult_assoc setmult_subset_G by (metis inf.coboundedI2)
    finally have "H1 <#> H \<inter> K1 = x <# (H1 <#> H \<inter> K1) #> inv x" 
      using xG setmult_subset_G allG by (simp add: l_coset_eq_set_mult r_coset_eq_set_mult)
    thus "x \<in> {g \<in> carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) (H1 <#> H \<inter> K1)
                                                                       = H1 <#> H \<inter> K1}"
      using xG allG setmult_subset_G[OF allG(3), where ?K = "H\<inter>K1"] xHK
      by auto
  qed
qed




lemma (in group) preliminary1 :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>" 
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows " (H\<inter>K) \<inter> (H1<#>(H\<inter>K1)) = (H1\<inter>K)<#>(H\<inter>K1)"
proof
  have all_inclG : "H \<subseteq> carrier G" "H1 \<subseteq> carrier G" "K \<subseteq> carrier G" "K1 \<subseteq> carrier G"
    using assms subgroup_imp_subset normal_imp_subgroup incl_subgroup apply blast+.
  show "H \<inter> K \<inter> (H1 <#> H \<inter> K1) \<subseteq> H1 \<inter> K <#> H \<inter> K1"
  proof
    fix x assume x_def : "x \<in> (H \<inter> K) \<inter> (H1 <#> (H \<inter> K1))"
    from x_def have x_incl : "x \<in> H" "x \<in> K" "x \<in> (H1 <#> (H \<inter> K1))" by auto
    then obtain h1 hk1 where h1hk1_def : "h1 \<in> H1" "hk1 \<in> H \<inter> K1" "h1 \<otimes> hk1 = x"
      using assms unfolding set_mult_def by blast
    hence "hk1 \<in> H \<inter> K" using subgroup_imp_subset[OF normal_imp_subgroup[OF assms(4)]] by auto
    hence "inv hk1 \<in> H \<inter> K" using subgroup.m_inv_closed[OF subgroups_Inter_pair] assms by auto
    moreover have "h1 \<otimes> hk1 \<in> H \<inter> K" using x_incl h1hk1_def by auto
    ultimately have "h1 \<otimes> hk1 \<otimes> inv hk1 \<in> H \<inter> K"
      using subgroup.m_closed[OF subgroups_Inter_pair] assms by auto
    hence "h1 \<in> H \<inter> K" using  h1hk1_def assms subgroup_imp_subset incl_subgroup normal_imp_subgroup
      by (metis Int_iff contra_subsetD inv_solve_right m_closed)
    hence "h1 \<in> H1 \<inter> H \<inter> K" using h1hk1_def by auto
    hence "h1 \<in> H1 \<inter> K" using subgroup_imp_subset[OF normal_imp_subgroup[OF assms(2)]] by auto
    hence "h1 \<otimes> hk1 \<in> (H1\<inter>K)<#>(H\<inter>K1)"
      using h1hk1_def unfolding set_mult_def by auto
    thus " x \<in> (H1\<inter>K)<#>(H\<inter>K1)" using h1hk1_def x_def by auto
  qed
  show "H1 \<inter> K <#> H \<inter> K1 \<subseteq> H \<inter> K \<inter> (H1 <#> H \<inter> K1)"
  proof-
    have "H1 \<inter> K \<subseteq> H \<inter> K" using subgroup_imp_subset[OF normal_imp_subgroup[OF assms(2)]] by auto
    moreover have "H \<inter> K1 \<subseteq> H \<inter> K"
      using subgroup_imp_subset[OF normal_imp_subgroup[OF assms(4)]] by auto
    ultimately have "H1 \<inter> K <#> H \<inter> K1 \<subseteq> H \<inter> K" unfolding set_mult_def
      using subgroup.m_closed[OF subgroups_Inter_pair [OF assms(1)assms(3)]] by blast
    moreover have "H1 \<inter> K \<subseteq> H1" by auto
    hence "H1 \<inter> K <#> H \<inter> K1 \<subseteq> (H1 <#> H \<inter> K1)" unfolding set_mult_def by auto
    ultimately show "H1 \<inter> K <#> H \<inter> K1 \<subseteq> H \<inter> K \<inter> (H1 <#> H \<inter> K1)" by auto
  qed
qed

lemma (in group) preliminary2 :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(H1<#>(H\<inter>K1)) \<lhd> G\<lparr>carrier:=(H1<#>(H\<inter>K))\<rparr>"
proof-
  have all_inclG : "H \<subseteq> carrier G" "H1 \<subseteq> carrier G" "K \<subseteq> carrier G" "K1 \<subseteq> carrier G"
    using assms subgroup_imp_subset normal_imp_subgroup incl_subgroup apply blast+.
  have subH1:"subgroup (H1 <#> H \<inter> K) (G\<lparr>carrier := H\<rparr>)" 
    using mult_norm_sub_in_sub[OF assms(2)subgroup_incl[OF subgroups_Inter_pair[OF assms(1)assms(3)]
          assms(1)]] assms by auto
  have "Group.group (G\<lparr>carrier:=(H1<#>(H\<inter>K))\<rparr>)"
    using  subgroup_imp_group[OF incl_subgroup[OF assms(1) subH1]].
  moreover have subH2 : "subgroup (H1 <#> H \<inter> K1) (G\<lparr>carrier := H\<rparr>)"
    using mult_norm_sub_in_sub[OF assms(2) subgroup_incl[OF subgroups_Inter_pair[OF
           assms(1) incl_subgroup[OF assms(3)normal_imp_subgroup[OF assms(4)]]]]] assms by auto
  hence "(H\<inter>K1) \<subseteq> (H\<inter>K)"
    using assms subgroup_imp_subset normal_imp_subgroup monoid.cases_scheme
    by (metis inf.mono  partial_object.simps(1) partial_object.update_convs(1) subset_refl)
  hence incl:"(H1<#>(H\<inter>K1)) \<subseteq> H1<#>(H\<inter>K)" using assms subgroup_imp_subset normal_imp_subgroup
    unfolding set_mult_def by blast
  hence "subgroup (H1 <#> H \<inter> K1) (G\<lparr>carrier := (H1<#>(H\<inter>K))\<rparr>)"
    using assms subgroup_incl[OF incl_subgroup[OF assms(1)subH2]incl_subgroup[OF assms(1)
          subH1]] normal_imp_subgroup subgroup_imp_subset unfolding set_mult_def by blast
  moreover have " (\<And> x. x\<in>carrier (G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>) \<Longrightarrow>
        H1 <#> H\<inter>K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H\<inter>K\<rparr>\<^esub> x = x <#\<^bsub>G\<lparr>carrier := H1 <#> H\<inter>K\<rparr>\<^esub> (H1 <#> H\<inter>K1))"
  proof-
    fix x assume  "x \<in>carrier (G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>)"
    hence x_def : "x \<in> H1 <#> H \<inter> K" by simp
    from this obtain h1 hk where h1hk_def :"h1 \<in> H1" "hk \<in> H \<inter> K" "h1 \<otimes> hk = x"
      unfolding set_mult_def by blast
    have xH : "x \<in> H" using subgroup_imp_subset[OF subH1] using x_def by auto
    hence allG : "h1 \<in> carrier G" "hk \<in> carrier G" "x \<in> carrier G"
      using assms subgroup_imp_subset h1hk_def normal_imp_subgroup incl_subgroup apply blast+.
    hence "x <#\<^bsub>G\<lparr>carrier := H1 <#> H\<inter>K\<rparr>\<^esub> (H1 <#> H\<inter>K1) =h1 \<otimes> hk <# (H1 <#> H\<inter>K1)"
      using set_mult_same_law subgroup_imp_subset xH h1hk_def by (simp add: l_coset_def)
    also have "... = h1 <# (hk <# (H1 <#> H\<inter>K1))"
      using lcos_m_assoc[OF subgroup_imp_subset[OF incl_subgroup[OF assms(1) subH1]]allG(1)allG(2)]
      by (metis allG(1) allG(2) assms(1) incl_subgroup lcos_m_assoc subH2 subgroup_imp_subset)
    also have "... = h1 <# (hk <# H1 <#> H\<inter>K1)"
      using set_mult_assoc all_inclG allG by (simp add: l_coset_eq_set_mult inf.coboundedI1)
    also have "... = h1 <# (hk <# H1 #> \<one> <#> H\<inter>K1 #> \<one>)"
      using coset_mult_one allG all_inclG l_coset_subset_G
      by (smt inf_le2 setmult_subset_G subset_trans)
    also have "... = h1 <# (hk <# H1 #> inv hk #> hk <#> H\<inter>K1 #> inv hk #> hk)"
      using all_inclG allG coset_mult_assoc l_coset_subset_G
      by (simp add: inf.coboundedI1 setmult_subset_G)
    finally  have "x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1) =
                    h1 <# ((hk <# H1 #> inv hk) <#> (hk <# H\<inter>K1 #> inv hk) #> hk)"
      using rcos_assoc_lcos allG all_inclG
      by (smt inf_le1 inv_closed l_coset_subset_G r_coset_subset_G setmult_rcos_assoc subset_trans)
    moreover have "H \<subseteq>  normalizer G H1"
      using assms h1hk_def subgroup_imp_subset[OF normal_imp_subgroup_normalizer] by simp
    hence "\<And>g. g \<in> H \<Longrightarrow>  g \<in> {g \<in> carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) H1 = H1}"
      using all_inclG assms unfolding normalizer_def stabilizer_def by auto
    hence "\<And>g. g \<in> H \<Longrightarrow>  g <# H1 #> inv g = H1" using all_inclG by simp
    hence "(hk <# H1 #> inv hk) = H1" using h1hk_def all_inclG by simp
    moreover have "H\<inter>K \<subseteq> normalizer G (H\<inter>K1)"
      using normal_inter[OF assms(3)assms(1)assms(4)] assms subgroups_Inter_pair
            subgroup_imp_subset[OF normal_imp_subgroup_normalizer] by (simp add: inf_commute)
    hence "\<And>g. g\<in>H\<inter>K \<Longrightarrow> g\<in>{g\<in>carrier G. (\<lambda>H\<in>{H. H \<subseteq> carrier G}. g <# H #> inv g) (H\<inter>K1) = H\<inter>K1}"
      using all_inclG assms unfolding normalizer_def stabilizer_def by auto
    hence "\<And>g. g \<in> H\<inter>K \<Longrightarrow>  g <# (H\<inter>K1) #> inv g = H\<inter>K1"
      using subgroup_imp_subset[OF subgroups_Inter_pair[OF assms(1) incl_subgroup[OF
            assms(3)normal_imp_subgroup[OF assms(4)]]]] by auto
    hence "(hk <# H\<inter>K1 #> inv hk) = H\<inter>K1" using h1hk_def by simp
    ultimately have "x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1) = h1 <#(H1 <#> (H \<inter> K1)#> hk)"
      by auto
    also have "... = h1 <# H1 <#> ((H \<inter> K1)#> hk)"
      using set_mult_assoc[where ?M = "{h1}" and ?H = "H1" and ?K = "(H \<inter> K1)#> hk"] allG all_inclG
      by (simp add: l_coset_eq_set_mult inf.coboundedI2 r_coset_subset_G setmult_rcos_assoc)
    also have "... = H1 <#> ((H \<inter> K1)#> hk)"
      using coset_join3 allG incl_subgroup[OF assms(1)normal_imp_subgroup[OF assms(2)]] h1hk_def
      by auto
    finally have eq1 : "x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1) = H1 <#> (H \<inter> K1) #> hk"
      by (simp add: allG(2) all_inclG inf.coboundedI2 setmult_rcos_assoc)
    have "H1 <#> H \<inter> K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> x = H1 <#> H \<inter> K1 #> (h1 \<otimes> hk)"
      using set_mult_same_law subgroup_imp_subset xH h1hk_def by (simp add: r_coset_def)
    also have "... = H1 <#> H \<inter> K1 #> h1 #> hk"
      using coset_mult_assoc by (simp add: allG all_inclG inf.coboundedI2 setmult_subset_G)
    also have"... =  H \<inter> K1 <#> H1 #> h1 #> hk"
      using commut_normal_subgroup[OF assms(1)assms(2)subgroup_incl[OF subgroups_Inter_pair[OF
           assms(1)incl_subgroup[OF assms(3)normal_imp_subgroup[OF assms(4)]]]assms(1)]] by simp
    also have "... = H \<inter> K1 <#> H1  #> hk"
      using coset_join2[OF allG(1)incl_subgroup[OF assms(1)normal_imp_subgroup]
            h1hk_def(1)] all_inclG allG assms by (metis inf.coboundedI2 setmult_rcos_assoc)
    finally  have "H1 <#> H \<inter> K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> x =H1 <#> H \<inter> K1  #> hk"
      using commut_normal_subgroup[OF assms(1)assms(2)subgroup_incl[OF subgroups_Inter_pair[OF
           assms(1)incl_subgroup[OF assms(3)normal_imp_subgroup[OF assms(4)]]]assms(1)]] by simp
    thus " H1 <#> H \<inter> K1 #>\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> x = 
             x <#\<^bsub>G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>\<^esub> (H1 <#> H \<inter> K1)" using eq1 by simp
  qed
  ultimately show "H1 <#> H \<inter> K1 \<lhd> G\<lparr>carrier := H1 <#> H \<inter> K\<rparr>"
    unfolding normal_def normal_axioms_def by auto
qed

      
  





proposition (in group)  Zassenhaus_1 :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>" 
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(G\<lparr>carrier:= H1 <#> (H\<inter>K)\<rparr> Mod (H1<#>(H\<inter>K1)))  \<cong> (G\<lparr>carrier:= (H\<inter>K)\<rparr> Mod  ((H1\<inter>K)<#>(H\<inter>K1))) \<noteq> {}"
proof-
  define N  and N1 where "N = (H\<inter>K)" and "N1 =H1<#>(H\<inter>K1)"
  have normal_N_N1 : "subgroup N (G\<lparr>carrier:=(normalizer G N1)\<rparr>)"


    by (simp add: N1_def N_def assms distinc normal_imp_subgroup)
  have Hp:"(G\<lparr>carrier:= N<#>N1\<rparr> Mod N1)  \<cong> (G\<lparr>carrier:= N\<rparr> Mod (N\<inter>N1)) \<noteq> {}"
  by (metis N1_def N_def assms incl_subgroup inf_le1 mult_norm_sub_in_sub
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
    proof (intro set_mult_subgroup_idem[where ?H = "H\<inter>K" and ?N="H\<inter>K1",
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
    using preliminary1 assms N_def N1_def by simp 
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
      using assms
      by (simp add:Gmod4_def Gmod2_def group.iso_sym preliminary2 h_def normal.factorgroup_is_group)

    obtain f where "f\<in>Gmod1  \<cong>  Gmod3" using H1 by blast
    hence  "(compose (carrier(Gmod1)) h f) \<in> Gmod1 \<cong> Gmod2" using Egal h_def assms
      by (simp add: Gmod1_def preliminary2 group.iso_trans is_group normal.factorgroup_is_group)
    hence  "Gmod1 \<cong> Gmod2 \<noteq> {}" by auto
    thus ?thesis 
      using Gmod1_def Gmod2_def  by (simp add: inf_commute)
  qed

