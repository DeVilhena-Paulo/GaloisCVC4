theory Papillon
  imports Coset
begin



lemma (in group) subgroup_incl :
  assumes "subgroup I G"
    and "subgroup J G"
    and "I\<subseteq>J"
  shows "subgroup I (G\<lparr>carrier:=J\<rparr>)"using assms subgroup_inv_equality
  by (auto simp add: subgroup_def)

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





proposition (in group) weak_snd_iso_thme :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>"
  shows "(G\<lparr>carrier := H1<#>H\<rparr> Mod H1 \<cong> G\<lparr>carrier:=H\<rparr> Mod (H1\<inter>H))\<noteq> {} "
  sorry

definition normalizer ::  "[('a, 'm) monoid_scheme,'a set] \<Rightarrow> 'a set"  ("Norm\<index>_" 60)
  where " (Norm\<^bsub>G\<^esub> H) = {x\<in>(carrier G).  H  #>\<^bsub>G\<^esub>  x = x <#\<^bsub>G\<^esub> H}"

lemma (in group) normalizer_group :
  assumes "H\<subseteq>carrier G"
  shows "subgroup (Norm H) G"
  sorry
 (* show K:"(Norm H) \<subseteq> carrier G"
    using normalizer_def by fastforce
  show "\<And>x y. x \<in> Norm H \<Longrightarrow> y \<in> Norm H \<Longrightarrow> x \<otimes> y \<in> Norm H"
  proof-
    fix x y assume p: "x\<in> Norm H" "y\<in> Norm H"
    have " (x \<otimes> y)<#H = H#>(x \<otimes> y)"
    proof-
      have " H#> (x \<otimes> y) = (H#>x) #> y"
        using K p coset_mult_assoc assms by (simp add: subset_iff) 
      also have "... = (x<#H) #> y" 
        using p by (simp add: normalizer_def p(1)) 
      also have "... = x <# (H#>y)" using r_coset_def l_coset_def m_assoc assms p
*)

lemma (in group) Idem_Norm: 
  assumes "subgroup H G"
  shows "normal H (G\<lparr>carrier:= (Norm H)\<rparr>)"
  sorry
  have " H \<subseteq>  (Norm H)" using normalizer_def coset_join2 assms
    by (smt l_repr_independence lcos_mult_one mem_Collect_eq subgroup.one_closed subgroup.subset subset_iff)
  hence "H\<subseteq> carrier (G\<lparr>carrier:= (Norm H)\<rparr>)" by simp
  hence "subgroup H (G\<lparr>carrier := (Norm H)\<rparr>)" using assms subgroup_incl normalizer_group


theorem (in group) snd_iso_thme :
  assumes "subgroup H G"
    and "subgroup N G"
    and "subgroup H (G\<lparr>carrier:= (Norm H)\<rparr>)"
  shows "(G\<lparr>carrier:= H<#>N\<rparr> Mod N)  \<cong> (G\<lparr>carrier:= H\<rparr> Mod (H\<inter>N)) \<noteq> {}"
  sorry

lemma (in group) distinc :
  assumes "subgroup  H G" 
    and "H1\<lhd>G\<lparr>carrier := H\<rparr>" 
    and  "subgroup K G" 
    and "K1\<lhd>G\<lparr>carrier:=K\<rparr>"
  shows "(H\<inter>K)\<lhd> (G\<lparr>carrier:=(Norm (H1<#>(H\<inter>K1))) \<rparr>)"
  sorry


lemma (in group) mult_norm_subgroup :
  assumes "normal N G"
  assumes "subgroup H G"
  shows "subgroup (N<#>H) G"
  sorry

lemma (in group) mult_norm_subgroup2 :
  assumes "normal N (G\<lparr>carrier:=K\<rparr>)"
  assumes "subgroup H (G\<lparr>carrier:=K\<rparr>)"
  assumes "subgroup K G"
  shows  "subgroup (N<#>H) (G\<lparr>carrier:=K\<rparr>)"
  sorry




lemma (in group) commut_normal :
  assumes "subgroup H G"
    and "N\<lhd>G"
  shows "H<#>N = N<#>H"
  sorry

lemma (in group) commut_normal_subgroup :
  assumes "subgroup H G"
    and "N\<lhd>(G\<lparr>carrier:=H\<rparr>)"
    and "subgroup K (G\<lparr>carrier:=H\<rparr>)"
  shows "K<#>N = N<#>K"
  sorry

lemma (in group) set_mult_assoc : "H1 <#> (H2<#>H3) = (H1<#>H2) <#> H3"
  sorry

lemma (in group) idem_set_mult :
  assumes "subgroup H G"
  shows "(carrier G)<#>H = carrier G"
  sorry


lemma (in group) set_mult_idem :
  assumes "subgroup H G"
and "K1\<subseteq> H"
and "K2\<subseteq>H"
shows "K1<#>\<^bsub>(G\<lparr>carrier:=H\<rparr>)\<^esub>K2 = K1<#>K2"
proof 
  show "K1 <#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> K2 \<subseteq> K1 <#> K2"
  proof
    fix h assume Hyph : "h\<in>K1<#>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>K2"
    then obtain k1 k2 where Hyp : "k1\<in>K1 \<and> k2\<in>K2 \<and> k1\<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>k2 = h" unfolding set_mult_def by blast
    hence k1H: "k1\<in>H" using assms by blast
    have  k2H: "k2\<in>H" using Hyp assms by blast
    have EGAL : "k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2 = k1 \<otimes>\<^bsub>G\<^esub> k2" using k1H k2H by simp
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
    using group.idem_set_mult assms GH_def GHgroup by blast
  hence "H<#>\<^bsub>G\<lparr>carrier:=H\<rparr>\<^esub>N = H" using GH_def by auto
  thus "H<#>N = H" using EGAL by auto
qed





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
          thus "H1K \<subseteq>H\<inter>K " 
            using H1K_def calculation by auto
        qed
        thus "subgroup H1K GHK" using GHK_def by simp

  next
        show "\<forall>x\<in>carrier GHK. \<forall>h\<in>H1K. x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x\<in> H1K"
        proof
          have invHK: "\<lbrakk>y\<in>HK\<rbrakk> \<Longrightarrow> inv\<^bsub>GHK\<^esub> y = inv\<^bsub>GH\<^esub> y"
            using subgroup_inv_equality assms HK_def GH_def GHK_def subgroups_Inter_pair by simp
          have multHK : "\<lbrakk>x\<in>HK;y\<in>HK\<rbrakk> \<Longrightarrow>  x \<otimes>\<^bsub>(G\<lparr>carrier:=HK\<rparr>)\<^esub> y =  x \<otimes> y"
            using HK_def by simp
          fix x assume p: "x\<in>carrier GHK"
            show "\<forall>h\<in>H1K. x \<otimes>\<^bsub>GHK\<^esub> h \<otimes>\<^bsub>GHK\<^esub> inv\<^bsub>GHK\<^esub> x \<in> H1K"
            proof
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
       qed
    qed
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
  have   "normal N (G\<lparr>carrier:=(Norm N1)\<rparr>)"
    by (simp add: N1_def N_def assms distinc)
  have Hp:"(G\<lparr>carrier:= N<#>N1\<rparr> Mod N1)  \<cong> (G\<lparr>carrier:= N\<rparr> Mod (N\<inter>N1)) \<noteq> {}"
  proof (intro snd_iso_thme)
    show  "subgroup N G"
      by (simp add: N_def assms subgroups_Inter_pair)
  next
    show "subgroup N1 G"
    proof-
      have "subgroup (H\<inter>K1) (G\<lparr>carrier:=H\<rparr>)"
      proof (intro subgroup_incl)
        have "subgroup  K1 (G\<lparr>carrier:=K\<rparr>)"
          by (simp add: assms(4) normal_imp_subgroup)
        hence "subgroup (K1) G"
          using assms(3) incl_subgroup by blast
        thus "subgroup (H\<inter>K1) G" using subgroups_Inter_pair assms(1) by blast
      next
        show "subgroup H G" using assms(1) by auto
      next
        show "H \<inter> K1 \<subseteq> H" by blast
      qed
      hence "subgroup (H1<#>(H\<inter>K1))  (G\<lparr>carrier:=H\<rparr>)" 
        using mult_norm_subgroup2 assms(1) assms(2) by blast
      thus "subgroup N1 G"
        using N1_def assms(1) incl_subgroup by blast
    qed
    show "subgroup N (G\<lparr>carrier := Norm N\<rparr>)" using  Idem_Norm normal_imp_subgroup
      by (simp add: normal_imp_subgroup N_def assms subgroups_Inter_pair)
  qed
  have H_simp: "N<#>N1 = H1<#> (H\<inter>K)"
  proof-
    have "N<#>N1=  (H\<inter>K)<#> (H1<#>(H\<inter>K1))" by (auto simp add: N_def N1_def)
    also have "... = ((H\<inter>K)<#>H1) <#>(H\<inter>K1)"
      using set_mult_assoc by simp       
    also have "... = (H1<#>(H\<inter>K))<#>(H\<inter>K1)" 
      using commut_normal_subgroup assms subgroup_incl subgroups_Inter_pair by auto
    also have "... =  H1 <#> ((H\<inter>K)<#>(H\<inter>K1))"
      using set_mult_assoc by simp 
    also have " ((H\<inter>K)<#>(H\<inter>K1)) = (H\<inter>K)"
    proof (intro idem_set_mult_subgroup[where ?H = "H\<inter>K" and ?N="H\<inter>K1"])
      thm idem_set_mult_subgroup
      show "subgroup (H \<inter> K) G"
        by (simp add : assms subgroups_Inter_pair)
    next
      show "subgroup (H \<inter> K1) (G\<lparr>carrier := H \<inter> K\<rparr>)" 
      proof(intro subgroup_incl)
        have  "subgroup  K1 G" 
          using assms  normal_imp_subgroup incl_subgroup by auto
        thus "subgroup (H \<inter> K1) G" using subgroups_Inter_pair assms 
          by auto
      next
        show "subgroup (H \<inter> K) G" using assms subgroups_Inter_pair 
          by auto
      next
        have "K1 \<subseteq> carrier(G\<lparr>carrier:=K\<rparr>)"
          using normal_imp_subgroup subgroup_def assms by metis
        also have "... \<subseteq> K" by simp
        finally have "K1 \<subseteq> K" by simp
        thus "H \<inter> K1 \<subseteq> H \<inter> K" by auto
      qed
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

