theory Exact_Sequence
  imports Group Coset Solvable_Groups
    
begin

inductive exact_seq :: "'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow> bool"  where
unity:       "\<lbrakk>group_hom G1 G2 f\<rbrakk> \<Longrightarrow> exact_seq ([G2, G1], [f])" |
extension: "\<lbrakk>exact_seq ((G # K # l), (g # q)); group H ; h \<in> hom G H ; kernel G H h=image g (carrier K)\<rbrakk>
            \<Longrightarrow> exact_seq (H # G # K # l, h # g # q)"

abbreviation exact_seq_arrow ::
"('a \<Rightarrow> 'a) \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow>  'a monoid \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list"
("(3_ / \<longlongrightarrow>\<index> _)" [1000, 60])
where
"exact_seq_arrow  f t G \<equiv> (G # (fst t), f # (snd t))"

lemma truncated_seq_is_exact_seq :
  assumes "exact_seq (l, q)"
and "length l \<ge> 3"
shows "exact_seq (tl l, tl q)"
proof-
  {fix t assume "exact_seq t"
    and "length (fst t) \<ge> 3"
    hence "exact_seq (tl (fst t), tl (snd t))"
  proof (induction )
    case (unity G1 G2 f)
    then have "False" by auto
    thus ?case by auto
  next
    case (extension G l g q H h)
    then show ?case by auto
  qed}
  thus ?thesis  using assms by auto
qed

lemma exact_seq_imp_exact_hom :
   assumes "exact_seq (G1 # l,q) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
   shows "g1 ` (carrier G1) = kernel G2 G3 g2"
proof-
  {fix t assume "exact_seq t"
and "length (fst t) \<ge> 3 \<and> length (snd t) \<ge> 2"
    hence "(hd (tl (snd t))) ` (carrier (hd (tl(tl(fst t))))) =
            kernel (hd (tl(fst t))) (hd (fst t)) (hd (snd t))"
    proof (induction)
case (unity G1 G2 f)
then show ?case by auto
next
  case (extension G l g q H h)
  then show ?case by auto
qed}
  thus ?thesis using assms by fastforce
qed


lemma (in group) solvable_group_imp_solvable_subgroup :
  assumes "solvable G"
and "subgroup H G"
shows "solvable_seq G H"
proof (rule ccontr)
  {assume "solvable (G\<lparr>carrier := H\<rparr>)" 
    hence "solvable_seq G H" unfolding solvable_def apply simp
    proof (induction H rule : solvable_seq.induct)
      have "\<one>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> = \<one>\<^bsub>G\<^esub>" using assms by simp
      thus "solvable_seq G {\<one>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>}"
        by (simp add: solvable_seq.unity)
      show "\<And>K Ha. solvable_seq (G\<lparr>carrier := H\<rparr>) K \<Longrightarrow> solvable_seq G K \<Longrightarrow> K \<subset> Ha \<Longrightarrow>
            subgroup Ha (G\<lparr>carrier := H\<rparr>) \<Longrightarrow> K \<lhd> G\<lparr>carrier := H, carrier := Ha\<rparr> \<Longrightarrow>
            comm_group (G\<lparr>carrier := H, carrier := Ha\<rparr> Mod K) \<Longrightarrow> solvable_seq G Ha"
        apply simp using assms solvable_seq.extension
        by (smt group_incl_imp_subgroup monoid.cases_scheme normal_def order.trans
           partial_object.simps(1) partial_object.update_convs(1) subgroup.subset)
    qed}
  note aux_lemma = this
  assume not_solv : "\<not> solvable_seq G H"
  have  "group_hom (G\<lparr>carrier := H\<rparr>) G id"
    using canonical_inj_is_hom assms 
    by simp
  hence "\<not> solvable G" using group_hom.not_solvable aux_lemma not_solv inj_on_id
    by blast
  thus "False" using assms by auto
qed


lemma (in group) solvable_seq_forall_n :
  assumes "solvable G"
  shows "(\<exists>n. \<forall>N. N\<ge>n \<longrightarrow> (derived G ^^ N) (carrier G) = { \<one>\<^bsub>G\<^esub> })"
proof-
  have  "(\<exists>n. (derived G ^^ n) (carrier G) = { \<one> })"
    using solvable_iff_trivial_derived_seq assms by blast
  from this obtain n where n_def : "(derived G ^^ n) (carrier G) = { \<one>\<^bsub>G\<^esub> }" by auto
  have "\<And> N. N\<ge> n \<Longrightarrow> (derived G ^^ N) (carrier G) = {\<one>}"
  proof-
  have one_fix_point : "derived G {\<one>\<^bsub>G\<^esub>} = {\<one>\<^bsub>G\<^esub>}"
    using normal_imp_subgroup group.one_is_normal group.derived_incl       
          derived_def equals0D generate.one subset_singletonD
    by (metis (no_types, lifting) is_group)
  fix N assume N_def : "N \<ge> n"
  show "(derived G ^^ N) (carrier G) = { \<one>\<^bsub>G\<^esub>}" using N_def n_def
  proof (induction N)
    case 0
    then show ?case by auto
  next
    case (Suc N)
    then show ?case
    proof (cases)
      assume "n = Suc N"
      thus "(derived G ^^ Suc N) (carrier G) = {\<one>\<^bsub>G\<^esub>}"
        using n_def one_fix_point by auto
    next
      assume hyp : "n \<noteq> Suc N" "n \<le> Suc N" 
      hence "n \<le> N" by auto
      hence "(derived G ^^ N) (carrier G) = {\<one>\<^bsub>G\<^esub>}"
        using Suc.IH Suc.prems(1) n_def by blast
      thus ?case using one_fix_point by simp
    qed
  qed
qed
  thus "(\<exists>n. \<forall>N. N\<ge>n \<longrightarrow> (derived G ^^ N) (carrier G) = { \<one>\<^bsub>G\<^esub> })"
    by auto
qed

lemma exact_seq_imp_group_hom :
  assumes "exact_seq ((G # l, q)) \<longlongrightarrow>\<^bsub>g\<^esub> H"
  shows "group_hom G H g"
proof-
  {fix t assume "exact_seq t"
    hence "group_hom (hd (tl (fst t))) (hd (fst t)) (hd(snd t))" 
proof (induction)
  case (unity G1 G2 f)
  then show ?case by auto
next
  case (extension G l g q H h)
  then show ?case unfolding group_hom_def group_hom_axioms_def by auto
qed}
  note aux_lemma = this
  show ?thesis using aux_lemma[OF assms]
    by simp
qed

lemma exact_seq_solvable_imp :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "solvable G2 \<Longrightarrow> (solvable G1) \<and> (solvable G3)"
proof
  assume solv :"solvable G2"
  show "solvable G1"
  proof (rule ccontr)
    assume "\<not> solvable G1"
    hence "\<not> solvable G2"
      using group_hom.not_solvable[of G1 G2 g1] assms
            exact_seq_imp_group_hom[where ?G = "G1" and ?H = "G2" and ?g = "g1"]
            truncated_seq_is_exact_seq
      by fastforce
    thus "False" using solv by auto
  qed
  show "solvable G3"
  proof-
    have "(\<exists>n. \<forall>N \<ge> n. (derived G3 ^^ n) (carrier G3) = { \<one>\<^bsub>G3\<^esub> })"
      using group.solvable_seq_forall_n assms exact_seq_imp_group_hom
      by (smt group.subgroup_self group_hom.derived_of_img group_hom.hom_one group_hom_def
         image_empty image_insert solv subgroup_imp_subset)
    moreover have "group G3" using assms exact_seq_imp_group_hom group_hom_def
      by metis
    ultimately show "solvable G3" using group.solvable_iff_trivial_derived_seq assms
      by auto
  qed
qed

lemma exact_seq_solvable_recip :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<Longrightarrow> solvable G2"
proof-
  have All_groups : "group G1" "group G2" "group G3"
    using assms exact_seq_imp_group_hom group_hom_def truncated_seq_is_exact_seq
      apply fastforce+.
  assume solv : "solvable G1 \<and> solvable G3"
  have "\<And>n. (derived G3 ^^ n) (g2 ` (carrier G2)) = g2 ` ((derived G2 ^^ n) (carrier G2))"
    using group_hom.derived_of_img exact_seq_imp_group_hom assms
    by blast
  moreover have "subgroup (g2 ` (carrier G2)) G3"
    using All_groups assms(1) exact_seq_imp_group_hom group_hom.img_is_subgroup
    by blast
  from this obtain n where n_def : "\<forall>N\<ge>n. (derived G3 ^^ N) (g2 ` (carrier G2)) = { \<one>\<^bsub>G3\<^esub> }"
    using  assms All_groups solv group.solvable_seq_forall_n
    by (metis exact_seq_solvable_imp)
  ultimately have "g2 ` ((derived G2 ^^ n) (carrier G2)) = { \<one>\<^bsub>G3\<^esub> }"
    by auto
  moreover have "(derived G2 ^^ n) (carrier G2) \<subseteq> carrier G2" 
    using All_groups group.exp_of_derived_in_carrier
    by auto
  ultimately have "(derived G2 ^^ n) (carrier G2) \<subseteq> kernel G2 G3 g2"
    unfolding kernel_def
    by auto
  moreover have "g1 ` (carrier G1) = kernel G2 G3 g2"
    using assms truncated_seq_is_exact_seq exact_seq_imp_exact_hom by fastforce
  ultimately have "(derived G2 ^^ n) (carrier G2) \<subseteq> g1 ` (carrier G1)" by auto
  moreover have "(g1 ` (carrier G1)) \<subseteq> carrier G2"
    using All_groups assms 
    by (simp add: exact_seq_imp_exact_hom exact_seq_imp_group_hom
         group.subgroupE(1) group_hom.subgroup_kernel)
  ultimately have "\<forall>m. (derived G2 ^^(m+n)) (carrier G2) \<subseteq> (derived G2 ^^ (m)) (g1`(carrier G1))"
    using group.mono_derived[OF All_groups(2)]
    by (simp add: funpow_add)
  moreover from solv obtain m where m_def : "\<forall>N\<ge>m. (derived G1 ^^ N) (carrier G1) = {\<one>\<^bsub>G1\<^esub>}"
    using All_groups group.solvable_seq_forall_n by blast
  moreover have "\<And>k. (derived G2 ^^ (k)) (g1`(carrier G1)) = g1 ` (derived G1 ^^ k) (carrier G1)"
    using group_hom.derived_of_img[sym, of G1 G2 g1 "carrier G1"] exact_seq_imp_group_hom assms(1)
         truncated_seq_is_exact_seq
    by fastforce
  ultimately have "(derived G2 ^^ (m + n)) (carrier G2) = {\<one>\<^bsub>G2\<^esub>}"
    using All_groups group.exp_of_derived_is_subgroup image_empty image_insert group.subgroup_self
    by (smt singleton_insert_inj_eq' subgroup.one_closed subset_singleton_iff order_refl
       insert_absorb)
  thus "solvable G2"
    using group.solvable_iff_trivial_derived_seq All_groups(2)
    by blast
qed
    
proposition exact_seq_solvable_iff :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<longleftrightarrow>  solvable G2"
  using exact_seq_solvable_recip exact_seq_solvable_imp assms by blast
            
end
         