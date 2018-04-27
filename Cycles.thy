theory Cycles
  imports "HOL-Library.Permutations"
    
begin

section \<open>Cycles\<close>

inductive cycle :: "'a set \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
  transp: "i \<noteq> j \<Longrightarrow> cycle {i, j} [(i, j)]"
| dcycle: "cycle I (Cons (j, k) cs) \<Longrightarrow> i \<notin> I \<Longrightarrow>
           cycle (insert i I) (Cons (i, j) (Cons (j, k) cs))"

fun cycle_of_list :: "('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "cycle_of_list [] = id"
| "cycle_of_list (Cons (i, j) cs) = Fun.swap i j id \<circ> (cycle_of_list cs)"

definition
  supp :: "('a \<times> 'a) list \<Rightarrow> 'a list"
  where "supp cs = Cons (fst (hd cs)) (map snd cs)"


subsection \<open>Properties About the Support of a Cycle\<close>

lemma finite_supp: "cycle I cs \<Longrightarrow> finite I"
  apply (induction rule: cycle.induct) by auto

lemma supp_eq_set: "cycle I cs \<Longrightarrow> set (supp cs) = I"
  unfolding supp_def apply (induction rule: cycle.induct) by auto

lemma supp_length: "length (supp cs) = length cs + 1"
  unfolding supp_def apply (induction cs) by auto

lemma supp_length_eq_card: "cycle I cs \<Longrightarrow> length (supp cs) = card I"
proof (induction rule: cycle.induct)
  case (transp i j) thus ?case unfolding supp_def by simp
next
  case (dcycle I j k cs i)
  hence "j \<in> I" using supp_eq_set[OF dcycle(1)]
    by (metis hd_in_set list.sel(1) list.simps(3) prod.sel(1) supp_def)
  have "length (supp ((i, j) # (j, k) # cs)) = length (i # (supp ((j, k) # cs)))"
    by (simp add: supp_length)
  also have " ... = 1 + length (supp ((j, k) # cs))" by simp
  also have " ... = 1 + card I"
    by (simp add: dcycle.IH)
  also have " ... = card (insert i I)"
    using dcycle.hyps(2) finite_supp[OF dcycle.hyps(1)] by auto
  finally show ?case .
qed

lemma supp_redef: "cycle I cs \<Longrightarrow> supp cs = (map fst cs) @ [snd (last cs)]"
  unfolding supp_def apply (induction rule: cycle.induct) by auto

lemma supp_elems: "cycle I cs \<Longrightarrow> i < length cs \<Longrightarrow> (supp cs) ! (i + 1)  = snd (cs ! i)"
  unfolding supp_def by simp


subsection\<open>Cycle as a Permutation\<close>

lemma id_outside_supp: "cycle I cs \<Longrightarrow> x \<notin> I \<Longrightarrow> (cycle_of_list cs) x = x"
proof (induction rule: cycle.induct)
  case (transp i j) thus ?case by simp
next
  case (dcycle I j k cs i)
  have "j \<in> I"
    using dcycle.hyps(1) supp_eq_set unfolding supp_def by force
  moreover have "cycle_of_list ((i, j) # (j, k) # cs) x = (Fun.swap i j id) x"
    using dcycle.IH dcycle.prems by auto
  ultimately show ?case
    by (metis dcycle.prems insertCI swap_id_eq) 
qed

lemma permutation_of_list: "permutation (cycle_of_list cs)"
proof (induction rule: cycle_of_list.induct)
  case 1 thus ?case by simp
next
  case (2 i j cs) thus ?case
    by (metis cycle_of_list.simps(2) permutation_compose permutation_swap_id) 
qed

lemma cycle_permutes: "cycle I cs \<Longrightarrow> (cycle_of_list cs) permutes I"
  using permutation_of_list[of cs] id_outside_supp
  by (metis Diff_iff permutation_permutes permutes_superset)


subsection\<open>Chained Elements\<close>

lemma fst_excluded: "cycle I cs \<Longrightarrow> I - {fst (hd cs)} = set (map snd cs)"
proof (induction rule: cycle.induct)
  case (transp i j)
  then show ?case by simp 
next
  case (dcycle I j k cs i) thus ?case using supp_eq_set unfolding supp_def
    by (smt Diff_insert_absorb fst_conv list.sel(1)
        list.simps(15) list.simps(9) snd_conv)
qed

lemma cycle_non_empty1: "cycle I cs \<Longrightarrow> cs \<noteq> []"
  apply (induction rule: cycle.induct) by auto

lemma cycle_non_empty2: "cycle I cs \<Longrightarrow> length (supp cs) \<ge> Suc 1"
  using cycle_non_empty1 supp_length
  by (simp add: cycle_non_empty1 supp_length Suc_leI)

lemma closed_chain1: "cycle I cs \<Longrightarrow> (cycle_of_list cs) (snd (last cs)) = fst (hd cs)"
  apply (induction rule: cycle.induct) by auto

lemma closed_chain2: "cycle I cs \<Longrightarrow> (cycle_of_list cs) (last (supp cs)) = (hd (supp cs))"
  by (simp add: closed_chain1 cycle_non_empty1 list.map_sel(1) supp_redef)

lemma chain_links1: "cycle I cs \<Longrightarrow> map (cycle_of_list cs) (map fst cs) = (map snd cs)"
proof (induction rule: cycle.induct)
  case (transp i j) thus ?case by simp
next
  case (dcycle I j k cs i)
  have i_excl:"i \<notin> set (map snd ((j, k) # cs))"
    using dcycle.hyps(1) dcycle.hyps(2) supp_eq_set unfolding supp_def by force
  have j_excl:"j \<notin> set (map snd ((j, k) # cs))"
    using fst_excluded[OF dcycle(1)] by auto
  have
    "map (cycle_of_list ((i, j) # (j, k) # cs)) (map fst ((j, k) # cs)) =
     map (Fun.swap i j id) (map (cycle_of_list ((j, k) # cs)) (map fst ((j, k) # cs)))" by simp
  also have " ... = map (Fun.swap i j id) (map snd ((j, k) # cs))"
    using dcycle.IH by auto
  also have " ... = (map snd ((j, k) # cs))"
    using i_excl j_excl by (smt list.map_id map_eq_conv swap_apply(3))
  finally have
    "map (cycle_of_list ((i, j) # (j, k) # cs)) (map fst ((j, k) # cs)) = (map snd ((j, k) # cs))" .
  moreover have "(cycle_of_list ((i, j) # (j, k) # cs)) i = j"
    using id_outside_supp[OF dcycle(1)] by (simp add: dcycle.hyps(2))
  ultimately show ?case by simp
qed

lemma chain_links2:
  assumes "cycle I cs"
    and "(i, j) \<in> set cs"
  shows "(cycle_of_list cs) i = j"
  using chain_links1[OF assms(1)] assms(2) by auto

lemma chain_links3:
  assumes "cycle I cs" "i < length cs"
  shows "(cycle_of_list cs) ((supp cs) ! i) = ((supp cs) ! (i + 1))"
  using chain_links1[OF assms(1)] supp_elems[OF assms] supp_redef[OF assms(1)]
  by (metis assms(2) length_map nth_append nth_map)


subsection\<open>Rotation of its Support List\<close>

lemma cyclic_rotation1:
  assumes "cycle I cs"
  shows "map (cycle_of_list cs) (supp cs) = rotate1 (supp cs)"
proof -
  have "map (cycle_of_list cs) (supp cs) = tl (supp cs) @ [hd (supp cs)]"
    using chain_links3[OF assms] supp_length[of cs] closed_chain1 closed_chain2 supp_def supp_redef
    by (smt assms chain_links1 list.sel(1) list.sel(3) list.simps(8) list.simps(9) map_append)
  thus ?thesis by (simp add: supp_def) 
qed

lemma cyclic_rotation2:
  assumes "cycle I cs"
  shows "map ((cycle_of_list cs) ^^ n) (supp cs) = rotate n (supp cs)"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "map (cycle_of_list cs ^^ Suc n) (supp cs) =
        map (cycle_of_list cs) (map (cycle_of_list cs ^^ n) (supp cs))" by simp
  also have "... = map (cycle_of_list cs) (rotate n (supp cs))"
    by (simp add: Suc.IH)
  also have " ... = (rotate (Suc n) (supp cs))" using cyclic_rotation1[OF assms]
    by (metis rotate1_rotate_swap rotate_Suc rotate_map)
  finally show ?case .
qed

lemma exp_id_outside_supp:
  assumes "cycle I cs" "x \<notin> I"
  shows "((cycle_of_list cs) ^^ n) x = x"
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n) thus ?case using id_outside_supp[OF assms] by simp
  qed

lemma cyclic_id_root:
  assumes "cycle I cs"
  shows "(cycle_of_list cs) ^^ (card I) = id"
proof -
  have "\<And>x. x \<notin> I \<Longrightarrow> ((cycle_of_list cs) ^^ (card I)) x = x"
    using exp_id_outside_supp[OF assms] by simp

  moreover have "\<And>x. x \<in> I \<Longrightarrow> ((cycle_of_list cs) ^^ (length (supp cs))) x = x"
  proof -
    fix x assume "x \<in> I" hence x: "x \<in> set (supp cs)"
      using supp_eq_set[OF assms] by simp
    have "rotate (length (supp cs)) (supp cs) = (supp cs)" by auto
    hence "map ((cycle_of_list cs) ^^ (length (supp cs))) (supp cs) = (supp cs)"
      using cyclic_rotation2[OF assms] by simp
    thus "((cycle_of_list cs) ^^ (length (supp cs))) x = x"
      using x map_eq_conv by fastforce 
  qed
  hence "\<And>x. x \<in> I \<Longrightarrow> ((cycle_of_list cs) ^^ (card I)) x = x"
    using supp_length_eq_card[OF assms] by simp

  ultimately show ?thesis
    by (meson eq_id_iff)
qed

lemma disjoint_cycles_commute_aux:
  assumes "cycle I \<sigma>1" "cycle J \<sigma>2"
    and "I \<inter> J = {}" "x \<in> I" "x \<notin> J"
  shows "((cycle_of_list \<sigma>1) \<circ> (cycle_of_list \<sigma>2)) x = ((cycle_of_list \<sigma>2) \<circ> (cycle_of_list \<sigma>1)) x"
proof -
  have "((cycle_of_list \<sigma>1) \<circ> (cycle_of_list \<sigma>2)) x = (cycle_of_list \<sigma>1) x"
    using id_outside_supp[OF assms(2) assms(5)] by simp
  moreover have "(cycle_of_list \<sigma>1) x \<notin> J"
    using assms permutes_in_image[OF cycle_permutes[OF assms(1)]] by fastforce
  hence "((cycle_of_list \<sigma>2) \<circ> (cycle_of_list \<sigma>1)) x = (cycle_of_list \<sigma>1) x"
    using id_outside_supp[OF assms(2)] by simp
  ultimately show ?thesis by simp
qed

lemma disjoint_cycles_commute:
  assumes "cycle I \<sigma>1" "cycle J \<sigma>2"
    and "I \<inter> J = {}"
  shows "(cycle_of_list \<sigma>1) \<circ> (cycle_of_list \<sigma>2) = (cycle_of_list \<sigma>2) \<circ> (cycle_of_list \<sigma>1)"
proof -
  let ?\<sigma>12 = "\<lambda>x. ((cycle_of_list \<sigma>1) \<circ> (cycle_of_list \<sigma>2)) x"
  let ?\<sigma>21 = "\<lambda>x. ((cycle_of_list \<sigma>2) \<circ> (cycle_of_list \<sigma>1)) x"

  show ?thesis
  proof
    fix x have "x \<in> I \<union> J \<or> x \<notin> I \<union> J" by blast
    from this show "?\<sigma>12 x = ?\<sigma>21 x"
    proof 
      assume "x \<in> I \<union> J" hence "(x \<in> I \<and> x \<notin> J) \<or> (x \<notin> I \<and> x \<in> J)" using assms(3) by blast
      from this show "?\<sigma>12 x = ?\<sigma>21 x"
      proof
        assume "x \<in> I \<and> x \<notin> J" thus ?thesis
          using disjoint_cycles_commute_aux[OF assms(1-3)] by simp
      next
        assume "x \<notin> I \<and> x \<in> J" thus ?thesis
          using assms disjoint_cycles_commute_aux inf_commute by metis
      qed
    next
      assume "x \<notin> I \<union> J" thus ?thesis using id_outside_supp assms(1-2)
        by (metis UnCI comp_apply)
    qed
  qed 
qed

lemma conjugation_of_cycle1:
  assumes "cycle I cs" "bij p"
  shows "cycle (p ` I) (map (\<lambda>(x, y). (p x, p y)) cs)" using assms
proof (induction rule: cycle.induct)
  case (transp i j)
  hence "p i \<noteq> p j" by (meson UNIV_I bij_betw_def inj_on_def) 
  thus ?case by (simp add: cycle.transp)  
next
  case (dcycle I j k cs i)
  hence "p i \<notin> (p ` I)" by (simp add: bij_is_inj inj_image_mem_iff)
  thus ?case using assms(2) cycle.simps dcycle.IH by fastforce 
qed

lemma conjugation_of_transp:
  assumes "bij p"
  shows "p \<circ> (Fun.swap a b id) \<circ> (inv p) = Fun.swap (p a) (p b) id"
  using surj_f_inv_f[OF bij_is_surj[OF \<open>bij p\<close>]] fun_eq_iff Fun.swap_def bij_inv_eq_iff[OF \<open>bij p\<close>]
  by (smt assms bij_imp_bij_inv bij_is_surj bij_swap_comp comp_swap inv_inv_eq o_assoc surj_iff)

lemma conjugation_of_cycle2:
  assumes "cycle I cs" "bij p"
  shows "p \<circ> (cycle_of_list cs) \<circ> (inv p) = cycle_of_list (map (\<lambda>(x, y). (p x, p y)) cs)" using assms
proof (induction rule: cycle.induct)
  case (transp i j) thus ?case
    using conjugation_of_transp[OF assms(2), of i j] by (simp add: comp_swap) 
next
  case (dcycle I j k cs i)
  have "p \<circ> cycle_of_list ((i, j) # (j, k) # cs) \<circ> inv p =
        p \<circ> ((Fun.swap i j id) \<circ> (cycle_of_list ((j, k) # cs))) \<circ> inv p" by simp
  also have " ... = (p \<circ> (Fun.swap i j id) \<circ> inv p) \<circ> (p \<circ> (cycle_of_list ((j, k) # cs))) \<circ> inv p"
    by (simp add: bij_is_inj dcycle.prems o_assoc)
  also have " ... = (Fun.swap (p i) (p j) id) \<circ> (p \<circ> (cycle_of_list ((j, k) # cs)) \<circ> inv p)"
    by (simp add: conjugation_of_transp dcycle.prems o_assoc)
  also have " ... = (Fun.swap (p i) (p j) id) \<circ> cycle_of_list (map (\<lambda>(x, y). (p x, p y)) ((j, k) # cs))"
    using assms(2) dcycle.IH by fastforce
  also have " ... = cycle_of_list (map (\<lambda>(x, y). (p x, p y)) ((i, j) # (j, k) # cs))"
    by simp
  finally show ?case . 
qed


subsection\<open>Cycles from Permutations\<close>

text\<open>Some important properties of permutations before defining how to extract its cycles\<close>

lemma exp_of_permutation1:
  assumes "p permutes S"
  shows "(p ^^ n) permutes S" using assms
proof (induction n)
  case 0 thus ?case by (simp add: permutes_def) 
next
  case (Suc n) thus ?case by (metis funpow_Suc_right permutes_compose) 
qed

lemma exp_of_permutation2:
  assumes "p permutes S"
    and "i < j" "(p ^^ j) = (p ^^ i)"
  shows "(p ^^ (j - i)) = id" using assms
proof -
  have "(p ^^ i) \<circ> (p ^^ (j - i)) = (p ^^ j)"
    by (metis add_diff_inverse_nat assms(2) funpow_add le_eq_less_or_eq not_le)
  also have " ... = (p ^^ i)" using assms(3) by simp
  finally have "(p ^^ i) \<circ> (p ^^ (j - i)) = (p ^^ i)" .
  moreover have "bij (p ^^ i)" using exp_of_permutation1[OF assms(1)]
    using permutes_bij by auto
  ultimately show ?thesis
    by (metis (no_types, lifting) bij_is_inj comp_assoc fun.map_id inv_o_cancel)
qed

lemma exp_of_permutation3:
  assumes "p permutes S" "finite S"
  shows "\<exists>n. (p ^^ n) = id \<and> n > 0"
proof (rule ccontr)
  assume "\<nexists>n. (p ^^ n) = id \<and> 0 < n"
  hence S: "\<And>n. n > 0 \<Longrightarrow> (p ^^ n) \<noteq> id" by auto
  hence "\<And>i j. \<lbrakk> i \<ge> 0; j \<ge> 0 \<rbrakk> \<Longrightarrow> i \<noteq> j \<Longrightarrow> (p ^^ i) \<noteq> (p ^^ j)"
  proof -
    fix i :: "nat" and j :: "nat" assume "i \<ge> 0" "j \<ge> 0" and Ineq: "i \<noteq> j"
    show "(p ^^ i) \<noteq> (p ^^ j)"
    proof (rule ccontr)
      assume "\<not> (p ^^ i) \<noteq> (p ^^ j)" hence Eq: "(p ^^ i) = (p ^^ j)" by simp
      have "(p ^^ (j - i)) = id" if "j > i"
        using Eq exp_of_permutation2[OF assms(1) that] by simp
      moreover have "(p ^^ (i - j)) = id" if "i > j"
        using Eq exp_of_permutation2[OF assms(1) that] by simp
      ultimately show False using Ineq S
        by (meson le_eq_less_or_eq not_le zero_less_diff)
    qed
  qed
  hence "bij_betw (\<lambda>i. (p ^^ i)) {i :: nat . i \<ge> 0} {(p ^^ i) | i :: nat . i \<ge> 0}"
    unfolding bij_betw_def inj_on_def by blast
  hence "infinite {(p ^^ i) | i :: nat . i \<ge> 0}"
    using bij_betw_finite by auto
  moreover have "{(p ^^ i) | i :: nat . i \<ge> 0} \<subseteq> {\<pi>. \<pi> permutes S}"
    using exp_of_permutation1[OF assms(1)] by blast
  hence "finite {(p ^^ i) | i :: nat . i \<ge> 0}"
    by (simp add: assms(2) finite_permutations finite_subset)
  ultimately show False ..
qed

fun extract_cycle :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list"
  where "extract_cycle p np x =
           (if np x = x then [] else Cons (np x, p (np x)) (extract_cycle p (np \<circ> p) x))"

fun cycle_decomp :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)"


end