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

end