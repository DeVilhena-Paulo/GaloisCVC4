
theory More_Embedded_Algebras
  imports Subrings Generated_Groups

begin

section \<open>Definitions\<close>

locale embedded_algebra =
  K?: subfield K R + R?: ring R for K :: "'a set" and R :: "('a, 'b) ring_scheme" (structure)

definition (in ring) line_ext :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "line_ext K a E = (K #> a) <+>\<^bsub>R\<^esub> E"

fun (in ring) Span :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a set"
  where "Span K Us = foldr (line_ext K) Us { \<zero> }"

fun (in ring) linear_comb :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a"
  where
    "linear_comb (k # Ks) (u # Us) = (k \<otimes> u) \<oplus> (linear_comb Ks Us)"
  | "linear_comb Ks Us = \<zero>"

inductive (in ring) linear_ind :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where
    li_Nil [simp, intro]: "linear_ind K []"
  | li_Cons: "\<lbrakk> u \<in> carrier R; u \<notin> Span K Us; linear_ind K Us \<rbrakk> \<Longrightarrow> linear_ind K (u # Us)"

inductive (in ring) dimension :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    zero_dim [simp, intro]: "dimension 0 K { \<zero> }"
   | Suc_dim: "\<lbrakk> v \<in> carrier R; v \<notin> E; dimension n K E \<rbrakk> \<Longrightarrow> dimension (Suc n) K (line_ext K v E)"


subsubsection \<open>Syntactic Definitions\<close>

abbreviation (in ring) linear_dep ::  "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "linear_dep K U \<equiv> \<not> linear_ind K U"

definition over :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "over" 65)
  where "f over a = f a"



context ring
begin

context
  fixes K :: "'a set" assumes K: "subfield K R"
begin


subsection \<open>Basic Properties\<close>

text \<open>\<close>

lemmas subring_props [simp] =
  subringE[OF subfieldE(1)[OF K]]

lemma line_ext_mem_iff: "u \<in> line_ext K a E \<longleftrightarrow> (\<exists>k \<in> K. \<exists>v \<in> E. u = k \<otimes> a \<oplus> v)"
  unfolding line_ext_def set_add_def'[of R "K #> a" E] unfolding r_coset_def by blast

lemma line_ext_of_is_subgroup:
  assumes "subgroup E (add_monoid R)" "a \<in> carrier R"
  shows "subgroup (line_ext K a E) (add_monoid R)"
proof (rule add.subgroupI)
  show "line_ext K a E \<subseteq> carrier R"
    by (simp add: assms add.subgroupE(1) line_ext_def r_coset_subset_G set_add_closed)
next
  have "\<zero> = \<zero> \<otimes> a \<oplus> \<zero>"
    using assms(2) by simp
  hence "\<zero> \<in> line_ext K a E"
    using line_ext_mem_iff subgroup.one_closed[OF assms(1)] by auto
  thus "line_ext K a E \<noteq> {}" by auto
next
  fix u1 u2
  assume "u1 \<in> line_ext K a E" and "u2 \<in> line_ext K a E"
  then obtain k1 k2 v1 v2
    where u1: "k1 \<in> K" "v1 \<in> E" "u1 = (k1 \<otimes> a) \<oplus> v1"
      and u2: "k2 \<in> K" "v2 \<in> E" "u2 = (k2 \<otimes> a) \<oplus> v2"
      and in_carr: "k1 \<in> carrier R" "v1 \<in> carrier R" "k2 \<in> carrier R" "v2 \<in> carrier R"
    using line_ext_mem_iff by (meson add.subgroupE(1)[OF assms(1)] subring_props(1) subsetCE)

  hence "u1 \<oplus> u2 = ((k1 \<oplus> k2) \<otimes> a) \<oplus> (v1 \<oplus> v2)"
    using assms(2) by algebra
  moreover have "k1 \<oplus> k2 \<in> K" and "v1 \<oplus> v2 \<in> E"
    using add.subgroupE(4)[OF assms(1)] u1 u2 by auto
  ultimately show "u1 \<oplus> u2 \<in> line_ext K a E"
    using line_ext_mem_iff by auto

  have "\<ominus> u1 = ((\<ominus> k1) \<otimes> a) \<oplus> (\<ominus> v1)"
    using in_carr(1-2) u1(3) assms(2) by algebra
  moreover have "\<ominus> k1 \<in> K" and "\<ominus> v1 \<in> E"
    using add.subgroupE(3)[OF assms(1)] u1 by auto
  ultimately show "(\<ominus> u1) \<in> line_ext K a E"
    using line_ext_mem_iff by auto
qed

corollary Span_is_add_subgroup:
  "set Us \<subseteq> carrier R \<Longrightarrow> subgroup (Span K Us) (add_monoid R)"
  by (induct Us) (auto simp add: add.normal_invE(1)[OF add.one_is_normal] line_ext_of_is_subgroup)

lemma line_ext_smult_closed:
  assumes "\<And>k v. \<lbrakk> k \<in> K; v \<in> E \<rbrakk> \<Longrightarrow> k \<otimes> v \<in> E" and "E \<subseteq> carrier R" "a \<in> carrier R"
  shows "\<And>k u. \<lbrakk> k \<in> K; u \<in> line_ext K a E \<rbrakk> \<Longrightarrow> k \<otimes> u \<in> line_ext K a E"
proof -
  fix k u assume A: "k \<in> K" "u \<in> line_ext K a E"
  then obtain k' v'
    where u: "k' \<in> K" "v' \<in> E" "u = k' \<otimes> a \<oplus> v'"
      and in_carr: "k \<in> carrier R" "k' \<in> carrier R" "v' \<in> carrier R"
    using line_ext_mem_iff assms(2) by (meson subring_props(1) subsetCE)
  hence "k \<otimes> u = (k \<otimes> k') \<otimes> a \<oplus> (k \<otimes> v')"
    using assms(3) by algebra
  thus "k \<otimes> u \<in> line_ext K a E"
    using assms(1)[OF A(1) u(2)] line_ext_mem_iff u(1) A(1) by auto
qed

lemma Span_subgroup_props [simp]:
  assumes "set Us \<subseteq> carrier R"
  shows "Span K Us \<subseteq> carrier R"
    and "\<zero> \<in> Span K Us"
    and "\<And>v1 v2. \<lbrakk> v1 \<in> Span K Us; v2 \<in> Span K Us \<rbrakk> \<Longrightarrow> (v1 \<oplus> v2) \<in> Span K Us"
    and "\<And>v. v \<in> Span K Us \<Longrightarrow> (\<ominus> v) \<in> Span K Us"
  using add.subgroupE subgroup.one_closed[of _ "add_monoid R"]
        Span_is_add_subgroup[OF assms(1)] by auto

lemma Span_smult_closed [simp]:
  assumes "set Us \<subseteq> carrier R"
  shows "\<And>k v. \<lbrakk> k \<in> K; v \<in> Span K Us \<rbrakk> \<Longrightarrow> k \<otimes> v \<in> Span K Us"
  using assms
proof (induct Us)
  case Nil thus ?case
    using r_null subring_props(1) by (auto, blast)
next
  case Cons thus ?case
    using Span_subgroup_props(1) line_ext_smult_closed by auto
qed

lemma Span_m_inv_simprule [simp]:
  assumes "set Us \<subseteq> carrier R"
  shows "\<lbrakk> k \<in> K - { \<zero> }; a \<in> carrier R \<rbrakk> \<Longrightarrow> k \<otimes> a \<in> Span K Us \<Longrightarrow> a \<in> Span K Us"
proof -
  assume k: "k \<in> K - { \<zero> }" and a: "a \<in> carrier R" and ka: "k \<otimes> a \<in> Span K Us"
  have inv_k: "inv k \<in> K" "inv k \<otimes> k = \<one>"
    using subfield_m_inv[OF K k] by simp+
  hence "inv k \<otimes> (k \<otimes> a) \<in> Span K Us"
    using Span_smult_closed[OF assms _ ka] by simp
  thus ?thesis
    using inv_k subring_props(1)a k by (smt DiffD1 l_one m_assoc set_rev_mp)
qed

lemma mono_Span:
  assumes "set Us \<subseteq> carrier R" and "u \<in> carrier R"
  shows "Span K Us \<subseteq> Span K (u # Us)"
proof
  fix v assume v: "v \<in> Span K Us"
  hence "(\<zero> \<otimes> u) \<oplus> v \<in> Span K (u # Us)"
    using line_ext_mem_iff by auto
  thus "v \<in> Span K (u # Us)"
    using Span_subgroup_props(1)[OF assms(1)] assms(2) v
    by (auto simp del: Span.simps)
qed

lemma line_ext_of_linear_comb_set:
  assumes "u \<in> carrier R"
  shows "line_ext K u { linear_comb Ks Us | Ks. set Ks \<subseteq> K } = 
                { linear_comb Ks (u # Us) | Ks. set Ks \<subseteq> K }"
  (is "?line_extension = ?linear_combinations")
proof
  show "?line_extension \<subseteq> ?linear_combinations"
  proof
    fix v assume "v \<in> ?line_extension"
    then obtain k Ks
      where "k \<in> K" "set Ks \<subseteq> K" and "v = linear_comb (k # Ks) (u # Us)"
      using line_ext_mem_iff by auto
    thus "v \<in> ?linear_combinations"
      by (metis (mono_tags, lifting) insert_subset list.simps(15) mem_Collect_eq)
  qed
next
  show "?linear_combinations \<subseteq> ?line_extension"
  proof
    fix v assume "v \<in> ?linear_combinations"
    then obtain Ks where v: "set Ks \<subseteq> K" "v = linear_comb Ks (u # Us)"
      by auto
    thus "v \<in> ?line_extension"
    proof (cases Ks)
      case Cons thus ?thesis
        using v line_ext_mem_iff by auto
    next
      case Nil
      hence "v = \<zero>"
        using v by simp
      moreover have "linear_comb [] Us = \<zero>" by simp
      hence "\<zero> \<in> { linear_comb Ks Us | Ks. set Ks \<subseteq> K }"
        by (metis (mono_tags, lifting) local.Nil mem_Collect_eq v(1))
      hence "(\<zero> \<otimes> u) \<oplus> \<zero> \<in> ?line_extension"
        using line_ext_mem_iff subring_props(2) by blast
      hence "\<zero> \<in> ?line_extension"
        using assms by auto
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma Span_eq_linear_comb_set:
  assumes "set Us \<subseteq> carrier R" shows "Span K Us = { linear_comb Ks Us | Ks. set Ks \<subseteq> K }"
  using assms
proof (induct Us)
  case Nil thus ?case
    by (auto, metis empty_set empty_subsetI)
next
  case Cons thus ?case
    using line_ext_of_linear_comb_set by auto
qed

corollary Span_mem_iff:
  assumes "set Us \<subseteq> carrier R" and "a \<in> carrier R"
  shows "a \<in> Span K Us \<longleftrightarrow> (\<exists>k \<in> K - { \<zero> }. \<exists>Ks. set Ks \<subseteq> K \<and> linear_comb (k # Ks) (a # Us) = \<zero>)"
         (is "?in_Span \<longleftrightarrow> ?exists_linear_comb")
proof 
  assume "?in_Span"
  then obtain Ks where Ks: "set Ks \<subseteq> K" "a = linear_comb Ks Us"
    using Span_eq_linear_comb_set[OF assms(1)] by auto
  hence "((\<ominus> \<one>) \<otimes> a) \<oplus> a = linear_comb ((\<ominus> \<one>) # Ks) (a # Us)"
    by auto
  moreover have "((\<ominus> \<one>) \<otimes> a) \<oplus> a = \<zero>"
    using assms(2) l_minus l_neg by auto  
  moreover have "\<ominus> \<one> \<noteq> \<zero>"
    using subfieldE(6)[OF K] l_neg by force 
  ultimately show "?exists_linear_comb"
    using subring_props(3,5) Ks(1) by (force simp del: linear_comb.simps)
next
  assume "?exists_linear_comb"
  then obtain k Ks
    where k: "k \<in> K" "k \<noteq> \<zero>" and Ks: "set Ks \<subseteq> K" and a: "(k \<otimes> a) \<oplus> linear_comb Ks Us = \<zero>"
    by auto
  hence "linear_comb Ks Us \<in> Span K Us"
    using Span_eq_linear_comb_set[OF assms(1)] by auto
  hence "k \<otimes> a \<in> Span K Us"
    using Span_subgroup_props[OF assms(1)] k Ks a
    by (metis (no_types, lifting) assms(2) contra_subsetD m_closed minus_equality subring_props(1))
  thus "?in_Span"
    using Span_m_inv_simprule[OF assms(1) _ assms(2), of k] k by auto
qed

lemma Span_min:
  assumes "set Us \<subseteq> carrier R" and "subgroup E (add_monoid R)"
  shows "K <#> (set Us) \<subseteq> E \<Longrightarrow> Span K Us \<subseteq> E"
proof -
  assume "K <#> (set Us) \<subseteq> E" show "Span K Us \<subseteq> E"
  proof
    fix v assume "v \<in> Span K Us"
    then obtain Ks where v: "set Ks \<subseteq> K" "v = linear_comb Ks Us"
      using Span_eq_linear_comb_set[OF assms(1)] by auto
    from \<open>set Ks \<subseteq> K\<close> \<open>set Us \<subseteq> carrier R\<close> and \<open>K <#> (set Us) \<subseteq> E\<close>
    show "v \<in> E" unfolding v(2)
    proof (induct Ks Us rule: linear_comb.induct)
      case (1 k Ks u Us)
      hence "k \<in> K" and "u \<in> set (u # Us)" by auto
      hence "k \<otimes> u \<in> E" 
        using 1(4) unfolding set_mult_def by auto
      moreover have "K <#> set Us \<subseteq> E"
        using 1(4) unfolding set_mult_def by auto
      hence "linear_comb Ks Us \<in> E"
        using 1 by auto
      ultimately show ?case
        using add.subgroupE(4)[OF assms(2)] by auto 
    next
      case "2_1" thus ?case
        using subgroup.one_closed[OF assms(2)] by auto
    next
      case  "2_2" thus ?case
        using subgroup.one_closed[OF assms(2)] by auto
    qed
  qed
qed

lemma Span_eq_generate:
  assumes "set Us \<subseteq> carrier R" shows "Span K Us = generate (add_monoid R) (K <#> (set Us))"
proof (rule add.generateI)
  show "K <#> set Us \<subseteq> carrier R"
    using subring_props(1) assms unfolding set_mult_def by blast
next
  show "subgroup (Span K Us) (add_monoid R)"
    using Span_is_add_subgroup[OF assms] .
next
  show "\<And>E. \<lbrakk> subgroup E (add_monoid R); K <#> set Us \<subseteq> E \<rbrakk> \<Longrightarrow> Span K Us \<subseteq> E"
    using Span_min assms by blast
next
  show "K <#> set Us \<subseteq> Span K Us"
  using assms
  proof (induct Us)
    case Nil thus ?case
      unfolding set_mult_def by auto
  next
    case (Cons u Us)
    have "K <#> set (u # Us) = (K <#> { u }) \<union> (K <#> set Us)"
      unfolding set_mult_def by auto
    moreover have "\<And>k. k \<in> K \<Longrightarrow> k \<otimes> u \<in> Span K (u # Us)"
    proof -
      fix k assume k: "k \<in> K"
      hence "linear_comb [ k ] (u # Us) \<in> Span K (u # Us)"
        using Span_eq_linear_comb_set[OF Cons(2)] by (auto simp del: linear_comb.simps)
      moreover have "k \<in> carrier R" and "u \<in> carrier R"
        using Cons(2) k subring_props(1) by (blast, auto) 
      ultimately show "k \<otimes> u \<in> Span K (u # Us)"
        by (auto simp del: Span.simps)
    qed
    hence "K <#> { u } \<subseteq> Span K (u # Us)"
      unfolding set_mult_def by auto
    moreover have "K <#> set Us \<subseteq> Span K (u # Us)"
      using mono_Span[of Us u] Cons by (auto simp del: Span.simps)
    ultimately show ?case
      using Cons by (auto simp del: Span.simps)
  qed
qed

corollary Span_same_set:
  assumes "set Us \<subseteq> carrier R"
  shows "set Us = set Vs \<Longrightarrow> Span K Us = Span K Vs"
  using Span_eq_generate assms by auto 

lemma Span_incl: "set Us \<subseteq> carrier R \<Longrightarrow> K <#> (set Us) \<subseteq> Span K Us"
  using Span_eq_generate generate.incl[of _ _ "add_monoid R"] by auto

lemma Span_base_incl: "set Us \<subseteq> carrier R \<Longrightarrow> set Us \<subseteq> Span K Us"
proof (induct Us)
  case Nil
  then show ?case by simp
next
  case (Cons u Us)
  hence u: "u \<in> carrier R" and Us: "set Us \<subseteq> carrier R" by auto
  hence "\<one> \<otimes> u \<oplus> \<zero> \<in> line_ext K u (Span K Us)"
    using subring_props(3) Span_subgroup_props(2) line_ext_mem_iff by metis
  hence "u \<in> Span K (u # Us)"
    using u by auto
  thus ?case
    using Cons(1) u Us mono_Span by fastforce 
qed

lemma mono_Span_sublist:
  assumes "set Us \<subseteq> set Vs" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subseteq> Span K Vs"
  using add.mono_generate[OF mono_set_mult[OF _ assms(1), of K K R]
        set_mult_closed[OF subring_props(1) assms(2)]]
        Span_eq_generate[OF assms(2)] Span_eq_generate[of Us] assms by auto

corollary mono_Span_append:
  assumes "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subseteq> Span K (Us @ Vs)"
    and "Span K Us \<subseteq> Span K (Vs @ Us)"
  using mono_Span_sublist[of Us "Us @ Vs"] assms
        Span_same_set[of "Us @ Vs" "Vs @ Us"] by auto

lemma mono_Span_subset:
  assumes "set Us \<subseteq> Span K Vs" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subseteq> Span K Vs"
proof (rule Span_min[OF _ Span_is_add_subgroup[OF assms(2)]])
  show "set Us \<subseteq> carrier R"
    using Span_subgroup_props(1)[OF assms(2)] assms by auto
  show "K <#> set Us \<subseteq> Span K Vs"
    using Span_smult_closed[OF assms(2)] assms(1) unfolding set_mult_def by blast
qed

lemma Span_strict_incl:
  assumes "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subset> Span K Vs \<Longrightarrow> (\<exists>v \<in> set Vs. v \<notin> Span K Us)"
proof -
  assume "Span K Us \<subset> Span K Vs" show "\<exists>v \<in> set Vs. v \<notin> Span K Us"
  proof (rule ccontr)
    assume "\<not> (\<exists>v \<in> set Vs. v \<notin> Span K Us)"
    hence "Span K Vs \<subseteq> Span K Us"
      using mono_Span_subset[OF _ assms(1), of Vs] by auto
    from \<open>Span K Us \<subset> Span K Vs\<close> and \<open>Span K Vs \<subseteq> Span K Us\<close>
    show False by simp
  qed
qed

lemma Span_append_eq_set_add:
  assumes "set Us \<subseteq> carrier R" and "set Vs \<subseteq> carrier R"
  shows "Span K (Us @ Vs) = (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
  using assms
proof (induct Us)
  case Nil thus ?case
    using Span_subgroup_props(1)[OF Nil(2)] unfolding set_add_def' by force
next
  case (Cons u Us)
  hence in_carrier:
    "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
    by auto

  have "line_ext K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs) = (Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs)"
  proof
    show "line_ext K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs) \<subseteq> (Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs)"
    proof
      fix v assume "v \<in> line_ext K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
      then obtain k u' v'
        where v: "k \<in> K" "u' \<in> Span K Us" "v' \<in> Span K Vs" "v = k \<otimes> u \<oplus> (u' \<oplus> v')"
        using line_ext_mem_iff[of v u "Span K Us <+>\<^bsub>R\<^esub> Span K Vs"]
        unfolding set_add_def' by blast
      hence "v = (k \<otimes> u \<oplus> u') \<oplus> v'"
        using in_carrier(2-3)[THEN Span_subgroup_props(1)] in_carrier(1) subring_props(1)
        by (metis (no_types, lifting) rev_subsetD ring_simprules(7) semiring_simprules(3))
      moreover have "k \<otimes> u \<oplus> u' \<in> Span K (u # Us)"
        using line_ext_mem_iff v(1-2) by auto
      ultimately show "v \<in> Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs"
        unfolding set_add_def' using v(3) by auto
    qed
  next
    show "Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs \<subseteq> line_ext K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
    proof
      fix v assume "v \<in> Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs"
      then obtain k u' v'
        where v: "k \<in> K" "u' \<in> Span K Us" "v' \<in> Span K Vs" "v = (k \<otimes> u \<oplus> u') \<oplus> v'"
        using line_ext_mem_iff[of _ u "Span K Us"] unfolding set_add_def' by auto
      hence "v = (k \<otimes> u) \<oplus> (u' \<oplus> v')"
        using in_carrier(2-3)[THEN Span_subgroup_props(1)] in_carrier(1) subring_props(1)
        by (metis (no_types, lifting) rev_subsetD ring_simprules(7) semiring_simprules(3))
      thus "v \<in> line_ext K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
        using line_ext_mem_iff[of "(k \<otimes> u) \<oplus> (u' \<oplus> v')" u "Span K Us <+>\<^bsub>R\<^esub> Span K Vs"]
        unfolding set_add_def' using v by auto
    qed
  qed
  thus ?case
    using Cons by auto
qed


subsection \<open>Basic Properties About Linear_Comb\<close>

lemma linear_comb_in_carrier [simp, intro]:
  "\<lbrakk> set Ks \<subseteq> carrier R; set Us \<subseteq> carrier R \<rbrakk> \<Longrightarrow> linear_comb Ks Us \<in> carrier R"
  by (induct Ks Us rule: linear_comb.induct) (auto)

lemma linear_comb_r_distr:
  "\<lbrakk> set Ks \<subseteq> carrier R; set Us \<subseteq> carrier R \<rbrakk> \<Longrightarrow>
     k \<in> carrier R \<Longrightarrow> k \<otimes> (linear_comb Ks Us) = linear_comb (map ((\<otimes>) k) Ks) Us"
  by (induct Ks Us rule: linear_comb.induct) (auto simp add: m_assoc r_distr)

lemma linear_comb_eq_foldr:
  "linear_comb Ks Us = foldr (\<lambda>(k, u). \<lambda>l. (k \<otimes> u) \<oplus> l) (zip Ks Us) \<zero>"
  by (induct Ks Us rule: linear_comb.induct) (auto)

lemma linear_comb_replicate:
  "set Us \<subseteq> carrier R \<Longrightarrow> linear_comb (replicate (length Us) \<zero>) Us = \<zero>"
  by (induct Us) (auto)

lemma linear_comb_append:
  assumes "length Ks = length Us"
    and "set Ks  \<subseteq> carrier R" "set Us \<subseteq> carrier R"
    and "set Ks' \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
  shows "(linear_comb Ks Us) \<oplus> (linear_comb Ks' Vs) = linear_comb (Ks @ Ks') (Us @ Vs)"
  using assms
proof (induct Ks arbitrary: Us)
  case Nil thus ?case by auto
next
  case (Cons k Ks)
  then obtain u Us' where Us: "Us = u # Us'"
    by (metis length_Suc_conv)
  hence u: "u \<in> carrier R" and Us': "set Us' \<subseteq> carrier R"
    using Cons(4) by auto
  then show ?case
    using linear_comb_in_carrier[OF _ Us', of Ks] Cons
          linear_comb_in_carrier[OF Cons(5-6)] unfolding Us
    by (auto, simp add: add.m_assoc)
qed

lemma linear_comb_take:
  assumes "set Ks  \<subseteq> carrier R" "set Us \<subseteq> carrier R"
  shows "length Ks \<le> length Us \<Longrightarrow> linear_comb Ks Us = linear_comb Ks (take (length Ks) Us)"
    and "length Us \<le> length Ks \<Longrightarrow> linear_comb Ks Us = linear_comb (take (length Us) Ks) Us"
proof -
  assume len: "length Ks \<le> length Us"
  hence Us: "Us = (take (length Ks) Us) @ (drop (length Ks) Us)" by auto
  hence set_t: "set (take (length Ks) Us) \<subseteq> carrier R" and set_d: "set (drop (length Ks) Us) \<subseteq> carrier R"
    using assms(2) len by (metis le_sup_iff set_append)+
  hence "linear_comb Ks Us = (linear_comb Ks (take (length Ks) Us)) \<oplus> \<zero>"
    using linear_comb_append[OF _ assms(1), of "take (length Ks) Us" "[]" "drop (length Ks) Us"] len by auto
  also have " ... = linear_comb Ks (take (length Ks) Us)"
    using linear_comb_in_carrier[OF assms(1) set_t] by auto
  finally show "linear_comb Ks Us = linear_comb Ks (take (length Ks) Us)" .
next
  assume len: "length Us \<le> length Ks"
  hence Us: "Ks = (take (length Us) Ks) @ (drop (length Us) Ks)" by auto
  hence set_t: "set (take (length Us) Ks) \<subseteq> carrier R" and set_d: "set (drop (length Us) Ks) \<subseteq> carrier R"
    using assms(1) len by (metis le_sup_iff set_append)+
  hence "linear_comb Ks Us = (linear_comb (take (length Us) Ks) Us) \<oplus> \<zero>"
    using linear_comb_append[OF _ _ assms(2), of "take (length Us) Ks" "drop (length Us) Ks" "[]"] len by auto
  also have " ... = linear_comb (take (length Us) Ks) Us"
    using linear_comb_in_carrier[OF set_t assms(2)] by auto 
  finally show "linear_comb Ks Us = linear_comb (take (length Us) Ks) Us" .
qed

lemma linear_comb_normalize:
  assumes "set Ks \<subseteq> K" "set Us \<subseteq> carrier R" "a = linear_comb Ks Us" 
  shows "\<exists>Ks'. set Ks' \<subseteq> K \<and> length Ks' = length Us \<and> a = linear_comb Ks' Us"
proof (cases "length Ks \<le> length Us")
  assume "\<not> length Ks \<le> length Us"
  hence len: "length Us < length Ks" by simp
  hence "length (take (length Us) Ks) = length Us" and "set (take (length Us) Ks) \<subseteq> K"
    using assms(1) by (auto, metis contra_subsetD in_set_takeD)
  thus ?thesis
    using linear_comb_take(2)[OF _ assms(2), of Ks] assms(1,3) subring_props(1) len
    by (metis dual_order.trans nat_less_le)
next
  assume len: "length Ks \<le> length Us"
  have Ks: "set Ks \<subseteq> carrier R" and set_r: "set (replicate (length Us - length Ks) \<zero>) \<subseteq> carrier R"
    using assms subring_props(1) zero_closed by (metis dual_order.trans, auto) 
  moreover
  have set_t: "set (take (length Ks) Us) \<subseteq> carrier R"
   and set_d: "set (drop (length Ks) Us) \<subseteq> carrier R"
    using assms(2) len set_take_subset set_drop_subset by (metis dual_order.trans)+
  ultimately 
  have "linear_comb (Ks @ (replicate (length Us - length Ks) \<zero>)) Us =
       (linear_comb Ks (take (length Ks) Us)) \<oplus>
       (linear_comb (replicate (length Us - length Ks) \<zero>) (drop (length Ks) Us))"
    using linear_comb_append[OF _ Ks set_t set_r set_d] len by auto
  also have " ... = linear_comb Ks (take (length Ks) Us)"
    using linear_comb_replicate[OF set_d] linear_comb_in_carrier[OF Ks set_t] by auto
  also have " ... = a"
    using linear_comb_take(1)[OF Ks assms(2) len] assms(3) by simp
  finally have "linear_comb (Ks @ (replicate (length Us - length Ks) \<zero>)) Us = a" .
  moreover have "set (Ks @ (replicate (length Us - length Ks) \<zero>)) \<subseteq> K"
    using assms(1) subring_props(2) by auto
  moreover have "length (Ks @ (replicate (length Us - length Ks) \<zero>)) = length Us"
    using len by simp
  ultimately show ?thesis by blast
qed

lemma Span_mem_iff_length_version:
  assumes "set Us \<subseteq> carrier R"
  shows "a \<in> Span K Us \<longleftrightarrow> (\<exists>Ks. set Ks \<subseteq> K \<and> length Ks = length Us \<and> a = linear_comb Ks Us)"
  using Span_eq_linear_comb_set[OF assms] linear_comb_normalize[OF _ assms] by blast


subsection \<open>Characterisation of Linearly Independent "Sets"\<close>

lemma linear_ind_in_carrier [intro]: "linear_ind K Us \<Longrightarrow> set Us \<subseteq> carrier R"
  by (induct Us rule: linear_ind.induct) (simp_all)

lemma linear_ind_backwards [intro]:
  "linear_ind K (u # Us) \<Longrightarrow> u \<notin> Span K Us"
  "linear_ind K (u # Us) \<Longrightarrow> linear_ind K Us"
  by (cases rule: linear_ind.cases, auto)+

lemma linear_ind_distinct: "linear_ind K Us \<Longrightarrow> distinct Us"
proof (induct Us rule: list.induct)
  case Nil thus ?case by simp
next
  case Cons thus ?case
    using linear_ind_backwards[OF Cons(2)] linear_ind_in_carrier[OF Cons(2)] Span_base_incl by auto
qed

lemma linear_ind_strinct_incl:
  assumes "linear_ind K (u # Us)" shows "Span K Us \<subset> Span K (u # Us)"
proof -
  have "u \<in> Span K (u # Us)"
    using Span_base_incl[OF linear_ind_in_carrier[OF assms]] by auto
  moreover have "Span K Us \<subseteq> Span K (u # Us)"
    using mono_Span linear_ind_in_carrier[OF assms] by auto
  ultimately show ?thesis
    using linear_ind_backwards(1)[OF assms] by auto 
qed

corollary linear_ind_replacement:
  assumes "linear_ind K (u # Us)" and "linear_ind K Vs"
  shows "Span K (u # Us) \<subseteq> Span K Vs \<Longrightarrow> (\<exists>v \<in> set Vs. linear_ind K (v # Us))"
proof -
  assume "Span K (u # Us) \<subseteq> Span K Vs"
  hence "Span K Us \<subset> Span K Vs"
    using linear_ind_strinct_incl[OF assms(1)] by auto
  then obtain v where v: "v \<in> set Vs" "v \<notin> Span K Us"
    using Span_strict_incl[of Us Vs] assms[THEN linear_ind_in_carrier] by auto
  thus ?thesis
    using li_Cons[of v K Us] assms linear_ind_in_carrier[OF assms(2)] by auto
qed

lemma linear_ind_split:
  assumes "linear_ind K (Us @ Vs)"
  shows "linear_ind K Vs"
    and "linear_ind K Us"
    and "Span K Us \<inter> Span K Vs = { \<zero> }"
proof -
  from assms show "linear_ind K Vs"
    by (induct Us) (auto)
next
  from assms show "linear_ind K Us"
  proof (induct Us)
    case Nil thus ?case by simp
  next
    case (Cons u Us')
    hence u: "u \<in> carrier R" and "set Us' \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
      using linear_ind_in_carrier[of "(u # Us') @ Vs"] by auto
    hence "Span K Us' \<subseteq> Span K (Us' @ Vs)"
      using mono_Span_append(1) by simp
    thus ?case
      using linear_ind_backwards[of u "Us' @ Vs"] Cons li_Cons[OF u] by auto
  qed
next
  from assms show "Span K Us \<inter> Span K Vs = { \<zero> }"
  proof (induct Us rule: list.induct)
    case Nil thus ?case
      using Span_subgroup_props(2)[OF linear_ind_in_carrier[of Vs]] by simp 
  next
    case (Cons u Us)
    hence IH: "Span K Us \<inter> Span K Vs = {\<zero>}" by auto
    have in_carrier:
      "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R" "set (u # Us) \<subseteq> carrier R"
      using Cons(2)[THEN linear_ind_in_carrier] by auto
    hence "{ \<zero> } \<subseteq> Span K (u # Us) \<inter> Span K Vs"
      using in_carrier(3-4)[THEN Span_subgroup_props(2)] by auto

    moreover have "Span K (u # Us) \<inter> Span K Vs \<subseteq> { \<zero> }"
    proof (rule ccontr)
      assume "\<not> Span K (u # Us) \<inter> Span K Vs \<subseteq> {\<zero>}"
      hence "\<exists>a. a \<noteq> \<zero> \<and> a \<in> Span K (u # Us) \<and> a \<in> Span K Vs" by auto
      then obtain k u' v'
        where u': "u' \<in> Span K Us" "u' \<in> carrier R"
          and v': "v' \<in> Span K Vs" "v' \<in> carrier R" "v' \<noteq> \<zero>"
          and k: "k \<in> K" "(k \<otimes> u \<oplus> u') = v'"
        using line_ext_mem_iff[of _ u "Span K Us"] in_carrier(2-3)[THEN Span_subgroup_props(1)]
              subring_props(1) by force
      hence "v' = \<zero>" if "k = \<zero>"
        using in_carrier(1) that IH by auto
      hence diff_zero: "k \<noteq> \<zero>" using v'(3) by auto

      have "k \<in> carrier R"
        using subring_props(1) k(1) by blast
      hence "k \<otimes> u = (\<ominus> u') \<oplus> v'"
        using in_carrier(1) k(2) u'(2) v'(2) add.m_comm r_neg1 by auto
      hence "k \<otimes> u \<in> Span K (Us @ Vs)"
        using Span_subgroup_props(4)[OF in_carrier(2) u'(1)] v'(1) 
              Span_append_eq_set_add[OF in_carrier(2-3)] unfolding set_add_def' by blast
      hence "u \<in> Span K (Us @ Vs)"
        using Cons(2) Span_m_inv_simprule[OF _ _ in_carrier(1), of "Us @ Vs" k]
              diff_zero k(1) in_carrier(2-3) by auto
      moreover have "u \<notin> Span K (Us @ Vs)"
        using linear_ind_backwards(1)[of u "Us @ Vs"] Cons(2) by auto
      ultimately show False by simp
    qed

    ultimately show ?case by auto
  qed
qed

lemma linear_ind_append:
  assumes "linear_ind K Us" and "linear_ind K Vs" and "Span K Us \<inter> Span K Vs = { \<zero> }"
  shows "linear_ind K (Us @ Vs)"
  using assms
proof (induct Us rule: list.induct)
case Nil
  then show ?case by simp
next
  case (Cons u Us)
  hence in_carrier:
    "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R" "set (u # Us) \<subseteq> carrier R"
    using Cons(2-3)[THEN linear_ind_in_carrier] by auto
  hence "Span K Us \<subseteq> Span K (u # Us)" 
    using mono_Span by auto
  hence "Span K Us \<inter> Span K Vs = { \<zero> }"
    using Cons(4) Span_subgroup_props(2)[OF in_carrier(2)] by auto
  hence "linear_ind K (Us @ Vs)"
    using Cons by auto
  moreover have "u \<notin> Span K (Us @ Vs)"
  proof (rule ccontr)
    assume "\<not> u \<notin> Span K (Us @ Vs)"
    then obtain u' v'
      where u': "u' \<in> Span K Us" "u' \<in> carrier R"
        and v': "v' \<in> Span K Vs" "v' \<in> carrier R" and u:"u = u' \<oplus> v'"
      using Span_append_eq_set_add[OF in_carrier(2-3)] in_carrier(2-3)[THEN Span_subgroup_props(1)]
      unfolding set_add_def' by blast
    hence "u \<oplus> (\<ominus> u') = v'"
      using in_carrier(1) by algebra
    moreover have "u \<in> Span K (u # Us)" and "u' \<in> Span K (u # Us)"
      using Span_base_incl[OF in_carrier(4)] mono_Span[OF in_carrier(2,1)] u'(1)
      by (auto simp del: Span.simps)
    hence "u \<oplus> (\<ominus> u') \<in> Span K (u # Us)"
      using Span_subgroup_props(3-4)[OF in_carrier(4)] by (auto simp del: Span.simps)
    ultimately have "u \<oplus> (\<ominus> u') = \<zero>"
      using Cons(4) v'(1) by auto
    hence "u = u'"
      using Cons(4) v'(1) in_carrier(1) u'(2) \<open>u \<oplus> \<ominus> u' = v'\<close> u by auto
    thus False
      using u'(1) linear_ind_backwards(1)[OF Cons(2)] by simp
  qed
  ultimately show ?case
    using in_carrier(1) li_Cons by simp
qed

lemma linear_ind_imp_non_trivial_linear_comb:
  assumes "linear_ind K Us"
  shows "\<And>Ks. \<lbrakk> set Ks \<subseteq> K; linear_comb Ks Us = \<zero> \<rbrakk> \<Longrightarrow> fst ` set ((zip Ks Us)) \<subseteq> { \<zero> }"
  using assms
proof (induct Us rule: list.induct)
  case Nil thus ?case by simp
next
  case (Cons u Us) thus ?case
  proof (cases "Ks = []")
    assume "Ks = []" thus ?thesis by auto
  next
    assume "Ks \<noteq> []"
    then obtain k Ks' where k: "k \<in> K" and Ks': "set Ks' \<subseteq> K" and Ks: "Ks = k # Ks'"
      using Cons(2) by (metis insert_subset list.exhaust_sel list.simps(15))
    hence Us: "set Us \<subseteq> carrier R" and u: "u \<in> carrier R"
      using linear_ind_in_carrier[OF Cons(4)] by auto
    have "u \<in> Span K Us" if "k \<noteq> \<zero>"
      using that Span_mem_iff[OF Us u] Cons(3-4) Ks' k unfolding Ks by blast
    hence k_zero: "k = \<zero>"
      using linear_ind_backwards[OF Cons(4)] by blast
    hence "linear_comb Ks' Us = \<zero>"
      using linear_comb_in_carrier[OF _ Us, of Ks'] Ks' u Cons(3) subring_props(1) unfolding Ks by auto
    hence "fst ` set ((zip Ks' Us)) \<subseteq> { \<zero> }"
      using Cons(1)[OF Ks' _ linear_ind_backwards(2)[OF Cons(4)]] by simp
    thus ?thesis
      using k_zero unfolding Ks by auto
  qed
qed

lemma non_trivial_linear_comb_imp_linear_ind:
  assumes "set Us \<subseteq> carrier R"
    and "\<And>Ks. \<lbrakk> set Ks \<subseteq> K; linear_comb Ks Us = \<zero> \<rbrakk> \<Longrightarrow> fst ` set ((zip Ks Us)) \<subseteq> { \<zero> }"
  shows "linear_ind K Us"
  using assms
proof (induct Us)
  case Nil thus ?case by simp
next
  case (Cons u Us)
  hence Us: "set Us \<subseteq> carrier R" and u: "u \<in> carrier R" by auto

  have "\<And>Ks. \<lbrakk> set Ks \<subseteq> K; linear_comb Ks Us = \<zero> \<rbrakk> \<Longrightarrow> fst ` set ((zip Ks Us)) \<subseteq> { \<zero> }"
  proof -
    fix Ks assume Ks: "set Ks \<subseteq> K" and lin_c: "linear_comb Ks Us = \<zero>"
    hence "linear_comb (\<zero> # Ks) (u # Us) = \<zero>"
      using u subring_props(1) linear_comb_in_carrier[OF _ Us] by auto
    hence "fst ` set ((zip (\<zero> # Ks) (u # Us))) \<subseteq> { \<zero> }"
      using Cons(3)[of "\<zero> # Ks"] subring_props(2) Ks by auto
    thus "fst ` set ((zip Ks Us)) \<subseteq> { \<zero> }" by auto
  qed
  hence "linear_ind K Us"
    using Cons(1)[OF Us] by simp

  moreover have "u \<notin> Span K Us"
  proof (rule ccontr)
    assume "\<not> u \<notin> Span K Us"
    then obtain k Ks where k: "k \<in> K" "k \<noteq> \<zero>" and Ks: "set Ks \<subseteq> K" and u: "linear_comb (k # Ks) (u # Us) = \<zero>"
      using Span_mem_iff[OF Us u] by auto
    have "fst ` set ((zip (k # Ks) (u # Us))) \<subseteq> { \<zero> }"
      using Cons(3)[OF _ u] k(1) Ks by auto
    hence "k = \<zero>" by auto
    from \<open>k = \<zero>\<close> and \<open>k \<noteq> \<zero>\<close> show False by simp
  qed

  ultimately show ?case
    using li_Cons[OF u] by simp
qed


subsection \<open>Replacement Theorem\<close>

lemma linear_ind_rotate1_aux:
  "linear_ind K (u # Us @ Vs) \<Longrightarrow> linear_ind K ((Us @ [u]) @ Vs)"
proof -
  assume "linear_ind K (u # Us @ Vs)"
  hence li: "linear_ind K [u]" "linear_ind K Us" "linear_ind K Vs"
    and inter: "Span K [u] \<inter> Span K Us = { \<zero> }"
               "Span K (u # Us) \<inter> Span K Vs = { \<zero> }"
    using linear_ind_split[of "u # Us" Vs] linear_ind_split[of "[u]" Us] by auto
  hence "linear_ind K (Us @ [u])"
    using linear_ind_append[OF li(2,1)] by auto
  moreover have "Span K (Us @ [u]) \<inter> Span K Vs = { \<zero> }"
    using Span_same_set[of "u # Us" "Us @ [u]"] li(1-2)[THEN linear_ind_in_carrier] inter(2) by auto
  ultimately show "linear_ind K ((Us @ [u]) @ Vs)"
    using linear_ind_append[OF _ li(3), of "Us @ [u]"] by simp
qed

corollary linear_ind_rotate1:
  "linear_ind K (Us @ Vs) \<Longrightarrow> linear_ind K ((rotate1 Us) @ Vs)"
  using linear_ind_rotate1_aux by (cases Us) (auto)

corollary linear_ind_rotate:
  "linear_ind K (Us @ Vs) \<Longrightarrow> linear_ind K ((rotate n Us) @ Vs)"
  using linear_ind_rotate1 by (induct n) auto

lemma rotate_append: "rotate (length l) (l @ q) = q @ l"
  by (induct l arbitrary: q) (auto simp add: rotate1_rotate_swap)

lemma replacement_theorem:
  assumes "linear_ind K (Us' @ Us)" and "linear_ind K Vs"
    and "Span K (Us' @ Us) \<subseteq> Span K Vs"
  shows "\<exists>Vs'. set Vs' \<subseteq> set Vs \<and> length Vs' = length Us' \<and> linear_ind K (Vs' @ Us)"
  using assms
proof (induct "length Us'" arbitrary: Us' Us)
  case 0 thus ?case by auto 
next
  case (Suc n)
  then obtain u Us'' where Us'': "Us' = Us'' @ [u]"
    by (metis list.size(3) nat.simps(3) rev_exhaust)
  then obtain Vs' where Vs': "set Vs' \<subseteq> set Vs" "length Vs' = n" "linear_ind K (Vs' @ (u # Us))"
    using Suc(1)[of Us'' "u # Us"] Suc(2-5) by auto
  hence li: "linear_ind K ((u # Vs') @ Us)"
    using linear_ind_rotate[of "Vs' @ [u]" Us "length Vs'"] rotate_append[of Vs' "[u]"] by auto
  moreover have in_carrier:
    "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Us' \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
    using Suc(3-4)[THEN linear_ind_in_carrier] Us'' by auto
  moreover have "Span K ((u # Vs') @ Us) \<subseteq> Span K Vs"
  proof -
    have "set Us \<subseteq> Span K Vs" "u \<in> Span K Vs"
      using Suc(5) Span_base_incl[of "Us' @ Us"] Us'' in_carrier(2-3) by auto
    moreover have "set Vs' \<subseteq> Span K Vs"
      using Span_base_incl[OF in_carrier(4)] Vs'(1) by auto
    ultimately have "set ((u # Vs') @ Us) \<subseteq> Span K Vs" by auto
    thus ?thesis
      using mono_Span_subset[OF _ in_carrier(4)] by (simp del: Span.simps)
  qed
  ultimately obtain v where "v \<in> set Vs" "linear_ind K ((v # Vs') @ Us)"
    using linear_ind_replacement[OF _ Suc(4), of u "Vs' @ Us"] by auto
  thus ?case
    using Vs'(1-2) Suc(2)
    by (metis (mono_tags, lifting) insert_subset length_Cons list.simps(15))
qed

corollary linear_ind_length_le:
  assumes "linear_ind K Us" and "linear_ind K Vs"
  shows "set Us \<subseteq> Span K Vs \<Longrightarrow> length Us \<le> length Vs"
proof -
  assume "set Us \<subseteq> Span K Vs"
  hence "Span K Us \<subseteq> Span K Vs"
    using mono_Span_subset[OF _ linear_ind_in_carrier[OF assms(2)]] by simp
  then obtain Vs' where Vs': "set Vs' \<subseteq> set Vs" "length Vs' = length Us" "linear_ind K Vs'"
    using replacement_theorem[OF _ assms(2), of Us "[]"] assms(1) by auto
  hence "card (set Vs') \<le> card (set Vs)"
    by (simp add: card_mono)
  thus "length Us \<le> length Vs"
    using linear_ind_distinct assms(2) Vs'(2-3) by (simp add: distinct_card)
qed


subsection \<open>Dimension\<close>

definition dim :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat"
  where "dim K' E = (THE n. dimension n K' E)"

lemma exists_base:
  assumes "dimension n K E"
  shows "\<exists>Vs. set Vs \<subseteq> carrier R \<and> linear_ind K Vs \<and> length Vs = n \<and> Span K Vs = E"
    (is "\<exists>Vs. ?base K Vs E n")
  using assms
proof (induct E rule: dimension.induct)
  case zero_dim thus ?case by auto
next
  case (Suc_dim v E n K)
  then obtain Vs where Vs: "set Vs \<subseteq> carrier R" "linear_ind K Vs" "length Vs = n" "Span K Vs = E"
    by auto
  hence "?base K (v # Vs) (line_ext K v E) (Suc n)"
    using Suc_dim li_Cons by auto
  thus ?case by blast
qed

lemma dimemsion_is_inj:
  assumes "dimension n K E" and "dimension m K E"
  shows "n = m"
proof -
  { fix n m assume "dimension n K E" and "dimension m K E"
    then obtain Vs Us
      where Vs: "set Vs \<subseteq> carrier R" "linear_ind K Vs" "length Vs = n" "Span K Vs = E"
        and Us: "set Us \<subseteq> carrier R" "linear_ind K Us" "length Us = m" "Span K Us = E"
      using exists_base by meson
    hence "n \<le> m"
      using linear_ind_length_le[OF Vs(2) Us(2)] Span_base_incl[OF Vs(1)] by auto
  } note aux_lemma = this

  show ?thesis
    using aux_lemma[OF assms] aux_lemma[OF assms(2,1)] by simp
qed



end

end

end