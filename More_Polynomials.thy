(*  Title:      HOL/Algebra/More_Polynomials.thy
    Author:     Paulo Emílio de Vilhena
*)

theory More_Polynomials
  imports Ring (* Ring_Divisibility *) Embedded_Algebras

begin

section \<open>Polynomials\<close>

subsection \<open>Definitions\<close>

abbreviation lead_coeff :: "'a list \<Rightarrow> 'a"
  where "lead_coeff \<equiv> hd"

abbreviation degree :: "'a list \<Rightarrow> nat"
  where "degree p \<equiv> length p - 1"

definition polynomial :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" ("polynomial\<index>")
  where "polynomial\<^bsub>R\<^esub> K p \<longleftrightarrow> p = [] \<or> (set p \<subseteq> K \<and> lead_coeff p \<noteq> \<zero>\<^bsub>R\<^esub>)"

definition (in ring) monon :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"
  where "monon a n = a # (replicate n \<zero>\<^bsub>R\<^esub>)"

fun (in ring) eval :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a"
  where
    "eval [] = (\<lambda>_. \<zero>)"
  | "eval p = (\<lambda>x. ((lead_coeff p) \<otimes> (x [^] (degree p))) \<oplus> (eval (tl p) x))"

fun (in ring) coeff :: "'a list \<Rightarrow> nat \<Rightarrow> 'a"
  where
    "coeff [] = (\<lambda>_. \<zero>)"
  | "coeff p = (\<lambda>i. if i = degree p then lead_coeff p else (coeff (tl p)) i)"

fun (in ring) normalize :: "'a list \<Rightarrow> 'a list"
  where
    "normalize [] = []"
  | "normalize p = (if lead_coeff p \<noteq> \<zero> then p else normalize (tl p))"

fun (in ring) poly_add :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "poly_add p1 p2 =
           (if length p1 \<ge> length p2
            then normalize (map2 (\<oplus>) p1 ((replicate (length p1 - length p2) \<zero>) @ p2))
            else poly_add p2 p1)"

fun (in ring) poly_mult :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "poly_mult [] p2 = []"
  | "poly_mult p1 p2 =
       poly_add ((map (\<lambda>a. lead_coeff p1 \<otimes> a) p2) @ (replicate (degree p1) \<zero>)) (poly_mult (tl p1) p2)"

fun (in ring) dense_repr :: "'a list \<Rightarrow> ('a \<times> nat) list"
  where
    "dense_repr [] = []"
  | "dense_repr p = (if lead_coeff p \<noteq> \<zero>
                     then (lead_coeff p, degree p) # (dense_repr (tl p))
                     else (dense_repr (tl p)))"

fun (in ring) of_dense :: "('a \<times> nat) list \<Rightarrow> 'a list"
  where "of_dense dl = foldr (\<lambda>(a, n) l. poly_add (monon a n) l) dl []"



subsection \<open>Basic Properties\<close>

context ring
begin

lemma polynomialI [intro]: "\<lbrakk> set p \<subseteq> K; lead_coeff p \<noteq> \<zero> \<rbrakk> \<Longrightarrow> polynomial K p"
  unfolding polynomial_def by auto

lemma polynomial_incl: "polynomial K p \<Longrightarrow> set p \<subseteq> K"
  unfolding polynomial_def by auto

lemma monon_in_carrier [intro]: "a \<in> carrier R \<Longrightarrow> set (monon a n) \<subseteq> carrier R"
  unfolding monon_def by auto

lemma lead_coeff_not_zero: "polynomial K (a # p) \<Longrightarrow> a \<in> K - { \<zero> }"
  unfolding polynomial_def by simp

lemma zero_is_polynomial [intro]: "polynomial K []"
  unfolding polynomial_def by simp

lemma const_is_polynomial [intro]: "a \<in> K - { \<zero> } \<Longrightarrow> polynomial K [ a ]"
  unfolding polynomial_def by auto

lemma normalize_gives_polynomial: "set p \<subseteq> K \<Longrightarrow> polynomial K (normalize p)"
  by (induction p) (auto simp add: polynomial_def)

lemma normalize_in_carrier: "set p \<subseteq> carrier R \<Longrightarrow> set (normalize p) \<subseteq> carrier R"
  by (induction p) (auto)

lemma normalize_idem: "polynomial K p \<Longrightarrow> normalize p = p"
  unfolding polynomial_def by (cases p) (auto)

lemma normalize_length_le: "length (normalize p) \<le> length p"
  by (induction p) (auto)

lemma eval_in_carrier: "\<lbrakk> set p \<subseteq> carrier R; x \<in> carrier R \<rbrakk> \<Longrightarrow> (eval p) x \<in> carrier R"
  by (induction p) (auto)

lemma coeff_in_carrier [simp]: "set p \<subseteq> carrier R \<Longrightarrow> (coeff p) i \<in> carrier R"
  by (induction p) (auto)

lemma lead_coeff_simp [simp]: "p \<noteq> [] \<Longrightarrow> (coeff p) (degree p) = lead_coeff p"
  by (metis coeff.simps(2) list.exhaust_sel)

lemma coeff_list: "map (coeff p) (rev [0..< length p]) = p"
proof (induction p)
  case Nil thus ?case by simp
next
  case (Cons a p)
  have "map (coeff (a # p)) (rev [0..<length (a # p)]) =
         a # (map (coeff p) (rev [0..<length p]))"
    by auto
  also have " ... = a # p"
    using Cons by simp
  finally show ?case . 
qed

lemma coeff_nth: "i < length p \<Longrightarrow> (coeff p) i = p ! (length p - 1 - i)"
proof -
  assume i_lt: "i < length p"
  hence "(coeff p) i = (map (coeff p) [0..< length p]) ! i"
    by simp
  also have " ... = (rev (map (coeff p) (rev [0..< length p]))) ! i"
    by (simp add: rev_map)
  also have " ... = (map (coeff p) (rev [0..< length p])) ! (length p - 1 - i)"
    using coeff_list i_lt rev_nth by auto
  also have " ... = p ! (length p - 1 - i)"
    using coeff_list[of p] by simp
  finally show "(coeff p) i = p ! (length p - 1 - i)" .
qed

lemma coeff_iff_length_cond:
  assumes "length p1 = length p2"
  shows "p1 = p2 \<longleftrightarrow> coeff p1 = coeff p2"
proof
  show "p1 = p2 \<Longrightarrow> coeff p1 = coeff p2"
    by simp
next
  assume A: "coeff p1 = coeff p2"
  have "p1 = map (coeff p1) (rev [0..< length p1])"
    using coeff_list[of p1] by simp
  also have " ... = map (coeff p2) (rev [0..< length p2])"
    using A assms by simp
  also have " ... = p2"
    using coeff_list[of p2] by simp
  finally show "p1 = p2" .
qed

lemma coeff_img_restrict: "(coeff p) ` {..< length p} = set p"
  using coeff_list[of p] by (metis atLeast_upt image_set set_rev)

lemma coeff_length: "\<And>i. i \<ge> length p \<Longrightarrow> (coeff p) i = \<zero>"
  by (induction p) (auto)

lemma coeff_degree: "\<And>i. i > degree p \<Longrightarrow> (coeff p) i = \<zero>"
  using coeff_length by (simp)

lemma replicate_zero_coeff [simp]: "coeff (replicate n \<zero>) = (\<lambda>_. \<zero>)"
  by (induction n) (auto)

lemma scalar_coeff: "a \<in> carrier R \<Longrightarrow> coeff (map (\<lambda>b. a \<otimes> b) p) = (\<lambda>i. a \<otimes> (coeff p) i)"
  by (induction p) (auto)

lemma monon_coeff: "coeff (monon a n) = (\<lambda>i. if i = n then a else \<zero>)"
  unfolding monon_def by (induction n) (auto)

lemma coeff_img:
  "(coeff p) ` {..< length p} = set p"
  "(coeff p) ` { length p ..} = { \<zero> }"
  "(coeff p) ` UNIV = (set p) \<union> { \<zero> }"
  using coeff_img_restrict
proof (simp)
  show coeff_img_up: "(coeff p) ` { length p ..} = { \<zero> }"
    using coeff_length[of p] by force
  from coeff_img_up and coeff_img_restrict[of p]
  show "(coeff p) ` UNIV = (set p) \<union> { \<zero> }"
    by force
qed

lemma degree_def':
  assumes "polynomial K p"
  shows "degree p = (LEAST n. \<forall>i. i > n \<longrightarrow> (coeff p) i = \<zero>)"
proof (cases p)
  case Nil thus ?thesis by auto
next
  define P where "P = (\<lambda>n. \<forall>i. i > n \<longrightarrow> (coeff p) i = \<zero>)"

  case (Cons a ps)
  hence "(coeff p) (degree p) \<noteq> \<zero>"
    using assms unfolding polynomial_def by auto
  hence "\<And>n. n < degree p \<Longrightarrow> \<not> P n"
    unfolding P_def by auto
  moreover have "P (degree p)"
    unfolding P_def using coeff_degree[of p] by simp
  ultimately have "degree p = (LEAST n. P n)"
    by (meson LeastI nat_neq_iff not_less_Least)
  thus ?thesis unfolding P_def .
qed

lemma coeff_iff_polynomial_cond:
  assumes "polynomial K p1" and "polynomial K p2"
  shows "p1 = p2 \<longleftrightarrow> coeff p1 = coeff p2"
proof
  show "p1 = p2 \<Longrightarrow> coeff p1 = coeff p2"
    by simp
next
  assume coeff_eq: "coeff p1 = coeff p2"
  hence deg_eq: "degree p1 = degree p2"
    using degree_def'[OF assms(1)] degree_def'[OF assms(2)] by auto
  thus "p1 = p2"
  proof (cases)
    assume "p1 \<noteq> [] \<and> p2 \<noteq> []"
    hence "length p1 = length p2"
      using deg_eq by (simp add: Nitpick.size_list_simp(2)) 
    thus ?thesis
      using coeff_iff_length_cond[of p1 p2] coeff_eq by simp
  next
    { fix p1 p2 assume A: "p1 = []" "coeff p1 = coeff p2" "polynomial K p2"
      have "p2 = []"
      proof (rule ccontr)
        assume "p2 \<noteq> []"
        hence "(coeff p2) (degree p2) \<noteq> \<zero>"
          using A(3) unfolding polynomial_def
          by (metis coeff.simps(2) list.collapse)
        moreover have "(coeff p1) ` UNIV = { \<zero> }"
          using A(1) by auto
        hence "(coeff p2) ` UNIV = { \<zero> }"
          using A(2) by simp
        ultimately show False
          by blast
      qed } note aux_lemma = this
    assume "\<not> (p1 \<noteq> [] \<and> p2 \<noteq> [])"
    hence "p1 = [] \<or> p2 = []" by simp
    thus ?thesis
      using assms coeff_eq aux_lemma[of p1 p2] aux_lemma[of p2 p1] by auto
  qed
qed

lemma normalize_lead_coeff:
  assumes "length (normalize p) < length p"
  shows "lead_coeff p = \<zero>"
proof (cases p)
  case Nil thus ?thesis
    using assms by simp
next
  case (Cons a ps) thus ?thesis
    using assms by (cases "a = \<zero>") (auto)
qed

lemma normalize_length_lt:
  assumes "lead_coeff p = \<zero>" and "length p > 0"
  shows "length (normalize p) < length p"
proof (cases p)
  case Nil thus ?thesis
    using assms by simp
next
  case (Cons a ps) thus ?thesis
    using normalize_length_le[of ps] assms by simp
qed

lemma normalize_length_eq:
  assumes "lead_coeff p \<noteq> \<zero>"
  shows "length (normalize p) = length p"
  using normalize_length_le[of p] assms nat_less_le normalize_lead_coeff by auto

lemma normalize_replicate_zero: "normalize ((replicate n \<zero>) @ p) = normalize p"
  by (induction n) (auto)

lemma normalize_def':
  shows   "p = (replicate (length p - length (normalize p)) \<zero>) @
                    (drop (length p - length (normalize p)) p)" (is ?statement1)
  and "normalize p = drop (length p - length (normalize p)) p"  (is ?statement2)
proof -
  show ?statement1
  proof (induction p)
    case Nil thus ?case by simp
  next
    case (Cons a p) thus ?case
    proof (cases "a = \<zero>")
      assume "a \<noteq> \<zero>" thus ?case
        using Cons by simp
    next
      assume eq_zero: "a = \<zero>"
      hence len_eq:
        "Suc (length p - length (normalize p)) = length (a # p) - length (normalize (a # p))"
        by (simp add: Suc_diff_le normalize_length_le)
      have "a # p = \<zero> # (replicate (length p - length (normalize p)) \<zero> @
                              drop (length p - length (normalize p)) p)"
        using eq_zero Cons by simp
      also have " ... = (replicate (Suc (length p - length (normalize p))) \<zero> @
                              drop (Suc (length p - length (normalize p))) (a # p))"
        by simp
      also have " ... = (replicate (length (a # p) - length (normalize (a # p))) \<zero> @
                              drop (length (a # p) - length (normalize (a # p))) (a # p))"
        using len_eq by simp
      finally show ?case .
    qed
  qed
next
  show ?statement2
  proof -
    have "\<exists>m. normalize p = drop m p"
    proof (induction p)
      case Nil thus ?case by simp
    next
      case (Cons a p) thus ?case
        apply (cases "a = \<zero>")
        apply (auto)
        apply (metis drop_Suc_Cons)
        apply (metis drop0)
        done
    qed
    then obtain m where m: "normalize p = drop m p" by auto
    hence "length (normalize p) = length p - m" by simp
    thus ?thesis
      using m by (metis rev_drop rev_rev_ident take_rev)
  qed
qed

lemma normalize_coeff: "coeff p = coeff (normalize p)"
proof (induction p)
  case Nil thus ?case by simp
next
  case (Cons a p)
  have "coeff (normalize p) (length p) = \<zero>"
    using normalize_length_le[of p] coeff_degree[of "normalize p"]
    by (metis One_nat_def coeff.simps(1) diff_less length_0_conv
        less_imp_diff_less nat_neq_iff neq0_conv not_le zero_less_Suc)
  then show ?case
    using Cons by (cases "a = \<zero>") (auto)
qed

lemma append_coeff:
  "coeff (p @ q) = (\<lambda>i. if i < length q then (coeff q) i else (coeff p) (i - length q))"
proof (induction p)
  case Nil thus ?case
    using coeff_length[of q] by auto
next
  case (Cons a p)
  have "coeff ((a # p) @ q) = (\<lambda>i. if i = length p + length q then a else (coeff (p @ q)) i)"
    by auto
  also have " ... = (\<lambda>i. if i = length p + length q then a
                         else if i < length q then (coeff q) i
                         else (coeff p) (i - length q))"
    using Cons by auto
  also have " ... = (\<lambda>i. if i < length q then (coeff q) i
                         else if i = length p + length q then a else (coeff p) (i - length q))"
    by auto
  also have " ... = (\<lambda>i. if i < length q then (coeff q) i
                         else if i - length q = length p then a else (coeff p) (i - length q))"
    by fastforce
  also have " ... = (\<lambda>i. if i < length q then (coeff q) i else (coeff (a # p)) (i - length q))"
    by auto
  finally show ?case .
qed

lemma prefix_replicate_zero_coeff: "coeff p = coeff ((replicate n \<zero>) @ p)"
  using append_coeff[of "replicate n \<zero>" p] replicate_zero_coeff[of n] coeff_length[of p] by auto

(* ========================================================================== *)
context
  fixes K :: "'a set" assumes K: "subring K R"
begin

lemma polynomial_in_carrier [intro]: "polynomial K p \<Longrightarrow> set p \<subseteq> carrier R"
  unfolding polynomial_def using subringE(1)[OF K] by auto

lemma carrier_polynomial [intro]: "polynomial K p \<Longrightarrow> polynomial (carrier R) p"
  unfolding polynomial_def using subringE(1)[OF K] by auto

lemma append_is_polynomial: "\<lbrakk> polynomial K p; p \<noteq> [] \<rbrakk> \<Longrightarrow> polynomial K (p @ (replicate n \<zero>))"
  unfolding polynomial_def using subringE(2)[OF K] by auto

lemma lead_coeff_in_carrier: "polynomial K (a # p) \<Longrightarrow> a \<in> carrier R - { \<zero> }"
  unfolding polynomial_def using subringE(1)[OF K] by auto

lemma monon_is_polynomial [intro]: "a \<in> K - { \<zero> } \<Longrightarrow> polynomial K (monon a n)"
  unfolding polynomial_def monon_def using subringE(2)[OF K] by auto

lemma eval_poly_in_carrier: "\<lbrakk> polynomial K p; x \<in> carrier R \<rbrakk> \<Longrightarrow> (eval p) x \<in> carrier R"
  using eval_in_carrier[OF polynomial_in_carrier] .

lemma poly_coeff_in_carrier [simp]: "polynomial K p \<Longrightarrow> coeff p i \<in> carrier R"
  using coeff_in_carrier[OF polynomial_in_carrier] .

end (* of fixed K context. *)
(* ========================================================================== *)


subsection \<open>Polynomial Addition\<close>

(* ========================================================================== *)
context
  fixes K :: "'a set" assumes K: "subring K R"
begin

lemma poly_add_is_polynomial:
  assumes "set p1 \<subseteq> K" and "set p2 \<subseteq> K"
  shows "polynomial K (poly_add p1 p2)"
proof -
  { fix p1 p2 assume A: "set p1 \<subseteq> K" "set p2 \<subseteq> K" "length p1 \<ge> length p2"
    hence "polynomial K (poly_add p1 p2)"
    proof -
      define p2' where "p2' = (replicate (length p1 - length p2) \<zero>) @ p2"
      hence "set p2' \<subseteq> K" and "length p1 = length p2'"
        using A(2-3) subringE(2)[OF K] by auto
      hence "set (map2 (\<oplus>) p1 p2') \<subseteq> K"
        using A(1) subringE(7)[OF K]
        by (induct p1) (auto, metis set_ConsD set_mp set_zip_leftD set_zip_rightD)
      thus ?thesis
        unfolding p2'_def using normalize_gives_polynomial A(3) by simp
    qed }
  thus ?thesis
    using assms by auto
qed

lemma poly_add_closed: "\<lbrakk> polynomial K p1; polynomial K p2 \<rbrakk> \<Longrightarrow> polynomial K (poly_add p1 p2)"
  using poly_add_is_polynomial polynomial_incl by simp

lemma poly_add_length_eq:
  assumes "polynomial K p1" "polynomial K p2" and "length p1 \<noteq> length p2"
  shows "length (poly_add p1 p2) = max (length p1) (length p2)"
proof -
  { fix p1 p2 assume A: "polynomial K p1" "polynomial K p2" "length p1 > length p2"
    hence "length (poly_add p1 p2) = max (length p1) (length p2)"
    proof -
      let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
      have p1: "p1 \<noteq> []" and p2: "?p2 \<noteq> []"
        using A(3) by auto
      hence "lead_coeff (map2 (\<oplus>) p1 ?p2) = lead_coeff p1 \<oplus> lead_coeff ?p2"
        by (smt case_prod_conv list.exhaust_sel list.map(2) list.sel(1) zip_Cons_Cons)
      moreover have "lead_coeff p1 \<in> carrier R"
        using p1 A(1) lead_coeff_in_carrier[OF K, of "hd p1" "tl p1"] by auto
      ultimately have "lead_coeff (map2 (\<oplus>) p1 ?p2) = lead_coeff p1"
        using A(3) by auto
      moreover have "lead_coeff p1 \<noteq> \<zero>"
        using p1 A(1) unfolding polynomial_def by simp
      ultimately have "length (normalize (map2 (\<oplus>) p1 ?p2)) = length p1"
        using normalize_length_eq by auto
      thus ?thesis
        using A(3) by auto
    qed }
  thus ?thesis
    using assms by auto
qed

lemma poly_add_degree_eq:
  assumes "polynomial K p1" "polynomial K p2" and "degree p1 \<noteq> degree p2"
  shows "degree (poly_add p1 p2) = max (degree p1) (degree p2)"
  using poly_add_length_eq[of p1 p2] assms
  by (smt diff_le_mono le_cases max.absorb1 max_def)

end (* of fixed K context. *)
(* ========================================================================== *)

lemma poly_add_in_carrier:
  "\<lbrakk> set p1 \<subseteq> carrier R; set p2 \<subseteq> carrier R \<rbrakk> \<Longrightarrow> set (poly_add p1 p2) \<subseteq> carrier R"
  using polynomial_incl[OF poly_add_is_polynomial[OF carrier_is_subring]] by simp

lemma poly_add_length_le: "length (poly_add p1 p2) \<le> max (length p1) (length p2)"
proof -
  { fix p1 p2 :: "'a list" assume A: "length p1 \<ge> length p2"
    let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
    have "length (poly_add p1 p2) \<le> max (length p1) (length p2)"
      using normalize_length_le[of "map2 (\<oplus>) p1 ?p2"] A by auto }
  thus ?thesis
    by (metis le_cases max.commute poly_add.simps)
qed

lemma poly_add_degree: "degree (poly_add p1 p2) \<le> max (degree p1) (degree p2)"
  using poly_add_length_le by (meson diff_le_mono le_max_iff_disj)

lemma poly_add_coeff_aux:
  assumes "length p1 \<ge> length p2"
  shows "coeff (poly_add p1 p2) = (\<lambda>i. ((coeff p1) i) \<oplus> ((coeff p2) i))"
proof
  fix i
  have "i < length p1 \<Longrightarrow> (coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)"
  proof -
    let ?p2 = "(replicate (length p1 - length p2) \<zero>) @ p2"
    have len_eqs: "length p1 = length ?p2" "length (map2 (\<oplus>) p1 ?p2) = length p1"
      using assms by auto
    assume i_lt: "i < length p1"
    have "(coeff (poly_add p1 p2)) i = (coeff (map2 (\<oplus>) p1 ?p2)) i"
      using normalize_coeff[of "map2 (\<oplus>) p1 ?p2"] assms by auto
    also have " ... = (map2 (\<oplus>) p1 ?p2) ! (length p1 - 1 - i)"
      using coeff_nth[of i "map2 (\<oplus>) p1 ?p2"] len_eqs(2) i_lt by auto
    also have " ... = (p1 ! (length p1 - 1 - i)) \<oplus> (?p2 ! (length ?p2 - 1 - i))"
      using len_eqs i_lt by auto
    also have " ... = ((coeff p1) i) \<oplus> ((coeff ?p2) i)"
      using coeff_nth[of i p1] coeff_nth[of i ?p2] i_lt len_eqs(1) by auto
    also have " ... = ((coeff p1) i) \<oplus> ((coeff p2) i)"
      using prefix_replicate_zero_coeff by simp
    finally show "(coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)" .
  qed
  moreover
  have "i \<ge> length p1 \<Longrightarrow> (coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)"
    using coeff_length[of "poly_add p1 p2"] coeff_length[of p1] coeff_length[of p2]
          poly_add_length_le[of p1 p2] assms by auto
  ultimately show "(coeff (poly_add p1 p2)) i = ((coeff p1) i) \<oplus> ((coeff p2) i)"
    using not_le by blast
qed

lemma poly_add_coeff:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "coeff (poly_add p1 p2) = (\<lambda>i. ((coeff p1) i) \<oplus> ((coeff p2) i))"
proof -
  have "length p1 \<ge> length p2 \<or> length p2 > length p1"
    by auto
  thus ?thesis
  proof
    assume "length p1 \<ge> length p2" thus ?thesis
      using poly_add_coeff_aux by simp
  next
    assume "length p2 > length p1"
    hence "coeff (poly_add p1 p2) = (\<lambda>i. ((coeff p2) i) \<oplus> ((coeff p1) i))"
      using poly_add_coeff_aux by simp
    thus ?thesis
      using assms by (simp add: add.m_comm)
  qed
qed

lemma poly_add_comm:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_add p1 p2 = poly_add p2 p1"
proof -
  have "coeff (poly_add p1 p2) = coeff (poly_add p2 p1)"
    using poly_add_coeff[OF assms] poly_add_coeff[OF assms(2) assms(1)]
          coeff_in_carrier[OF assms(1)] coeff_in_carrier[OF assms(2)] add.m_comm by auto
  thus ?thesis
    using coeff_iff_polynomial_cond[OF
          poly_add_is_polynomial[OF carrier_is_subring assms] 
          poly_add_is_polynomial[OF carrier_is_subring assms(2,1)]] by simp 
qed

lemma poly_add_monon:
  assumes "set p \<subseteq> carrier R" and "a \<in> carrier R - { \<zero> }"
  shows "poly_add (monon a (length p)) p = a # p"
  unfolding monon_def using assms by (induction p) (auto)

lemma poly_add_append_zero:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R"
  shows "poly_add (p @ [ \<zero> ]) (q @ [ \<zero> ]) = normalize ((poly_add p q) @ [ \<zero> ])"
proof -
  have in_carrier: "set (p @ [ \<zero> ]) \<subseteq> carrier R" "set (q @ [ \<zero> ]) \<subseteq> carrier R"
    using assms by auto
  have "coeff (poly_add (p @ [ \<zero> ]) (q @ [ \<zero> ])) = coeff ((poly_add p q) @ [ \<zero> ])"
    using append_coeff[of p "[ \<zero> ]"] poly_add_coeff[OF in_carrier]
          append_coeff[of q "[ \<zero> ]"] append_coeff[of "poly_add p q" "[ \<zero> ]"]
          poly_add_coeff[OF assms] assms[THEN coeff_in_carrier] by auto
  hence "coeff (poly_add (p @ [ \<zero> ]) (q @ [ \<zero> ])) = coeff (normalize ((poly_add p q) @ [ \<zero> ]))"
    using normalize_coeff by simp
  moreover have "set ((poly_add p q) @ [ \<zero> ]) \<subseteq> carrier R"
    using poly_add_in_carrier[OF assms] by simp
  ultimately show ?thesis
    using coeff_iff_polynomial_cond[OF poly_add_is_polynomial[OF carrier_is_subring in_carrier]
          normalize_gives_polynomial] by simp
qed

lemma poly_add_normalize_aux:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_add p1 p2 = poly_add (normalize p1) p2"
proof -
  { fix n p1 p2 assume "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
    hence "poly_add p1 p2 = poly_add ((replicate n \<zero>) @ p1) p2"
    proof (induction n)
      case 0 thus ?case by simp
    next
      { fix p1 p2 :: "'a list"
        assume in_carrier: "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
        have "poly_add p1 p2 = poly_add (\<zero> # p1) p2"
        proof -
          have "length p1 \<ge> length p2 \<Longrightarrow> ?thesis"
          proof -
            assume A: "length p1 \<ge> length p2"
            let ?p2 = "\<lambda>n. (replicate n \<zero>) @ p2"
            have "poly_add p1 p2 = normalize (map2 (\<oplus>) (\<zero> # p1) (\<zero> # ?p2 (length p1 - length p2)))"
              using A by simp
            also have " ... = normalize (map2 (\<oplus>) (\<zero> # p1) (?p2 (length (\<zero> # p1) - length p2)))"
              by (simp add: A Suc_diff_le)
            also have " ... = poly_add (\<zero> # p1) p2"
              using A by simp
            finally show ?thesis .
          qed

          moreover have "length p2 > length p1 \<Longrightarrow> ?thesis"
          proof -
            assume A: "length p2 > length p1"
            let ?f = "\<lambda>n p. (replicate n \<zero>) @ p"
            have "poly_add p1 p2 = poly_add p2 p1"
              using A by simp
            also have " ... = normalize (map2 (\<oplus>) p2 (?f (length p2 - length p1) p1))"
              using A by simp
            also have " ... = normalize (map2 (\<oplus>) p2 (?f (length p2 - Suc (length p1)) (\<zero> # p1)))"
              by (metis A Suc_diff_Suc append_Cons replicate_Suc replicate_app_Cons_same)
            also have " ... = poly_add p2 (\<zero> # p1)"
              using A by simp
            also have " ... = poly_add (\<zero> # p1) p2"
              using poly_add_comm[of p2 "\<zero> # p1"] in_carrier by auto
            finally show ?thesis .
          qed

          ultimately show ?thesis by auto
        qed } note aux_lemma = this

      case (Suc n)
      hence in_carrier: "set (replicate n \<zero> @ p1) \<subseteq> carrier R"
        by auto
      have "poly_add p1 p2 = poly_add (replicate n \<zero> @ p1) p2"
        using Suc by simp
      also have " ... = poly_add (replicate (Suc n) \<zero> @ p1) p2"
        using aux_lemma[OF in_carrier Suc(3)] by simp
      finally show ?case .
    qed } note aux_lemma = this

  have "poly_add p1 p2 =
        poly_add ((replicate (length p1 - length (normalize p1)) \<zero>) @ normalize p1) p2"
    using normalize_def'[of p1] by simp
  also have " ... = poly_add (normalize p1) p2"
    using aux_lemma[OF normalize_in_carrier[OF assms(1)] assms(2)] by simp
  finally show ?thesis .
qed

lemma poly_add_normalize:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_add p1 p2 = poly_add (normalize p1) p2"
    and "poly_add p1 p2 = poly_add p1 (normalize p2)"
    and "poly_add p1 p2 = poly_add (normalize p1) (normalize p2)"
proof -
  show "poly_add p1 p2 = poly_add p1 (normalize p2)"
    unfolding poly_add_comm[OF assms] poly_add_normalize_aux[OF assms(2) assms(1)]
              poly_add_comm[OF normalize_in_carrier[OF assms(2)] assms(1)] by simp 
next
  show "poly_add p1 p2 = poly_add (normalize p1) p2"
    using poly_add_normalize_aux[OF assms] .
  also have " ... = poly_add (normalize p2) (normalize p1)"
    unfolding  poly_add_comm[OF normalize_in_carrier[OF assms(1)] assms(2)]
               poly_add_normalize_aux[OF assms(2) normalize_in_carrier[OF assms(1)]] by simp
  finally show "poly_add p1 p2 = poly_add (normalize p1) (normalize p2)"
    unfolding  poly_add_comm[OF assms[THEN normalize_in_carrier]] .
qed

lemma poly_add_zero':
  assumes "set p \<subseteq> carrier R"
  shows "poly_add p [] = normalize p" and "poly_add [] p = normalize p"
proof -
  have "map2 (\<oplus>) p (replicate (length p) \<zero>) = p"
    using assms by (induct p) (auto)
  thus "poly_add p [] = normalize p" and "poly_add [] p = normalize p"
    using poly_add_comm[OF assms, of "[]"] by simp+
qed

lemma poly_add_zero:
  assumes "subring K R" "polynomial K p"
  shows "poly_add p [] = p" and "poly_add [] p = p"
  using poly_add_zero' normalize_idem polynomial_in_carrier assms by auto

lemma poly_add_replicate_zero':
  assumes "set p \<subseteq> carrier R"
  shows "poly_add p (replicate n \<zero>) = normalize p" and "poly_add (replicate n \<zero>) p = normalize p"
proof -
  have "poly_add p (replicate n \<zero>) = poly_add p []"
    using poly_add_normalize(2)[OF assms, of "replicate n \<zero>"]
          normalize_replicate_zero[of n "[]"] by force
  also have " ... = normalize p"
    using poly_add_zero'[OF assms] by simp
  finally show "poly_add p (replicate n \<zero>) = normalize p" .
  thus "poly_add (replicate n \<zero>) p = normalize p"
    using poly_add_comm[OF assms, of "replicate n \<zero>"] by force
qed

lemma poly_add_replicate_zero:
  assumes "subring K R" "polynomial K p"
  shows "poly_add p (replicate n \<zero>) = p" and "poly_add (replicate n \<zero>) p = p"
  using poly_add_replicate_zero' normalize_idem polynomial_in_carrier assms by auto



subsection \<open>Dense Representation\<close>

lemma dense_repr_replicate_zero: "dense_repr ((replicate n \<zero>) @ p) = dense_repr p"
  by (induction n) (auto)

lemma polynomial_dense_repr:
  assumes "polynomial K p" and "p \<noteq> []"
  shows "dense_repr p = (lead_coeff p, degree p) # dense_repr (normalize (tl p))"
proof -
  let ?len = length and ?norm = normalize
  obtain a p' where p: "p = a # p'"
    using assms(2) list.exhaust_sel by blast 
  hence a: "a \<in> K - { \<zero> }" and p': "set p' \<subseteq> K"
    using assms(1) unfolding p by (auto simp add: polynomial_def)
  hence "dense_repr p = (lead_coeff p, degree p) # dense_repr p'"
    unfolding p by simp
  also have " ... =
    (lead_coeff p, degree p) # dense_repr ((replicate (?len p' - ?len (?norm p')) \<zero>) @ ?norm p')"
    using normalize_def' dense_repr_replicate_zero by simp
  also have " ... = (lead_coeff p, degree p) # dense_repr (?norm p')"
    using dense_repr_replicate_zero by simp
  finally show ?thesis
    unfolding p by simp
qed

lemma monon_decomp:
  assumes "subring K R" "polynomial K p"
  shows "p = of_dense (dense_repr p)"
  using assms(2)
proof (induct "length p" arbitrary: p rule: less_induct)
  case less thus ?case
  proof (cases p)
    case Nil thus ?thesis by simp
  next
    case (Cons a l)
    hence a: "a \<in> carrier R - { \<zero> }" and l: "set l \<subseteq> carrier R"  "set l \<subseteq> K"
      using less(2) subringE(1)[OF assms(1)] by (auto simp add: polynomial_def)
    hence "a # l = poly_add (monon a (degree (a # l))) l"
      using poly_add_monon[of l a] by simp
    also have " ... = poly_add (monon a (degree (a # l))) (normalize l)"
      using poly_add_normalize(2)[of "monon a (degree (a # l))", OF _ l(1)] a
      unfolding monon_def by force
    also have " ... = poly_add (monon a (degree (a # l))) (of_dense (dense_repr (normalize l)))"
      using less(1)[OF _ normalize_gives_polynomial[OF l(2)]] normalize_length_le[of l]
      unfolding Cons by simp
    also have " ... = of_dense ((a, degree (a # l)) # dense_repr (normalize l))"
      by simp
    also have " ... = of_dense (dense_repr (a # l))"
      using polynomial_dense_repr[OF less(2)] unfolding Cons by simp
    finally show ?thesis
      unfolding Cons by simp
  qed
qed


subsection \<open>Polynomial Multiplication\<close>

lemma poly_mult_is_polynomial:
  assumes "subring K R" "set p1 \<subseteq> K" and "set p2 \<subseteq> K"
  shows "polynomial K (poly_mult p1 p2)"
  using assms(2-3)
proof (induction p1)
  case Nil thus ?case
    by (simp add: polynomial_def)
next
  case (Cons a p1)
  let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (degree (a # p1)) \<zero>)"
  
  have "set (poly_mult p1 p2) \<subseteq> K"
    using Cons unfolding polynomial_def by auto
  moreover have "set ?a_p2 \<subseteq> K"
      using assms(3) Cons(2) subringE(1-2,6)[OF assms(1)] by(induct p2) (auto)
  ultimately have "polynomial K (poly_add ?a_p2 (poly_mult p1 p2))"
    using poly_add_is_polynomial[OF assms(1)] by blast
  thus ?case by simp
qed

lemma poly_mult_closed:
  assumes "subring K R"
  shows "\<lbrakk> polynomial K p1; polynomial K p2 \<rbrakk> \<Longrightarrow> polynomial K (poly_mult p1 p2)"
  using poly_mult_is_polynomial polynomial_incl assms by simp

lemma poly_mult_in_carrier:
  "\<lbrakk> set p1 \<subseteq> carrier R; set p2 \<subseteq> carrier R \<rbrakk> \<Longrightarrow> set (poly_mult p1 p2) \<subseteq> carrier R"
  using poly_mult_is_polynomial polynomial_in_carrier carrier_is_subring by simp

lemma poly_mult_coeff:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "coeff (poly_mult p1 p2) = (\<lambda>i. \<Oplus> k \<in> {..i}. (coeff p1) k \<otimes> (coeff p2) (i - k))"
  using assms(1) 
proof (induction p1)
  case Nil thus ?case using assms(2) by auto
next
  case (Cons a p1)
  hence in_carrier:
    "a \<in> carrier R" "\<And>i. (coeff p1) i \<in> carrier R" "\<And>i. (coeff p2) i \<in> carrier R"
    using coeff_in_carrier assms(2) by auto

  let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (degree (a # p1)) \<zero>)"
  have "coeff  (replicate (degree (a # p1)) \<zero>) = (\<lambda>_. \<zero>)"
   and "length (replicate (degree (a # p1)) \<zero>) = length p1"
    using prefix_replicate_zero_coeff[of "[]" "length p1"] by auto
  hence "coeff ?a_p2 = (\<lambda>i. if i < length p1 then \<zero> else (coeff (map (\<lambda>b. a \<otimes> b) p2)) (i - length p1))"
    using append_coeff[of "map (\<lambda>b. a \<otimes> b) p2" "replicate (length p1) \<zero>"] by auto
  also have " ... = (\<lambda>i. if i < length p1 then \<zero> else a \<otimes> ((coeff p2) (i - length p1)))"
  proof -
    have "\<And>i. i < length p2 \<Longrightarrow> (coeff (map (\<lambda>b. a \<otimes> b) p2)) i = a \<otimes> ((coeff p2) i)"
    proof -
      fix i assume i_lt: "i < length p2"
      hence "(coeff (map (\<lambda>b. a \<otimes> b) p2)) i = (map (\<lambda>b. a \<otimes> b) p2) ! (length p2 - 1 - i)"
        using coeff_nth[of i "map (\<lambda>b. a \<otimes> b) p2"] by auto
      also have " ... = a \<otimes> (p2 ! (length p2 - 1 - i))"
        using i_lt by auto
      also have " ... = a \<otimes> ((coeff p2) i)"
        using coeff_nth[OF i_lt] by simp
      finally show "(coeff (map (\<lambda>b. a \<otimes> b) p2)) i = a \<otimes> ((coeff p2) i)" .
    qed
    moreover have "\<And>i. i \<ge> length p2 \<Longrightarrow> (coeff (map (\<lambda>b. a \<otimes> b) p2)) i = a \<otimes> ((coeff p2) i)"
      using coeff_length[of p2] coeff_length[of "map (\<lambda>b. a \<otimes> b) p2"] in_carrier by auto
    ultimately show ?thesis by (meson not_le)
  qed
  also have " ... = (\<lambda>i. \<Oplus> k \<in> {..i}. (if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k))"
  (is "?f1 = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)))")
  proof
    fix i
    have "\<And>k. k \<in> {..i} \<Longrightarrow> ?f2 k \<otimes> ?f3 (i - k) = \<zero>" if "i < length p1"
      using in_carrier that by auto
    hence "(\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)) = \<zero>" if "i < length p1"
      using that in_carrier
            add.finprod_cong'[of "{..i}" "{..i}" "\<lambda>k. ?f2 k \<otimes> ?f3 (i - k)" "\<lambda>i. \<zero>"]
      by auto
    hence eq_lt: "?f1 i = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k))) i" if "i < length p1"
      using that by auto

    have "\<And>k. k \<in> {..i} \<Longrightarrow>
              ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k) = (if length p1 = k then a \<otimes> coeff p2 (i - k) else \<zero>)"
      using in_carrier by auto
    hence "(\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)) = 
           (\<Oplus> k \<in> {..i}. (if length p1 = k then a \<otimes> coeff p2 (i - k) else \<zero>))"
      using in_carrier
            add.finprod_cong'[of "{..i}" "{..i}" "\<lambda>k. ?f2 k \<otimes> ?f3 (i - k)"
                             "\<lambda>k. (if length p1 = k then a \<otimes> coeff p2 (i - k) else \<zero>)"]
      by fastforce
    also have " ... = a \<otimes> (coeff p2) (i - length p1)" if "i \<ge> length p1"
      using add.finprod_singleton[of "length p1" "{..i}" "\<lambda>j. a \<otimes> (coeff p2) (i - j)"]
            in_carrier that by auto
    finally
    have "(\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k)) =  a \<otimes> (coeff p2) (i - length p1)" if "i \<ge> length p1"
      using that by simp
    hence eq_ge: "?f1 i = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k))) i" if "i \<ge> length p1"
      using that by auto

    from eq_lt eq_ge show "?f1 i = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?f2 k \<otimes> ?f3 (i - k))) i" by auto
  qed

  finally have coeff_a_p2:
    "coeff ?a_p2 = (\<lambda>i. \<Oplus> k \<in> {..i}. (if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k))" .

  have "set ?a_p2 \<subseteq> carrier R"
    using in_carrier(1) assms(2) by auto

  moreover have "set (poly_mult p1 p2) \<subseteq> carrier R"
    using poly_mult_in_carrier[OF _ assms(2)] Cons(2) by simp

  ultimately
  have "coeff (poly_mult (a # p1) p2) = (\<lambda>i. ((coeff ?a_p2) i) \<oplus> ((coeff (poly_mult p1 p2)) i))"
    using poly_add_coeff[of ?a_p2 "poly_mult p1 p2"] by simp
  also have " ... = (\<lambda>i. (\<Oplus> k \<in> {..i}. (if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k)) \<oplus>
                         (\<Oplus> k \<in> {..i}. (coeff p1) k \<otimes> (coeff p2) (i - k)))"
    using Cons  coeff_a_p2 by simp
  also have " ... = (\<lambda>i. (\<Oplus> k \<in> {..i}. ((if k = length p1 then a else \<zero>) \<otimes> (coeff p2) (i - k)) \<oplus>
                                                            ((coeff p1) k \<otimes> (coeff p2) (i - k))))"
    using add.finprod_multf in_carrier by auto
  also have " ... = (\<lambda>i. (\<Oplus> k \<in> {..i}. (coeff (a # p1) k) \<otimes> (coeff p2) (i - k)))"
   (is "(\<lambda>i. (\<Oplus> k \<in> {..i}. ?f i k)) = (\<lambda>i. (\<Oplus> k \<in> {..i}. ?g i k))")
  proof
    fix i
    have "\<And>k. ?f i k = ?g i k"
      using in_carrier coeff_length[of p1] by auto
    thus "(\<Oplus> k \<in> {..i}. ?f i k) = (\<Oplus> k \<in> {..i}. ?g i k)" by simp
  qed
  finally show ?case .
qed

lemma poly_mult_zero:
  assumes "set p \<subseteq> carrier R"
  shows "poly_mult [] p = []" and "poly_mult p [] = []"
proof (simp)
  have "coeff (poly_mult p []) = (\<lambda>_. \<zero>)"
    using poly_mult_coeff[OF assms, of "[]"] coeff_in_carrier[OF assms] by auto
  thus "poly_mult p [] = []"
    using coeff_iff_polynomial_cond[OF
          poly_mult_is_polynomial[OF carrier_is_subring assms] zero_is_polynomial] by simp
qed

lemma poly_mult_l_distr':
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R"
  shows "poly_mult (poly_add p1 p2) p3 = poly_add (poly_mult p1 p3) (poly_mult p2 p3)"
proof -
  let ?c1 = "coeff p1" and ?c2 = "coeff p2" and ?c3 = "coeff p3"
  have in_carrier:
    "\<And>i. ?c1 i \<in> carrier R" "\<And>i. ?c2 i \<in> carrier R" "\<And>i. ?c3 i \<in> carrier R"
    using assms coeff_in_carrier by auto

  have "coeff (poly_mult (poly_add p1 p2) p3) = (\<lambda>n. \<Oplus>i \<in> {..n}. (?c1 i \<oplus> ?c2 i) \<otimes> ?c3 (n - i))"
    using poly_mult_coeff[of "poly_add p1 p2" p3]  poly_add_coeff[OF assms(1-2)]
          poly_add_in_carrier[OF assms(1-2)] assms by auto
  also have " ... = (\<lambda>n. \<Oplus>i \<in> {..n}. (?c1 i \<otimes> ?c3 (n - i)) \<oplus> (?c2 i \<otimes> ?c3 (n - i)))"
    using in_carrier l_distr by auto
  also
  have " ... = (\<lambda>n. (\<Oplus>i \<in> {..n}. (?c1 i \<otimes> ?c3 (n - i))) \<oplus> (\<Oplus>i \<in> {..n}. (?c2 i \<otimes> ?c3 (n - i))))"
    using add.finprod_multf in_carrier by auto
  also have " ... = coeff (poly_add (poly_mult p1 p3) (poly_mult p2 p3))"
    using poly_mult_coeff[OF assms(1) assms(3)] poly_mult_coeff[OF assms(2-3)]
          poly_add_coeff[OF poly_mult_in_carrier[OF assms(1) assms(3)]]
                            poly_mult_in_carrier[OF assms(2-3)] by simp
  finally have "coeff (poly_mult (poly_add p1 p2) p3) =
                coeff (poly_add (poly_mult p1 p3) (poly_mult p2 p3))" .
  moreover have "polynomial (carrier R) (poly_mult (poly_add p1 p2) p3)"
            and "polynomial (carrier R) (poly_add (poly_mult p1 p3) (poly_mult p2 p3))"
    using assms poly_add_is_polynomial poly_mult_is_polynomial polynomial_in_carrier
          carrier_is_subring by auto
  ultimately show ?thesis
    using coeff_iff_polynomial_cond by auto 
qed

lemma poly_mult_l_distr:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" "polynomial K p3"
  shows "poly_mult (poly_add p1 p2) p3 = poly_add (poly_mult p1 p3) (poly_mult p2 p3)"
  using poly_mult_l_distr' polynomial_in_carrier assms by auto

lemma poly_mult_prepend_replicate_zero:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_mult p1 p2 = poly_mult ((replicate n \<zero>) @ p1) p2"
proof -
  { fix p1 p2 assume A: "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
    hence "poly_mult p1 p2 = poly_mult (\<zero> # p1) p2"
    proof -
      let ?a_p2 = "(map ((\<otimes>) \<zero>) p2) @ (replicate (length p1) \<zero>)"
      have "?a_p2 = replicate (length p2 + length p1) \<zero>"
        using A(2) by (induction p2) (auto)
      hence "poly_mult (\<zero> # p1) p2 = poly_add (replicate (length p2 + length p1) \<zero>) (poly_mult p1 p2)"
        by simp
      also have " ... = poly_add (normalize (replicate (length p2 + length p1) \<zero>)) (poly_mult p1 p2)"
        using poly_add_normalize(1)[of "replicate (length p2 + length p1) \<zero>" "poly_mult p1 p2"]
              poly_mult_in_carrier[OF A] by force
      also have " ... = poly_mult p1 p2"
        using poly_add_zero(2)[OF _ poly_mult_is_polynomial[OF _ A]] carrier_is_subring
              normalize_replicate_zero[of "length p2 + length p1" "[]"] by simp
      finally show ?thesis by auto
    qed } note aux_lemma = this
  
  from assms show ?thesis
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n) thus ?case
      using aux_lemma[of "replicate n \<zero> @ p1" p2] by force
  qed
qed

lemma poly_mult_normalize:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_mult p1 p2 = poly_mult (normalize p1) p2"
proof -
  let ?replicate = "replicate (length p1 - length (normalize p1)) \<zero>"
  have "poly_mult p1 p2 = poly_mult (?replicate @ (normalize p1)) p2"
    using normalize_def'[of p1] by simp
  thus ?thesis
    using poly_mult_prepend_replicate_zero normalize_in_carrier assms by auto
qed

lemma poly_mult_append_zero:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R"
  shows "poly_mult (p @ [ \<zero> ]) q = normalize ((poly_mult p q) @ [ \<zero> ])"
  using assms(1)
proof (induct p)
  case Nil thus ?case
    using poly_mult_normalize[OF _ assms(2), of "[] @ [ \<zero> ]"]
          poly_mult_zero(1) poly_mult_zero(1)[of "q @ [ \<zero> ]"] assms(2) by auto
next
  case (Cons a p)
  let ?q_a = "\<lambda>n. (map ((\<otimes>) a) q) @ (replicate n \<zero>)"
  have set_q_a: "\<And>n. set (?q_a n) \<subseteq> carrier R"
    using Cons(2) assms(2) by (induct q) (auto)
  have set_poly_mult: "set ((poly_mult p q) @ [ \<zero> ]) \<subseteq> carrier R"
    using poly_mult_in_carrier[OF _ assms(2)] Cons(2) by auto
  have "poly_mult ((a # p) @ [\<zero>]) q = poly_add (?q_a (Suc (length p))) (poly_mult (p @ [\<zero>]) q)"
    by auto
  also have " ... = poly_add (?q_a (Suc (length p))) (normalize ((poly_mult p q) @ [ \<zero> ]))"
    using Cons by simp
  also have " ... = poly_add ((?q_a (length p)) @ [ \<zero> ]) ((poly_mult p q) @ [ \<zero> ])"
    using poly_add_normalize(2)[OF set_q_a[of "Suc (length p)"] set_poly_mult]
    by (simp add: replicate_append_same)
  also have " ... = normalize ((poly_add (?q_a (length p)) (poly_mult p q)) @ [ \<zero> ])"
    using poly_add_append_zero[OF set_q_a[of "length p"] poly_mult_in_carrier[OF _ assms(2)]] Cons(2) by auto
  also have " ... = normalize ((poly_mult (a # p) q) @ [ \<zero> ])"
    by auto
  finally show ?case .
qed

end (* of ring context. *)


subsection \<open>Properties Within a Domain\<close>

context domain
begin

lemma one_is_polynomial [intro]: "subring K R \<Longrightarrow> polynomial K [ \<one> ]"
  unfolding polynomial_def using subringE(3) by auto

lemma poly_mult_comm:
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R"
  shows "poly_mult p1 p2 = poly_mult p2 p1"
proof -
  let ?c1 = "coeff p1" and ?c2 = "coeff p2"
  have "\<And>i. (\<Oplus>k \<in> {..i}. ?c1 k \<otimes> ?c2 (i - k)) = (\<Oplus>k \<in> {..i}. ?c2 k \<otimes> ?c1 (i - k))"
  proof -
    fix i :: nat
    let ?f = "\<lambda>k. ?c1 k \<otimes> ?c2 (i - k)"
    have in_carrier: "\<And>i. ?c1 i \<in> carrier R" "\<And>i. ?c2 i \<in> carrier R"
      using coeff_in_carrier[OF assms(1)] coeff_in_carrier[OF assms(2)] by auto

    have reindex_inj: "inj_on (\<lambda>k. i - k) {..i}"
      using inj_on_def by force
    moreover have "(\<lambda>k. i - k) ` {..i} \<subseteq> {..i}" by auto
    hence "(\<lambda>k. i - k) ` {..i} = {..i}"
      using reindex_inj endo_inj_surj[of "{..i}" "\<lambda>k. i - k"] by simp 
    ultimately have "(\<Oplus>k \<in> {..i}. ?f k) = (\<Oplus>k \<in> {..i}. ?f (i - k))"
      using add.finprod_reindex[of ?f "\<lambda>k. i - k" "{..i}"] in_carrier by auto

    moreover have "\<And>k. k \<in> {..i} \<Longrightarrow> ?f (i - k) = ?c2 k \<otimes> ?c1 (i - k)"
      using in_carrier m_comm by auto
    hence "(\<Oplus>k \<in> {..i}. ?f (i - k)) = (\<Oplus>k \<in> {..i}. ?c2 k \<otimes> ?c1 (i - k))"
      using add.finprod_cong'[of "{..i}" "{..i}"] in_carrier by auto
    ultimately show "(\<Oplus>k \<in> {..i}. ?f k) = (\<Oplus>k \<in> {..i}. ?c2 k \<otimes> ?c1 (i - k))"
      by simp
  qed
  hence "coeff (poly_mult p1 p2) = coeff (poly_mult p2 p1)"
    using poly_mult_coeff[OF assms] poly_mult_coeff[OF assms(2,1)] by simp
  thus ?thesis
    using coeff_iff_polynomial_cond[OF poly_mult_is_polynomial[OF _ assms]
                                       poly_mult_is_polynomial[OF _ assms(2,1)]]
          carrier_is_subring by simp
qed

lemma poly_mult_r_distr':
  assumes "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R"
  shows "poly_mult p1 (poly_add p2 p3) = poly_add (poly_mult p1 p2) (poly_mult p1 p3)"
  unfolding poly_mult_comm[OF assms(1) poly_add_in_carrier[OF assms(2-3)]]
            poly_mult_l_distr'[OF assms(2-3,1)] assms(2-3)[THEN poly_mult_comm[OF _ assms(1)]] ..

lemma poly_mult_r_distr:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" "polynomial K p3"
  shows "poly_mult p1 (poly_add p2 p3) = poly_add (poly_mult p1 p2) (poly_mult p1 p3)"
  using poly_mult_r_distr' polynomial_in_carrier assms by auto

lemma poly_mult_replicate_zero:
  assumes "set p \<subseteq> carrier R"
  shows "poly_mult (replicate n \<zero>) p = []"
    and "poly_mult p (replicate n \<zero>) = []"
proof -
  have in_carrier: "\<And>n. set (replicate n \<zero>) \<subseteq> carrier R" by auto
  show "poly_mult (replicate n \<zero>) p = []" using assms
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    hence "poly_mult (replicate (Suc n) \<zero>) p = poly_mult (\<zero> # (replicate n \<zero>)) p"
      by simp
    also have " ... = poly_add ((map (\<lambda>a. \<zero> \<otimes> a) p) @ (replicate n \<zero>)) []"
      using Suc by simp
    also have " ... = poly_add ((map (\<lambda>a. \<zero>) p) @ (replicate n \<zero>)) []"
      using Suc(2) by (smt map_eq_conv ring_simprules(24) subset_code(1))
    also have " ... = poly_add (replicate (length p + n) \<zero>) []"
      by (simp add: map_replicate_const replicate_add)
    also have " ... = poly_add [] []"
      using poly_add_normalize(1)[of "replicate (length p + n) \<zero>" "[]"]
            normalize_replicate_zero[of "length p + n" "[]"] by auto
    also have " ... = []" by simp
    finally show ?case . 
  qed
  thus "poly_mult p (replicate n \<zero>) = []"
    using poly_mult_comm[OF assms in_carrier] by simp
qed

lemma poly_mult_const':
  assumes "set p \<subseteq> carrier R" "a \<in> carrier R"
  shows "poly_mult [ a ] p = normalize (map (\<lambda>b. a \<otimes> b) p)"
    and "poly_mult p [ a ] = normalize (map (\<lambda>b. a \<otimes> b) p)"
proof -
  have "map2 (\<oplus>) (map ((\<otimes>) a) p) (replicate (length p) \<zero>) = map ((\<otimes>) a) p"
    using assms by (induction p) (auto)
  thus "poly_mult [ a ] p = normalize (map (\<lambda>b. a \<otimes> b) p)" by simp
  thus "poly_mult p [ a ] = normalize (map (\<lambda>b. a \<otimes> b) p)"
    using poly_mult_comm[OF assms(1), of "[ a ]"] assms(2) by auto
qed

lemma poly_mult_const:
  assumes "subring K R" "polynomial K p" "a \<in> K - { \<zero> }"
  shows "poly_mult [ a ] p = map (\<lambda>b. a \<otimes> b) p"
    and "poly_mult p [ a ] = map (\<lambda>b. a \<otimes> b) p"
proof -
  have in_carrier: "set p \<subseteq> carrier R" "a \<in> carrier R"
    using polynomial_in_carrier[OF assms(1-2)] assms(3) subringE(1)[OF assms(1)] by auto

  show "poly_mult [ a ] p = map (\<lambda>b. a \<otimes> b) p"
  proof (cases p)
    case Nil thus ?thesis
      using poly_mult_const'(1) in_carrier by auto
  next
    case (Cons b q)
    have "lead_coeff (map (\<lambda>b. a \<otimes> b) p) \<noteq> \<zero>"
      using assms subringE(1)[OF assms(1)] integral[of a b] Cons lead_coeff_in_carrier by auto
    hence "normalize (map (\<lambda>b. a \<otimes> b) p) = (map (\<lambda>b. a \<otimes> b) p)"
      unfolding Cons by simp
    thus ?thesis
      using poly_mult_const'(1) in_carrier by auto
  qed
  thus "poly_mult p [ a ] = map (\<lambda>b. a \<otimes> b) p"
    using poly_mult_comm[OF in_carrier(1)] in_carrier(2) by auto
qed

lemma poly_mult_semiassoc:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
  shows "poly_mult (poly_mult [ a ] p) q = poly_mult [ a ] (poly_mult p q)"
proof -
  let ?cp = "coeff p" and ?cq = "coeff q"
  have "coeff (poly_mult [ a ] p) = (\<lambda>i. (a \<otimes> ?cp i))"
    using poly_mult_const'(1)[OF assms(1,3)] normalize_coeff scalar_coeff[OF assms(3)] by simp

  hence "coeff (poly_mult (poly_mult [ a ] p) q) = (\<lambda>i. (\<Oplus>j \<in> {..i}. (a \<otimes> ?cp j) \<otimes> ?cq (i - j)))"
    using poly_mult_coeff[OF poly_mult_in_carrier[OF _ assms(1)] assms(2), of "[ a ]"] assms(3) by auto
  also have " ... = (\<lambda>i. a \<otimes> (\<Oplus>j \<in> {..i}. ?cp j \<otimes> ?cq (i - j)))"
  proof
    fix i show "(\<Oplus>j \<in> {..i}. (a \<otimes> ?cp j) \<otimes> ?cq (i - j)) = a \<otimes> (\<Oplus>j \<in> {..i}. ?cp j \<otimes> ?cq (i - j))"
      using finsum_rdistr[OF _ assms(3), of _ "\<lambda>j. ?cp j \<otimes> ?cq (i - j)"]
            assms(1-2)[THEN coeff_in_carrier] by (simp add: assms(3) m_assoc)
  qed
  also have " ... = coeff (poly_mult [ a ] (poly_mult p q))"
    unfolding poly_mult_const'(1)[OF poly_mult_in_carrier[OF assms(1-2)] assms(3)]
    using scalar_coeff[OF assms(3), of "poly_mult p q"]
          poly_mult_coeff[OF assms(1-2)] normalize_coeff by simp
  finally have "coeff (poly_mult (poly_mult [ a ] p) q) = coeff (poly_mult [ a ] (poly_mult p q))" .
  moreover have "polynomial (carrier R) (poly_mult (poly_mult [ a ] p) q)"
            and "polynomial (carrier R) (poly_mult [ a ] (poly_mult p q))"
    using poly_mult_is_polynomial[OF _ poly_mult_in_carrier[OF _ assms(1)] assms(2)]
          poly_mult_is_polynomial[OF _ _ poly_mult_in_carrier[OF assms(1-2)]]
          carrier_is_subring assms(3) by (auto simp del: poly_mult.simps)
  ultimately show ?thesis
    using coeff_iff_polynomial_cond by simp
qed


text \<open>Note that "polynomial (carrier R) p" and "subring K p; polynomial K p" are "equivalent"
      assumptions for any lemma in ring which the result doesn't depend on K, because carrier
      is a subring and a polynomial for a subset of the carrier is a carrier polynomial. The
      decision between one of them should be based on how the lemma is going to be used and
      proved. These are some tips:
        (a) Lemmas about the algebraic structure of polynomials should use the latter option.
        (b) Also, if the lemma deals with lots of polynomials, then the latter option is preferred.
        (c) If the proof is going to be much easier with the first option, do not hesitate. \<close>

lemma poly_mult_monon':
  assumes "set p \<subseteq> carrier R" "a \<in> carrier R"
  shows "poly_mult (monon a n) p = normalize ((map ((\<otimes>) a) p) @ (replicate n \<zero>))"
proof -
  have set_map: "set ((map ((\<otimes>) a) p) @ (replicate n \<zero>)) \<subseteq> carrier R"
    using assms by (induct p) (auto)
  show ?thesis
  using poly_mult_replicate_zero(1)[OF assms(1), of n]
        poly_add_zero'(1)[OF set_map]
  unfolding monon_def by simp
qed

lemma poly_mult_monon:
  assumes "polynomial (carrier R) p" "a \<in> carrier R - { \<zero> }"
  shows "poly_mult (monon a n) p =
           (if p = [] then [] else (poly_mult [ a ] p) @ (replicate n \<zero>))"
proof (cases p)
  case Nil thus ?thesis
    using poly_mult_zero(2)[of "monon a n"] assms(2) monon_def by fastforce
next
  case (Cons b ps)
  hence "lead_coeff ((map (\<lambda>b. a \<otimes> b) p) @ (replicate n \<zero>)) \<noteq> \<zero>"
    using Cons assms integral[of a b] unfolding polynomial_def by auto
  thus ?thesis
    using poly_mult_monon'[OF polynomial_incl[OF assms(1)], of a n] assms(2) Cons
    unfolding poly_mult_const(1)[OF carrier_is_subring assms] by simp
qed

lemma poly_mult_one':
  assumes "set p \<subseteq> carrier R"
  shows "poly_mult [ \<one> ] p = normalize p" and "poly_mult p [ \<one> ] = normalize p"
proof -
  have "map2 (\<oplus>) (map ((\<otimes>) \<one>) p) (replicate (length p) \<zero>) = p"
    using assms by (induct p) (auto)
  thus "poly_mult [ \<one> ] p = normalize p" and "poly_mult p [ \<one> ] = normalize p"
    using poly_mult_comm[OF assms, of "[ \<one> ]"] by auto
qed

lemma poly_mult_one:
  assumes "subring K R" "polynomial K p"
  shows "poly_mult [ \<one> ] p = p" and "poly_mult p [ \<one> ] = p"
  using poly_mult_one'[OF polynomial_in_carrier[OF assms]] normalize_idem[OF assms(2)] by auto

lemma poly_mult_lead_coeff_aux:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" and "p1 \<noteq> []" and "p2 \<noteq> []"
  shows "(coeff (poly_mult p1 p2)) (degree p1 + degree p2) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
proof -
  have p1: "lead_coeff p1 \<in> carrier R - { \<zero> }" and p2: "lead_coeff p2 \<in> carrier R - { \<zero> }"
    using assms(2-5) lead_coeff_in_carrier[OF assms(1)] by (metis list.collapse)+

  have "(coeff (poly_mult p1 p2)) (degree p1 + degree p2) = 
        (\<Oplus> k \<in> {..((degree p1) + (degree p2))}.
          (coeff p1) k \<otimes> (coeff p2) ((degree p1) + (degree p2) - k))"
    using poly_mult_coeff[OF assms(2-3)[THEN polynomial_in_carrier[OF assms(1)]]] by simp
  also have " ... = (lead_coeff p1) \<otimes> (lead_coeff p2)"
  proof -
    let ?f = "\<lambda>i. (coeff p1) i \<otimes> (coeff p2) ((degree p1) + (degree p2) - i)"
    have in_carrier: "\<And>i. (coeff p1) i \<in> carrier R" "\<And>i. (coeff p2) i \<in> carrier R"
      using coeff_in_carrier assms by auto
    have "\<And>i. i < degree p1 \<Longrightarrow> ?f i = \<zero>"
      using coeff_degree[of p2] in_carrier by auto
    moreover have "\<And>i. i > degree p1 \<Longrightarrow> ?f i = \<zero>"
      using coeff_degree[of p1] in_carrier by auto
    moreover have "?f (degree p1) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
      using assms(4-5) lead_coeff_simp by simp 
    ultimately have "?f = (\<lambda>i. if degree p1 = i then (lead_coeff p1) \<otimes> (lead_coeff p2) else \<zero>)"
      using nat_neq_iff by auto
    thus ?thesis
      using add.finprod_singleton[of "degree p1" "{..((degree p1) + (degree p2))}"
                                     "\<lambda>i. (lead_coeff p1) \<otimes> (lead_coeff p2)"] p1 p2 by auto
  qed
  finally show ?thesis .
qed

lemma poly_mult_degree_eq:
  assumes "subring K R" "polynomial K p1" "polynomial K p2"
  shows "degree (poly_mult p1 p2) = (if p1 = [] \<or> p2 = [] then 0 else (degree p1) + (degree p2))"
proof (cases p1)
  case Nil thus ?thesis by simp
next
  case (Cons a p1') note p1 = Cons
  show ?thesis
  proof (cases p2)
    case Nil thus ?thesis
      using poly_mult_zero(2)[OF polynomial_in_carrier[OF assms(1-2)]] by simp
  next
    case (Cons b p2') note p2 = Cons
    have a: "a \<in> carrier R" and b: "b \<in> carrier R"
      using p1 p2 polynomial_in_carrier[OF assms(1-2)] polynomial_in_carrier[OF assms(1,3)] by auto
    have "(coeff (poly_mult p1 p2)) ((degree p1) + (degree p2)) = a \<otimes> b"
      using poly_mult_lead_coeff_aux[OF assms] p1 p2 by simp
    hence "(coeff (poly_mult p1 p2)) ((degree p1) + (degree p2)) \<noteq> \<zero>"
      using assms(2-3) integral[of a b] lead_coeff_in_carrier[OF assms(1)] p1 p2 by auto  
    moreover have "\<And>i. i > (degree p1) + (degree p2) \<Longrightarrow> (coeff (poly_mult p1 p2)) i = \<zero>"
    proof -
      have aux_lemma: "degree (poly_mult p1 p2) \<le> (degree p1) + (degree p2)"
      proof (induct p1)
        case Nil
        then show ?case by simp
      next
        case (Cons a p1)
        let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (degree (a # p1)) \<zero>)"
        have "poly_mult (a # p1) p2 = poly_add ?a_p2 (poly_mult p1 p2)" by simp
        hence "degree (poly_mult (a # p1) p2) \<le> max (degree ?a_p2) (degree (poly_mult p1 p2))"
          using poly_add_degree[of ?a_p2 "poly_mult p1 p2"] by simp
        also have " ... \<le> max ((degree (a # p1)) + (degree p2)) (degree (poly_mult p1 p2))"
          by auto
        also have " ... \<le> max ((degree (a # p1)) + (degree p2)) ((degree p1) + (degree p2))"
          using Cons by simp
        also have " ... \<le> (degree (a # p1)) + (degree p2)"
          by auto
        finally show ?case .
      qed
      fix i show "i > (degree p1) + (degree p2) \<Longrightarrow> (coeff (poly_mult p1 p2)) i = \<zero>"
        using coeff_degree aux_lemma by simp
    qed
    ultimately have "degree (poly_mult p1 p2) = degree p1 + degree p2"
      using degree_def'[OF poly_mult_closed[OF assms]]
      by (smt coeff_degree linorder_cases not_less_Least)
    thus ?thesis
      using p1 p2 by auto
  qed
qed

lemma poly_mult_integral:
  assumes "subring K R" "polynomial K p1" "polynomial K p2"
  shows "poly_mult p1 p2 = [] \<Longrightarrow> p1 = [] \<or> p2 = []"
proof (rule ccontr)
  assume A: "poly_mult p1 p2 = []" "\<not> (p1 = [] \<or> p2 = [])"
  hence "degree (poly_mult p1 p2) = degree p1 + degree p2"
    using poly_mult_degree_eq[OF assms] by simp
  hence "length p1 = 1 \<and> length p2 = 1"
    using A Suc_diff_Suc by fastforce
  then obtain a b where p1: "p1 = [ a ]" and p2: "p2 = [ b ]"
    by (metis One_nat_def length_0_conv length_Suc_conv)
  hence "a \<in> carrier R - { \<zero> }" and "b \<in> carrier R - { \<zero> }"
    using assms lead_coeff_in_carrier by auto
  hence "poly_mult [ a ] [ b ] = [ a \<otimes> b ]"
    using integral by auto
  thus False using A(1) p1 p2 by simp
qed

lemma poly_mult_lead_coeff:
  assumes "subring K R" "polynomial K p1" "polynomial K p2" and "p1 \<noteq> []" and "p2 \<noteq> []"
  shows "lead_coeff (poly_mult p1 p2) = (lead_coeff p1) \<otimes> (lead_coeff p2)"
proof -
  have "poly_mult p1 p2 \<noteq> []"
    using poly_mult_integral[OF assms(1-3)] assms(4-5) by auto
  hence "lead_coeff (poly_mult p1 p2) = (coeff (poly_mult p1 p2)) (degree p1 + degree p2)"
    using poly_mult_degree_eq[OF assms(1-3)] assms(4-5) by (metis coeff.simps(2) list.collapse)
  thus ?thesis
    using poly_mult_lead_coeff_aux[OF assms] by simp
qed

end (* of domain context. *)


subsection \<open>Algebraic Structure of Polynomials\<close>

definition univ_poly :: "('a, 'b) ring_scheme \<Rightarrow>'a set \<Rightarrow> ('a list) ring" ("_ [X]\<index>" 80)
  where "univ_poly R K =
           \<lparr> carrier = { p. polynomial\<^bsub>R\<^esub> K p },
                mult = ring.poly_mult R,
                 one = [ \<one>\<^bsub>R\<^esub> ],
                zero = [],
                 add = ring.poly_add R \<rparr>"


context domain
begin

lemma poly_mult_monon_assoc:
  assumes "set p \<subseteq> carrier R" "set q \<subseteq> carrier R" and "a \<in> carrier R"
    shows "poly_mult (poly_mult (monon a n) p) q =
           poly_mult (monon a n) (poly_mult p q)"
proof (induct n)
  case 0 thus ?case
    unfolding monon_def using poly_mult_semiassoc[OF assms] by (auto simp del: poly_mult.simps)
next
  case (Suc n)
  have "poly_mult (poly_mult (monon a (Suc n)) p) q =
        poly_mult (normalize ((poly_mult (monon a n) p) @ [ \<zero> ])) q"
    using poly_mult_append_zero[OF monon_in_carrier[OF assms(3), of n] assms(1)]
    unfolding monon_def by (auto simp del: poly_mult.simps simp add: replicate_append_same)
  also have " ... = normalize ((poly_mult (poly_mult (monon a n) p) q) @ [ \<zero> ])"
    using poly_mult_normalize[OF _ assms(2)] poly_mult_append_zero[OF _ assms(2)]
          poly_mult_in_carrier[OF monon_in_carrier[OF assms(3), of n] assms(1)] by auto
  also have " ... = normalize ((poly_mult (monon a n) (poly_mult p q)) @ [ \<zero> ])"
    using Suc by simp
  also have " ... = poly_mult (monon a (Suc n)) (poly_mult p q)"
    using poly_mult_append_zero[OF monon_in_carrier[OF assms(3), of n]
                                   poly_mult_in_carrier[OF assms(1-2)]]
    unfolding monon_def by (simp add: replicate_append_same)
  finally show ?case .
qed


context
  fixes K :: "'a set" assumes K: "subring K R"
begin

lemma univ_poly_is_monoid: "monoid (K[X])"
  unfolding univ_poly_def using poly_mult_one[OF K]
proof (auto simp add: K poly_add_closed poly_mult_closed one_is_polynomial monoid_def)
  fix p1 p2 p3
  let ?P = "poly_mult (poly_mult p1 p2) p3 = poly_mult p1 (poly_mult p2 p3)"

  assume A: "polynomial K p1" "polynomial K p2" "polynomial K p3"
  show ?P using polynomial_in_carrier[OF K A(1)]
  proof (induction p1)
    case Nil thus ?case by simp
  next
next
    case (Cons a p1) thus ?case
    proof (cases "a = \<zero>")
      assume eq_zero: "a = \<zero>"
      have p1: "set p1 \<subseteq> carrier R"
        using Cons(2) by simp
      have "poly_mult (poly_mult (a # p1) p2) p3 = poly_mult (poly_mult p1 p2) p3"
        using poly_mult_prepend_replicate_zero[OF p1 polynomial_in_carrier[OF K A(2)], of "Suc 0"]
              eq_zero by simp
      also have " ... = poly_mult p1 (poly_mult p2 p3)"
        using p1[THEN Cons(1)] by simp
      also have " ... = poly_mult (a # p1) (poly_mult p2 p3)"
        using poly_mult_prepend_replicate_zero[OF p1
              poly_mult_in_carrier[OF A(2-3)[THEN polynomial_in_carrier[OF K]]], of "Suc 0"] eq_zero
        by simp
      finally show ?thesis .
    next
      assume "a \<noteq> \<zero>" hence in_carrier:
        "set p1 \<subseteq> carrier R" "set p2 \<subseteq> carrier R" "set p3 \<subseteq> carrier R" "a \<in> carrier R - { \<zero> }"
        using A(2-3) polynomial_in_carrier[OF K] Cons by auto

      let ?a_p2 = "(map (\<lambda>b. a \<otimes> b) p2) @ (replicate (length p1) \<zero>)"
      have a_p2_in_carrier: "set ?a_p2 \<subseteq> carrier R"
        using in_carrier by auto

      have "poly_mult (poly_mult (a # p1) p2) p3 = poly_mult (poly_add ?a_p2 (poly_mult p1 p2)) p3"
        by simp
      also have " ... = poly_add (poly_mult ?a_p2 p3) (poly_mult (poly_mult p1 p2) p3)"
        using poly_mult_l_distr'[OF a_p2_in_carrier poly_mult_in_carrier[OF in_carrier(1-2)] in_carrier(3)] .
      also have " ... = poly_add (poly_mult ?a_p2 p3) (poly_mult p1 (poly_mult p2 p3))"
        using Cons(1)[OF in_carrier(1)] by simp
      also have " ... = poly_add (poly_mult (normalize ?a_p2) p3) (poly_mult p1 (poly_mult p2 p3))"
        using poly_mult_normalize[OF a_p2_in_carrier in_carrier(3)] by simp
      also have " ... = poly_add (poly_mult (poly_mult (monon a (length p1)) p2) p3)
                                 (poly_mult p1 (poly_mult p2 p3))"
        using poly_mult_monon'[OF in_carrier(2), of a "length p1"] in_carrier(4) by simp
      also have " ... = poly_add (poly_mult (a # (replicate (length p1) \<zero>)) (poly_mult p2 p3))
                                 (poly_mult p1 (poly_mult p2 p3))"
        using poly_mult_monon_assoc[of p2 p3 a "length p1"] in_carrier unfolding monon_def by simp
      also have " ... = poly_mult (poly_add (a # (replicate (length p1) \<zero>)) p1) (poly_mult p2 p3)"
        using poly_mult_l_distr'[of "a # (replicate (length p1) \<zero>)" p1 "poly_mult p2 p3"]
              poly_mult_in_carrier[OF in_carrier(2-3)] in_carrier by force
      also have " ... = poly_mult (a # p1) (poly_mult p2 p3)"
        using poly_add_monon[OF in_carrier(1) in_carrier(4)] unfolding monon_def by simp
      finally show ?thesis .
    qed
  qed
qed

declare poly_add.simps[simp del]

lemma univ_poly_is_abelian_monoid: "abelian_monoid (K[X])"
  unfolding univ_poly_def
  using poly_add_closed poly_add_zero zero_is_polynomial K
proof (auto simp add: abelian_monoid_def comm_monoid_def monoid_def comm_monoid_axioms_def)
  fix p1 p2 p3
  let ?c = "\<lambda>p. coeff p"
  assume A: "polynomial K p1" "polynomial K p2" "polynomial K p3"
  hence
    p1: "\<And>i. (?c p1) i \<in> carrier R" "set p1 \<subseteq> carrier R" and
    p2: "\<And>i. (?c p2) i \<in> carrier R" "set p2 \<subseteq> carrier R" and
    p3: "\<And>i. (?c p3) i \<in> carrier R" "set p3 \<subseteq> carrier R"
    using A[THEN polynomial_in_carrier[OF K]] coeff_in_carrier by auto
  have "?c (poly_add (poly_add p1 p2) p3) = (\<lambda>i. (?c p1 i \<oplus> ?c p2 i) \<oplus> (?c p3 i))"
    using poly_add_coeff[OF poly_add_in_carrier[OF p1(2) p2(2)] p3(2)]
          poly_add_coeff[OF p1(2) p2(2)] by simp
  also have " ... = (\<lambda>i. (?c p1 i) \<oplus> ((?c p2 i) \<oplus> (?c p3 i)))"
    using p1 p2 p3 add.m_assoc by simp
  also have " ... = ?c (poly_add p1 (poly_add p2 p3))"
    using poly_add_coeff[OF p1(2) poly_add_in_carrier[OF p2(2) p3(2)]]
          poly_add_coeff[OF p2(2) p3(2)] by simp
  finally have "?c (poly_add (poly_add p1 p2) p3) = ?c (poly_add p1 (poly_add p2 p3))" .
  thus "poly_add (poly_add p1 p2) p3 = poly_add p1 (poly_add p2 p3)"
    using coeff_iff_polynomial_cond poly_add_closed[OF K] A by meson
  show "poly_add p1 p2 = poly_add p2 p1"
    using poly_add_comm[OF p1(2) p2(2)] .
qed

lemma univ_poly_is_abelian_group: "abelian_group (K[X])"
proof -
  interpret abelian_monoid "K[X]"
    using univ_poly_is_abelian_monoid .
  show ?thesis
  proof (unfold_locales)
    show "carrier (add_monoid (K[X])) \<subseteq> Units (add_monoid (K[X]))"
      unfolding univ_poly_def Units_def
    proof (auto)
      fix p assume p: "polynomial K p"
      have "polynomial K [ \<ominus> \<one> ]"
        unfolding polynomial_def using r_neg subringE(3,5)[OF K] by force
      hence cond0: "polynomial K (poly_mult [ \<ominus> \<one> ] p)"
        using poly_mult_closed[OF K, of "[ \<ominus> \<one> ]" p] p by simp
      
      have "poly_add p (poly_mult [ \<ominus> \<one> ] p) = poly_add (poly_mult [ \<one> ] p) (poly_mult [ \<ominus> \<one> ] p)"
        using poly_mult_one[OF K p] by simp
      also have " ... = poly_mult (poly_add [ \<one> ] [ \<ominus> \<one> ]) p"
        using poly_mult_l_distr' polynomial_in_carrier[OF K p] by auto
      also have " ... = poly_mult [] p"
        using poly_add.simps[of "[ \<one> ]" "[ \<ominus> \<one> ]"]
        by (simp add: case_prod_unfold r_neg)
      also have " ... = []" by simp
      finally have cond1: "poly_add p (poly_mult [ \<ominus> \<one> ] p) = []" .

      have "poly_add (poly_mult [ \<ominus> \<one> ] p) p = poly_add (poly_mult [ \<ominus> \<one> ] p) (poly_mult [ \<one> ] p)"
        using poly_mult_one[OF K p] by simp
      also have " ... = poly_mult (poly_add [ \<ominus>  \<one> ] [ \<one> ]) p"
        using poly_mult_l_distr' polynomial_in_carrier[OF K p] by auto
      also have " ... = poly_mult [] p"
        using \<open>poly_mult (poly_add [\<one>] [\<ominus> \<one>]) p = poly_mult [] p\<close> poly_add_comm by auto
      also have " ... = []" by simp
      finally have cond2: "poly_add (poly_mult [ \<ominus> \<one> ] p) p = []" .

      from cond0 cond1 cond2 show "\<exists>q. polynomial K q \<and> poly_add q p = [] \<and> poly_add p q = []"
        by auto
    qed
  qed
qed

lemma univ_poly_is_ring: "ring (K[X])"
proof -
  interpret UP: abelian_group "K[X]" + monoid "K[X]"
    using univ_poly_is_abelian_group univ_poly_is_monoid .
  show ?thesis
    by (unfold_locales)
       (auto simp add: univ_poly_def poly_mult_r_distr[OF K] poly_mult_l_distr[OF K])
qed

lemma univ_poly_is_cring: "cring (K[X])"
proof -
  interpret UP: ring "K[X]"
    using univ_poly_is_ring .
  have "\<And>p q. \<lbrakk> p \<in> carrier (K[X]); q \<in> carrier (K[X]) \<rbrakk> \<Longrightarrow> p \<otimes>\<^bsub>K[X]\<^esub> q = q \<otimes>\<^bsub>K[X]\<^esub> p"
    unfolding univ_poly_def using poly_mult_comm polynomial_in_carrier[OF K] by auto
  thus ?thesis
    by unfold_locales auto
qed

lemma univ_poly_is_domain: "domain (K[X])"
proof -
  interpret UP: cring "K[X]"
    using univ_poly_is_cring .
  show ?thesis
    by (unfold_locales, auto simp add: univ_poly_def poly_mult_integral[OF K])
qed

declare poly_add.simps[simp]

lemma univ_poly_a_inv_def':
  assumes "p \<in> carrier (K[X])"
  shows "\<ominus>\<^bsub>K[X]\<^esub> p = map (\<lambda>a. \<ominus> a) p"
proof -
  have aux_lemma:
    "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> p \<oplus>\<^bsub>K[X]\<^esub> (map (\<lambda>a. \<ominus> a) p) = []"
    "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> (map (\<lambda>a. \<ominus> a) p) \<in> carrier (K[X])"
  proof -
    fix p assume p: "p \<in> carrier (K[X])"
    hence set_p: "set p \<subseteq> K"
      unfolding univ_poly_def using polynomial_incl by auto
    show "(map (\<lambda>a. \<ominus> a) p) \<in> carrier (K[X])"
    proof (cases "p = []")
      assume "p = []" thus ?thesis
        unfolding univ_poly_def polynomial_def by auto
    next
      assume not_nil: "p \<noteq> []"
      hence "lead_coeff p \<noteq> \<zero>"
        using p unfolding univ_poly_def polynomial_def by auto
      moreover have "lead_coeff (map (\<lambda>a. \<ominus> a) p) = \<ominus> (lead_coeff p)"
        using not_nil by (simp add: hd_map)
      ultimately have "lead_coeff (map (\<lambda>a. \<ominus> a) p) \<noteq> \<zero>"
        using hd_in_set local.minus_zero not_nil set_p subringE(1)[OF K] by force
      moreover have "set (map (\<lambda>a. \<ominus> a) p) \<subseteq> K"
        using set_p subringE(5)[OF K] by (induct p) (auto)
      ultimately show ?thesis
        unfolding univ_poly_def polynomial_def by simp
    qed

    have "map2 (\<oplus>) p (map (\<lambda>a. \<ominus> a) p) = replicate (length p) \<zero>"
      using set_p subringE(1)[OF K] by (induct p) (auto simp add: r_neg)
    thus "p \<oplus>\<^bsub>K[X]\<^esub> (map (\<lambda>a. \<ominus> a) p) = []"
      unfolding univ_poly_def using normalize_replicate_zero[of "length p" "[]"] by auto
  qed

  interpret UP: ring "K[X]"
    using univ_poly_is_ring .

  from aux_lemma
  have "\<And>p. p \<in> carrier (K[X]) \<Longrightarrow> \<ominus>\<^bsub>K[X]\<^esub> p = map (\<lambda>a. \<ominus> a) p"
    by (metis Nil_is_map_conv UP.add.inv_closed UP.l_zero UP.r_neg1 UP.r_zero UP.zero_closed)
  thus ?thesis
    using assms by simp
qed


subsection \<open>Long Division Theorem\<close>

lemma long_division_theorem:
  assumes "polynomial K p" and "polynomial K b" "b \<noteq> []"
     and "lead_coeff b \<in> Units (R \<lparr> carrier := K \<rparr>)"
  shows "\<exists>q r. polynomial K q \<and> polynomial K r \<and>
               p = (b \<otimes>\<^bsub>K[X]\<^esub> q) \<oplus>\<^bsub>K[X]\<^esub> r \<and> (r = [] \<or> degree r < degree b)"
    (is "\<exists>q r. ?long_division p q r")
  using assms(1)
proof (induct "length p" arbitrary: p rule: less_induct)
  case less thus ?case
  proof (cases p)
    case Nil
    hence "?long_division p [] []"
      using zero_is_polynomial poly_mult_zero[OF polynomial_in_carrier[OF K assms(2)]]
      by (simp add: univ_poly_def)
    thus ?thesis by blast
  next
    case (Cons a p') thus ?thesis
    proof (cases "length b > length p")
      assume "length b > length p"
      hence "p = [] \<or> degree p < degree b"
        by (meson diff_less_mono length_0_conv less_one not_le) 
      hence "?long_division p [] p"
        using poly_mult_zero(2)[OF polynomial_in_carrier[OF K assms(2)]]
              poly_add_zero(2)[OF K less(2)] zero_is_polynomial less(2)
        by (simp add: univ_poly_def)
      thus ?thesis by blast
    next
      interpret UP: cring "K[X]"
        using univ_poly_is_cring .

      assume "\<not> length b > length p"
      hence len_ge: "length p \<ge> length b" by simp
      obtain c b' where b: "b = c # b'"
        using assms(3) list.exhaust_sel by blast
      then obtain c' where c': "c' \<in> carrier R" "c' \<in> K" "c' \<otimes> c = \<one>" "c \<otimes> c' = \<one>"
        using assms(4) subringE(1)[OF K] unfolding Units_def by auto
      have c: "c \<in> carrier R" "c \<in> K" "c \<noteq> \<zero>" and a: "a \<in> carrier R" "a \<in> K" "a \<noteq> \<zero>"
        using less(2) assms(2) lead_coeff_not_zero subringE(1)[OF K] b Cons by auto
      hence lc: "c' \<otimes> (\<ominus> a) \<in> K - { \<zero> }"
        using subringE(5-6)[OF K] c' add.inv_solve_right integral_iff by fastforce

      let ?len = "length"
      define s where "s = monon (c' \<otimes> (\<ominus> a)) (?len p - ?len b)"
      hence s: "polynomial K s" "s \<noteq> []" "degree s = ?len p - ?len b" "length s \<ge> 1"
        using monon_is_polynomial[OF K lc] unfolding monon_def by auto
      hence is_polynomial: "polynomial K (p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s))"
        using poly_add_closed[OF K less(2) poly_mult_closed[OF K assms(2), of s]]
        by (simp add: univ_poly_def)

      have "lead_coeff (b \<otimes>\<^bsub>K[X]\<^esub> s) = \<ominus> a"
        using poly_mult_lead_coeff[OF K assms(2) s(1) assms(3) s(2)] c c' a
        unfolding b s_def monon_def univ_poly_def by (auto simp del: poly_mult.simps, algebra)
      then obtain s' where s': "b \<otimes>\<^bsub>K[X]\<^esub> s = (\<ominus> a) # s'"
        using poly_mult_integral[OF K assms(2) s(1)] assms(2-3) s(2)
        by (simp add: univ_poly_def, metis hd_Cons_tl)
      moreover have "degree p = degree (b \<otimes>\<^bsub>K[X]\<^esub> s)"
        using poly_mult_degree_eq[OF K assms(2) s(1)] assms(3) s(2-4) len_ge b Cons
        by (auto simp add: univ_poly_def)
      hence "?len p = ?len (b \<otimes>\<^bsub>K[X]\<^esub> s)"
        unfolding Cons s' by simp
      hence "?len (p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)) < ?len p"
        unfolding Cons s' using a normalize_length_le[of "map2 (\<oplus>) p' s'"]
        by (auto simp add: univ_poly_def r_neg)
      then obtain q' r' where l_div: "?long_division (p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)) q' r'"
        using less(1)[OF _ is_polynomial] by blast

      have in_carrier:
         "p \<in> carrier (K[X])"  "b \<in> carrier (K[X])" "s \<in> carrier (K[X])"
        "q' \<in> carrier (K[X])" "r' \<in> carrier (K[X])"
        using l_div assms less(2) s unfolding univ_poly_def by auto
      have "(p \<oplus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)) \<ominus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s) =
          ((b \<otimes>\<^bsub>K[X]\<^esub> q') \<oplus>\<^bsub>K[X]\<^esub> r') \<ominus>\<^bsub>K[X]\<^esub> (b \<otimes>\<^bsub>K[X]\<^esub> s)"
        using l_div by simp
      hence "p = (b \<otimes>\<^bsub>K[X]\<^esub> (q' \<ominus>\<^bsub>K[X]\<^esub> s)) \<oplus>\<^bsub>K[X]\<^esub> r'"
        using in_carrier by algebra
      moreover have "q' \<ominus>\<^bsub>K[X]\<^esub> s \<in> carrier (K[X])"
        using in_carrier by algebra
      hence "polynomial K (q' \<ominus>\<^bsub>K[X]\<^esub> s)"
        unfolding univ_poly_def by simp
      ultimately have "?long_division p (q' \<ominus>\<^bsub>K[X]\<^esub> s) r'"
        using l_div by auto
      thus ?thesis by blast
    qed
  qed
qed

end (* of fixed K context. *)

end (* of domain context. *)

lemma (in field) field_long_division_theorem:
  assumes "subfield K R" "polynomial K p" and "polynomial K b" "b \<noteq> []"
  shows "\<exists>q r. polynomial K q \<and> polynomial K r \<and>
               p = (b \<otimes>\<^bsub>K[X]\<^esub> q) \<oplus>\<^bsub>K[X]\<^esub> r \<and> (r = [] \<or> degree r < degree b)"
  using long_division_theorem[OF subfieldE(1)[OF assms(1)] assms(2-4)] assms(3-4)
        subfield.subfield_Units[OF assms(1)] lead_coeff_not_zero[of K "hd b" "tl b"]
  by simp

end
