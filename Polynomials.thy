(* ************************************************************************** *)
(* Title:      Polynomials.thy                                                     *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Polynomials
  imports Ring (* "HOL-Library.Multiset" *)

begin

inductive
  polynomial :: "('k, 'c) ring_scheme \<Rightarrow> (('k \<times> nat) list) \<Rightarrow> bool"
  for R where
    zero: "polynomial R []"
  | pow : "k \<in> carrier R - { \<zero>\<^bsub>R\<^esub> } \<Longrightarrow> polynomial R [(k, n)]"
  | ext : "\<lbrakk> polynomial R ((k1, n1) # p); k2 \<in> carrier R - { \<zero>\<^bsub>R\<^esub> }; n2 > n1 \<rbrakk> \<Longrightarrow>
             polynomial R ((k2, n2) # (k1, n1) # p)"

fun p_add :: "('k, 'c) ring_scheme \<Rightarrow> ('k \<times> nat) list \<Rightarrow> ('k \<times> nat) list \<Rightarrow> ('k \<times> nat) list"
  where
    "p_add R [] p2 = p2"
  | "p_add R p1 [] = p1"
  | "p_add R ((k1, n1) # p1) ((k2, n2) # p2) =
       (if n1 > n2 then (k1, n1) # (p_add R p1 ((k2, n2) # p2))
        else if n2 > n1 then (k2, n2) # (p_add R ((k1, n1) # p1) p2)
        else if k1 \<oplus>\<^bsub>R\<^esub> k2 = \<zero>\<^bsub>R\<^esub> then p_add R p1 p2
        else (k1 \<oplus>\<^bsub>R\<^esub> k2, n1) # (p_add R p1 p2))"

fun p_mult_aux :: "('k, 'c) ring_scheme \<Rightarrow> ('k \<times> nat) \<Rightarrow> ('k \<times> nat) list \<Rightarrow> ('k \<times> nat) list"
  where
    "p_mult_aux R (k1, n1) [] = []"
  | "p_mult_aux R (k1, n1) ((k2, n2) # p2) =
       (if k1 \<otimes>\<^bsub>R\<^esub> k2 = \<zero>\<^bsub>R\<^esub> then p_mult_aux R (k1, n1) p2
        else (k1 \<otimes>\<^bsub>R\<^esub> k2, n1 + n2) # (p_mult_aux R (k1, n1) p2))"

fun p_mult :: "('k, 'c) ring_scheme \<Rightarrow> ('k \<times> nat) list \<Rightarrow> ('k \<times> nat) list \<Rightarrow> ('k \<times> nat) list"
  where
    "p_mult R [] p2 = []"
  | "p_mult R ((k1, n1) # p1) p2 = p_add R (p_mult_aux R (k1, n1) p2) (p_mult R p1 p2)"

fun norm ::  "('k, 'c) ring_scheme \<Rightarrow> ('k \<times> nat) list \<Rightarrow> ('k \<times> nat) list"
  where
    "norm R [] = []"
  | "norm R ((k, n) # p) = (if k = \<zero>\<^bsub>R\<^esub> then (norm R p) else (k, n) # (norm R p))"

fun degree :: "('k \<times> nat) list \<Rightarrow> nat"
  where "degree [] = 0" | "degree ((_, n) # _) = n"



subsection \<open>Basic Properties\<close>

lemma drop_polynomial: "polynomial R p \<Longrightarrow> polynomial R (drop (i :: nat) p)"
proof (induct p arbitrary: i rule: polynomial.induct)
  case zero thus ?case
    using polynomial.zero by simp
next
  case pow
  have "i = 0 \<or> i > 0" by blast
  thus ?case
    using polynomial.zero polynomial.pow[OF pow] by auto
next
  case (ext k1 n1 p k2 n2) show ?case
  proof (cases)
    assume "i = 0" thus ?case
      using polynomial.ext[OF ext(1) ext(3-4)] by simp
  next
    assume "i \<noteq> 0" then obtain k where "i = Suc k"
      using Suc_pred' by blast
    thus ?case using ext(2)[of k] by simp
  qed
qed 

lemma tl_polynomial: "polynomial R p \<Longrightarrow> polynomial R (tl p)"
  using drop_polynomial[of R p "Suc 0"] drop_Suc[of 0 p] by simp

lemma coeff_in_carrier: "polynomial R ((k, n) # p) \<Longrightarrow> k \<in> carrier R - { \<zero>\<^bsub>R\<^esub> }"
  by (cases rule: polynomial.cases[of R "(k, n) # p"]) auto

lemma coeff_in_carrier_arbitrary:
  assumes "i < length p"
  shows "polynomial R p \<Longrightarrow> fst (p ! i) \<in> carrier R - { \<zero>\<^bsub>R\<^esub> }"
  using coeff_in_carrier[of R "fst (p ! i)" "snd (p ! i)" "drop (Suc i) p"]
        assms by (simp add: drop_polynomial Cons_nth_drop_Suc)

lemma constant_polynomial: "polynomial R ((k, 0) # p) \<Longrightarrow> p = []"
  by (cases rule: polynomial.cases[of R "(k, 0) # p"]) auto

lemma degree_ge: "polynomial R p \<Longrightarrow> degree p \<ge> degree (tl p)"
  by (induct p rule: polynomial.induct) (auto)

lemma degree_ze: "\<lbrakk> polynomial R p; degree p = degree (tl p) \<rbrakk> \<Longrightarrow> degree p = 0"
  by (induct p rule: polynomial.induct) (auto)

lemma degree_gt: "\<lbrakk> polynomial R p; degree p > 0 \<rbrakk> \<Longrightarrow> degree p > degree (tl p)"
  by (induct p rule: polynomial.induct) (auto)

lemma pow_list_ge: "polynomial R p \<Longrightarrow> \<forall>t \<in> set p. degree p \<ge> snd t"
  by (induct p rule: polynomial.induct) (auto)

lemma pow_list_gt: "\<lbrakk> polynomial R p; degree p > 0 \<rbrakk> \<Longrightarrow> \<forall>t \<in> set (tl p). degree p > snd t"
  using degree_gt pow_list_ge tl_polynomial by fastforce

lemma pow_list_le: "polynomial R p \<Longrightarrow> \<forall>t \<in> set p. snd (last p) \<le> snd t"
  by (induct p rule: polynomial.induct) (auto)

lemma card_pow_set: "polynomial R p \<Longrightarrow> card (snd ` (set p)) = length p"
proof (induct p rule: polynomial.induct)
  case zero thus ?case by simp
  case pow  thus ?case by simp
next
  case (ext k1 n1 p k2 n2)
  have "n2 \<notin> snd ` (set ((k1, n1) # p))"
    using pow_list_gt[OF polynomial.ext[OF ext(1) ext(3-4)]] ext.hyps(4) by auto
  thus ?case using ext.hyps(2) by simp
qed

lemma degree_ext:
  "\<lbrakk> polynomial R p; k \<in> carrier R - { \<zero>\<^bsub>R\<^esub> }; n > degree p \<rbrakk> \<Longrightarrow> polynomial R ((k, n) # p)"
  by (induct p rule: polynomial.induct)
     (auto simp add: polynomial.ext polynomial.pow polynomial.zero)

lemma p_add_degree:
  assumes "polynomial R p1" "polynomial R p2"
  shows "degree (p_add R p1 p2) \<le> max (degree p1) (degree p2)" using assms
proof (induct p1 p2 rule: p_add.induct)
  case 1 thus ?case by simp
  case 2 thus ?case by simp
next
  case (3 R k1 n1 p1 k2 n2 p2)
  have ?case if "n1 > n2"
    using that by simp
  moreover have ?case if "n2 > n1"
    using that by simp
  moreover have ?case if "n1 = n2"
    using degree_ge[OF 3(6)] tl_polynomial[OF 3(6)]
          degree_ge[OF 3(5)] tl_polynomial[OF 3(5)] that 3(3) by auto
  ultimately show ?case by auto
qed

lemma p_mult_zero: "p_mult R p [] = []"
  by (induct p) (auto)

lemma p_add_zero [simp]: "p_add R p [] = p"
  apply (cases "p = []")
  apply auto
  apply (metis list.exhaust p_add.simps(2))
  done

lemma p_add_degreeI:
  assumes "degree p1 > degree p2"
    shows "degree (p_add R p1 p2) = degree p1"
proof -
  have not_empty: "p1 \<noteq> []"
    using assms by auto
  show "degree (p_add R p1 p2) = degree p1"
  proof (cases)
    assume "p2 = []" thus ?thesis
      using assms by auto
  next
    assume "p2 \<noteq> []"
    then obtain p1' p2' k1 k2
      where "p1 = (k1, degree p1) # p1'"
        and "p2 = (k2, degree p2) # p2'"
      by (metis degree.cases degree.simps(2) not_empty)
    thus ?thesis
      using assms by (metis degree.simps(2) p_add.simps(3))
  qed
qed

lemma p_mult_aux_degree_weak:
  "polynomial R p2  \<Longrightarrow> degree (p_mult_aux R t p2) \<le> (snd t) + degree p2"
proof (induct p2 rule: p_mult_aux.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case
    using tl_polynomial[OF 2(3)] degree_ge[OF 2(3)] by auto
qed

lemma (in domain) p_mult_aux_degree:
  assumes "polynomial R p" and "p \<noteq> []" and "k \<in> carrier R - { \<zero> }"
  shows "degree (p_mult_aux R (k, n) p) = n + degree p"
proof -
  { fix p :: "('a \<times> nat) list" and t :: "'a \<times> nat"
    assume "polynomial R p" "p \<noteq> []" "fst t \<in> carrier R - { \<zero> }"
    hence "degree (p_mult_aux R t p) = snd t + degree p"
      using domain_axioms
    proof (induct p rule: p_mult_aux.induct)
      case 1 thus ?case by simp
    next
      case (2 R k1 n1 k2 n2 p2)
      then show ?case
        using coeff_in_carrier[OF 2(3)] domain.integral_iff[OF 2(6)] by auto
    qed }
  thus ?thesis
    using assms by auto
qed

lemma (in domain) p_mult_degree:
  assumes "polynomial R p1" "polynomial R p2"
  shows "degree (p_mult R p1 p2) =
           (if p1 = [] \<or> p2 = [] then 0 else (degree p1) + (degree p2))"
proof -
  { fix p1 p2 assume "polynomial R p1" "polynomial R p2" "p1 \<noteq> []" "p2 \<noteq> []"
    hence "degree (p_mult R p1 p2) = (degree p1) + (degree p2)" using domain_axioms
    proof (induct p1 p2 rule: p_mult.induct)
      case 1 thus ?case by simp
    next
      case (2 R k1 n1 p1 p2) show ?case
      proof (cases)
        assume "p1 = []" thus ?case
          using domain.p_mult_aux_degree[OF 2(6) 2(3) 2(5) coeff_in_carrier[OF 2(2)], of n1] by simp 
      next
        assume A: "p1 \<noteq> []"
        have "n1 > degree p1"
        proof (rule ccontr)
          assume "\<not> n1 > degree p1"
          hence "n1 = degree p1"
            using degree_ge[OF 2(2)] by simp
          hence "n1 = 0"
            using degree_ze[OF 2(2)] by simp
          hence "p1 = []"
            using 2(2) by (simp add: constant_polynomial)
          thus False using A by simp 
        qed
        moreover have "degree (p_mult_aux R (k1, n1) p2) = n1 + degree p2"
          using domain.p_mult_aux_degree[OF 2(6) 2(3) 2(5) coeff_in_carrier[OF 2(2)], of n1] by simp
        moreover have "degree (p_mult R p1 p2) = degree p1 + degree p2"
          using "2.hyps" A 2(5) 2(3) tl_polynomial[OF 2(2)] 2(6) by simp
        ultimately show ?case
          using p_add_degreeI[of "p_mult R p1 p2" "p_mult_aux R (k1, n1) p2" R] by simp
      qed
    qed }

  thus ?thesis
    using assms p_mult_zero[of R p1] by auto
qed



subsection \<open>\<close>

fun supp :: "('k, 'c) ring_scheme \<Rightarrow> (('k \<times> nat) list) \<Rightarrow> (nat \<Rightarrow> 'k)"
  where
    "supp R [] = (\<lambda>a. \<zero>\<^bsub>R\<^esub>)"
  | "supp R ((k, n) # p) = (\<lambda>i. if i = n then k else (supp R p) i)"

lemma (in ring) supp_img_in_carrier: "polynomial R p \<Longrightarrow> (supp R p) ` UNIV \<subseteq> carrier R"
  by (induct p rule: polynomial.induct) (auto)

lemma supp_bounded1: "polynomial R p \<Longrightarrow> i > degree p \<Longrightarrow> (supp R) p i = \<zero>\<^bsub>R\<^esub>"
  by (induct p rule: polynomial.induct) (auto simp add: degree_ge tl_polynomial)

lemma supp_bounded2: "polynomial R p \<Longrightarrow> i < snd (last p) \<Longrightarrow> (supp R) p i = \<zero>\<^bsub>R\<^esub>"
proof (induct p rule: polynomial.induct)
  case zero thus ?case by simp
next
  case pow  thus ?case by simp
next
  case (ext k1 n1 p k2 n2)
  have "n2 > snd (last ((k1, n1) # p))"
    using pow_list_gt[OF polynomial.ext[OF ext(1) ext(3-4)]] ext(4) by simp
  moreover have "i < snd (last ((k1, n1) # p))"
    using ext(5) by simp
  ultimately show ?case
    using ext by auto
qed

lemma supp_bounded3: "polynomial R ((k, n) # p) \<Longrightarrow> i \<ge> n \<Longrightarrow> (supp R) p i = \<zero>\<^bsub>R\<^esub>"
proof (cases)
  assume "p = []" thus ?thesis by simp
next
  assume A: "p \<noteq> []" "polynomial R ((k, n) # p)" "i \<ge> n"
  hence "n > degree p"
    using constant_polynomial[of R k p] degree_gt[OF A(2)] by auto 
  thus ?thesis
    using supp_bounded1[OF tl_polynomial[OF A(2)]] A(3) by simp
qed

lemma supp_set:
  assumes "polynomial R p"
  shows "{ i. (supp R) p i \<noteq> \<zero>\<^bsub>R\<^esub> } = set (map snd p)" (is "?supp p = _")
  using assms
proof (induct p rule: polynomial.induct)
  case zero thus ?case by simp
  case pow  thus ?case by simp
next
  case (ext k1 n1 p k2 n2)
  have "?supp ((k2, n2) # (k1, n1) # p) = insert n2 (?supp ((k1, n1) # p))"
    using ext(3) supp_bounded1[OF polynomial.ext[OF ext(1) ext(3-4)]] by auto
  thus ?case
    using ext(2) by auto
qed

lemma supp_coeff:
  assumes "polynomial R p"
  shows "map (supp R p) (map snd p) = map fst p" using assms
proof (induct p rule: polynomial.induct)
  case zero thus ?case by simp
  case pow  thus ?case by simp
next
  case ext  thus ?case
    using pow_list_gt[OF polynomial.ext[OF ext(1) ext(3-4)]] by auto
qed

lemma supp_iff:
  assumes "polynomial R p1" "polynomial R p2"
  shows "p1 = p2 \<longleftrightarrow> (supp R) p1 = (supp R) p2"
proof
  assume "p1 = p2" thus "(supp R) p1 = (supp R) p2"
    by simp
next
  { fix p1 p2
    assume p1: "polynomial R p1"
       and p2: "polynomial R p2"
       and set_eq: "set (map snd p1) = set (map snd p2)"
    hence  len_eq: "length p1 = length p2"
      using card_pow_set[OF p1] card_pow_set[OF p2] by simp
    have "(map snd p1) = (map snd p2)"
      using p1 p2 set_eq len_eq
    proof (induct p1 arbitrary: p2 rule: polynomial.induct)
      case zero thus ?case by simp
    next
      case pow  thus ?case
        by (cases rule: polynomial.cases[OF pow(2)]) (auto)
    next
      case (ext k1 n1 p1 k2 n2) thus ?case
      proof (cases rule: polynomial.cases[OF ext(5)])
        case 1 thus ?thesis
          using ext(7) by auto
      next
        case 2 thus ?thesis
          using ext(7) by auto
      next
        case (3 k1' n1' p2' k2' n2')
        define coeff_set :: "('a \<times> nat) list \<Rightarrow> nat set"
        where "coeff_set = (\<lambda>p. set (map snd p))"
        hence finite_set: "\<And>p. finite (coeff_set p)" by auto

        have n2': "\<And>c. c \<in> coeff_set ((k1', n1') # p2') \<Longrightarrow> n2' > c" unfolding coeff_set_def
          using pow_list_gt[OF polynomial.ext[OF 3(2-4)]] 3(4) by auto
        moreover
        have n2: "\<And>c. c \<in> coeff_set ((k1, n1) # p1) \<Longrightarrow> n2 > c" unfolding coeff_set_def
          using pow_list_gt[OF polynomial.ext[OF ext(1) ext(3-4)]] ext(4) by auto
        moreover have coeff_set_eq:
          "insert n2' (coeff_set ((k1', n1') # p2')) = insert n2 (coeff_set ((k1, n1) # p1))"
          using ext(6) 3(1) unfolding coeff_set_def by simp
        ultimately have eq: "n2' = n2" by fastforce
        hence "coeff_set ((k1', n1') # p2') = coeff_set ((k1, n1) # p1)"
          using coeff_set_eq n2 n2' by (metis Diff_insert_absorb less_irrefl)
        then show ?thesis unfolding coeff_set_def
          using ext(2)[OF 3(2)] eq ext(7) 3(1) by auto
      qed 
    qed } note aux_lemma = this
  
  assume same_supp: "(supp R) p1 = (supp R) p2"
  hence "set (map snd p1) = set (map snd p2)"
    using supp_set[OF assms(1)] supp_set[OF assms(2)] by auto
  hence fst_eq: "map snd p1 = map snd p2"
    using aux_lemma[OF assms] by simp
  hence snd_eq: "map fst p1 = map fst p2"
    using supp_coeff[OF assms(1)] supp_coeff[OF assms(2)] same_supp by auto
  show "p1 = p2"
    using fst_eq snd_eq by (simp add: pair_list_eqI) 
qed

lemma (in ring) p_add_is_polynomial:
  assumes "polynomial R p1" "polynomial R p2"
  shows "polynomial R (p_add R p1 p2)" using assms ring_axioms
proof (induct p1 p2 rule: p_add.induct)
  case 1 thus ?case by simp
  case 2 thus ?case by simp
next
  case (3 R k1 n1 p1 k2 n2 p2)
  have ?case if "n1 = n2" "k1 \<oplus>\<^bsub>R\<^esub> k2 = \<zero>\<^bsub>R\<^esub>"
    using 3(3) 3(7) that tl_polynomial[OF 3(6)] tl_polynomial[OF 3(5)] by simp

  moreover have ?case if "n1 = n2" "k1 \<oplus>\<^bsub>R\<^esub> k2 \<noteq> \<zero>\<^bsub>R\<^esub>"
  proof -
    have in_carr: "k1 \<oplus>\<^bsub>R\<^esub> k2 \<in> carrier R - { \<zero>\<^bsub>R\<^esub> }"
      using coeff_in_carrier[OF 3(5)] coeff_in_carrier[OF 3(6)] that(2)
      by (simp add: ring.ring_simprules(1)[OF 3(7)])
    show ?thesis
    proof (cases)
      assume "n1 = 0" 
      hence "p1 = []" "p2 = []"
        using constant_polynomial[of R k1 p1]
              constant_polynomial[of R k2 p2] 3(5-6) that(1) by auto
      thus ?thesis
        using \<open>n1 = 0\<close> polynomial.pow[OF in_carr, of 0] that by auto
    next
      assume "n1 \<noteq> 0"
      hence "n1 > degree p1" "n2 > degree p2"
        using that degree_gt[OF 3(5)] degree_gt[OF 3(6)] by auto
      moreover have IH: "polynomial R (p_add R p1 p2)"
        using 3(4) that tl_polynomial[OF 3(5)] tl_polynomial[OF 3(6)] 3(7) by auto 
      ultimately show ?case
        using that degree_ext[OF IH in_carr, of n1] p_add_degree[of R p1 p2]
              tl_polynomial[OF 3(5)] tl_polynomial[OF 3(6)] 3(4) 3(7) by auto
    qed
  qed

  moreover have ?case if "n1 > n2"
  proof -
    have "polynomial R (p_add R p1 ((k2, n2) # p2))"
      using 3(1)[OF that] 3(6) tl_polynomial[OF 3(5)] 3(7) by simp
    moreover have "degree (p_add R p1 ((k2, n2) # p2)) < n1"
      using p_add_degree[OF tl_polynomial[OF 3(5)] 3(6)] degree_gt[OF 3(5)] that by force
    ultimately show ?thesis
      using degree_ext[of R "p_add R p1 ((k2, n2) # p2)" k1 n1]
            coeff_in_carrier[OF 3(5)] that by simp
  qed

  moreover have ?case if "n2 > n1"
  proof -
    have "polynomial R (p_add R ((k1, n1) # p1) p2)"
      using 3(2) 3(5) tl_polynomial[OF 3(6)] that 3(7) by simp
    moreover have "degree (p_add R ((k1, n1) # p1) p2) < n2"
      using p_add_degree[OF 3(5) tl_polynomial[OF 3(6)]] degree_gt[OF 3(6)] that by force
    ultimately show ?thesis
      using degree_ext[of R "p_add R ((k1, n1) # p1) p2" k2 n2]
            coeff_in_carrier[OF 3(6)] that by simp
  qed
  
  ultimately show ?case by auto
qed

lemma (in ring) p_mult_is_polynomial:
  assumes "polynomial R p1" "polynomial R p2"
  shows "polynomial R (p_mult R p1 p2)"
  using assms ring_axioms
proof (induct p1 p2 rule: p_mult.induct)
  case 1 thus ?case by simp
next
  case (2 R k1 n1 p1 p2)
  then interpret ring R
    by simp
  have aux_lemma: "polynomial R (p_mult_aux R (k1, n1) p2)"
    using 2(3) coeff_in_carrier[OF 2(2)]
  proof (induct p2 rule: polynomial.induct)
    case zero thus ?case
      by (simp add: polynomial.zero)
  next
    case pow  thus ?case
      by (simp add: polynomial.zero polynomial.pow)
  next
    case (ext k1' n1' p2 k2' n2')
    have ?case if "k1 \<otimes>\<^bsub>R\<^esub> k2' = \<zero>\<^bsub>R\<^esub>"
      using that ext(2)[OF ext(5)] by simp
    moreover have ?case if "k1 \<otimes>\<^bsub>R\<^esub> k2' \<noteq> \<zero>\<^bsub>R\<^esub>"
      using that ext p_mult_aux_degree_weak[OF ext(1), of "(k1, n1)"]
            degree_ext[of R "p_mult_aux R (k1, n1) ((k1', n1') # p2)" "k1 \<otimes>\<^bsub>R\<^esub> k2'" "n1 + n2'"]
      by auto
    ultimately show ?case by auto
  qed
  show ?case
    using tl_polynomial[OF 2(2)] p_add_is_polynomial[OF aux_lemma] 2 by auto
qed

corollary (in ring) p_mult_aux_is_polynomial:
  assumes "k \<in> carrier R" "polynomial R p"
  shows "polynomial R (p_mult_aux R (k, n) p)"
proof (cases)
  assume "k = \<zero>"
  hence "p_mult_aux R (k, n) p = []"
    using assms ring_axioms
  proof (induct p)
    case Nil thus ?case by simp
  next
    case (Cons a p)
    hence "k \<otimes>\<^bsub>R\<^esub> fst a = \<zero>\<^bsub>R\<^esub>"
      using coeff_in_carrier[of R "fst a" "snd a" p] ring.ring_simprules(24)[OF Cons(5)] by auto 
    then show ?case
      using tl_polynomial[OF Cons(4)] Cons
      by (metis list.sel(3) p_mult_aux.simps(2) prod.collapse)
  qed
  thus ?thesis
    using polynomial.zero by simp
next
  assume "k \<noteq> \<zero>" thus ?thesis
    using p_mult_is_polynomial[of "[(k, n)]" p] assms polynomial.pow[of k R n] by auto
qed


lemma (in ring) supp_add:
  assumes "polynomial R p1" "polynomial R p2"
  shows "supp R (p_add R p1 p2) = (\<lambda>i. ((supp R p1) i) \<oplus> ((supp R p2) i))"
  using ring_axioms assms
proof (induct R p1 p2 rule: p_add.induct)
  case (1 R p2) thus ?case
    using ring.supp_img_in_carrier[OF 1(1) 1(3)]
    by (simp add: image_subset_iff ring.ring_simprules(8))
next
  case (2 R v va) thus ?case
    using ring.supp_img_in_carrier[OF 2(1-2)]
    by (simp add: image_subset_iff ring.ring_simprules(15))
next
  case (3 R k1 n1 p1 k2 n2 p2)
  from 3(5) interpret ring R .
  have p1: "polynomial R p1" and p2: "polynomial R p2"
    using tl_polynomial[OF 3(6)] tl_polynomial[OF 3(7)] by auto

  have ?case if "n1 = n2" "k1 \<oplus>\<^bsub>R\<^esub> k2 \<noteq> \<zero>\<^bsub>R\<^esub>"
    using 3(4) that p1 p2 is_ring by auto

  moreover have ?case if "n1 > n2"
    using 3(1)[OF that is_ring p1 3(7)] that supp_bounded1[OF p2, of n1]
          degree_ge[OF 3(7)] coeff_in_carrier[OF 3(6)] by auto

  moreover have ?case if "n2 > n1"
    using 3(2) that is_ring p2 3(6) supp_bounded1[OF p1, of n2]
          degree_ge[OF 3(6)] coeff_in_carrier[OF 3(7)] by auto

  moreover have ?case if "n1 = n2" "k1 \<oplus>\<^bsub>R\<^esub> k2 = \<zero>\<^bsub>R\<^esub>"
  proof (cases)
    assume "n1 = 0"
    hence "p1 = []" "p2 = []"
      using constant_polynomial[of R k1 p1] 3(6)
            constant_polynomial[of R k2 p2] 3(7) that(1) by auto
    thus ?case
      using 3(3) that p1 p2 is_ring by auto
  next
    assume "n1 \<noteq> 0"
    hence "n1 > 0" "n2 > 0"
      using that(1) by simp+
    hence "n1 > degree (p_add R p1 p2)"
      using p_add_degree[OF p1 p2] degree_gt[OF 3(6)] degree_gt[OF 3(7)] that(1) by auto
    thus ?case
      using 3(3) that p1 p2 is_ring supp_bounded1[OF p_add_is_polynomial[OF p1 p2]] by auto
  qed

  ultimately show ?case by auto
qed

lemma p_mult_aux_eq_map_and_norm:
  "p_mult_aux R (k, n) p = norm R (map (\<lambda>(k', n'). (k \<otimes>\<^bsub>R\<^esub> k', n + n')) p)"
proof -
  define t where "t = (k, n)"
  have "p_mult_aux R t p = norm R (map (\<lambda>(k', n'). (fst t \<otimes>\<^bsub>R\<^esub> k', snd t + n')) p)"
    by (induct p rule: p_mult_aux.induct) (auto)
  thus ?thesis using t_def by simp
qed

lemma norm_cons: "polynomial R p \<Longrightarrow> p = norm R p"
proof (induct p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
    using coeff_in_carrier[of R "fst a" "snd a" p] tl_polynomial[OF Cons(2)]
             norm.simps(2)[of R "fst a" "snd a" p] by auto
qed

lemma (in ring) supp_mult_aux:
  assumes "polynomial R p" "k \<in> carrier R"
  shows "supp R (p_mult_aux R (k, n) p) =
           (\<lambda>i. if i \<ge> n then k \<otimes> (supp R p) (i - n) else \<zero>\<^bsub>R\<^esub>)"
proof -
  { fix t :: "'a \<times> nat"
    assume "fst t \<in> carrier R"
    hence "supp R (p_mult_aux R t p) =
             (\<lambda>i. if i \<ge> (snd t) then (fst t) \<otimes> (supp R p) (i - (snd t)) else \<zero>\<^bsub>R\<^esub>)"
      using ring_axioms assms(1)
    proof (induct p rule: p_mult_aux.induct)
      case 1 thus ?case
        using ring.ring_simprules(25)[OF 1(2)] by auto
    next
      case (2 R k1 n1 k2 n2 p2)
      then interpret ring R by simp

      have p2: "polynomial R p2"
        using tl_polynomial[OF 2(5)] by simp

      have ?case if "k1 \<otimes>\<^bsub>R\<^esub> k2 = \<zero>\<^bsub>R\<^esub>" "p2 = []"
        using that 2(3) by auto

      moreover have ?case (is "?f1 = ?f2") if "k1 \<otimes>\<^bsub>R\<^esub> k2 = \<zero>\<^bsub>R\<^esub>" "p2 \<noteq> []"
      proof -
        define f1 f2 where "f1 = ?f1" and "f2 = ?f2"
        have "n2 > degree p2"
          using that(2) constant_polynomial[of R k2 p2] degree_gt[OF 2(5)] 2(5) neq0_conv by auto 
        hence "\<And>i. i = n1 + n2 \<Longrightarrow> f1 i = f2 i" unfolding f1_def f2_def
          using that 2(3-5) 2(1) p2 supp_bounded1[OF p2] by auto
        moreover have "\<And>i. i \<noteq> n1 + n2 \<Longrightarrow> f1 i = f2 i" unfolding f1_def f2_def
          using that 2(3-5) 2(1) p2 by auto
        ultimately have "f1 = f2" by blast
        thus ?thesis unfolding f1_def f2_def by simp
      qed
          
      moreover have ?case if "k1 \<otimes>\<^bsub>R\<^esub> k2 \<noteq> \<zero>\<^bsub>R\<^esub>"
      proof -
        have "\<And>i. i \<ge> n1 \<Longrightarrow> ?f1 i = ?f2 i"
          using 2(2-5) that p2 by auto
        moreover have "\<And>i. i < n1 \<Longrightarrow> ?f1 i = ?f2 i"
          using 2(2-5) that p2 by auto
        ultimately show ?thesis
          by auto
      qed

      ultimately show ?case
        by blast
    qed }

  thus ?thesis
    using assms by auto
qed

lemma (in ring) supp_mult:
  assumes "polynomial R p1" "polynomial R p2"
  shows "supp R (p_mult R p1 p2) = (\<lambda>i. \<Oplus> k \<in> {..i}. ((supp R p1) k) \<otimes> ((supp R p2) (i - k)))"
  using assms ring_axioms
proof (induct p1 p2 rule: p_mult.induct)
  case (1 R p2)
  then interpret ring R
    by simp
  have "\<And>i k :: nat. supp R [] i \<otimes>\<^bsub>R\<^esub> supp R p2 (i - k) = \<zero>\<^bsub>R\<^esub>"
  proof (simp)
    fix i k
    have "supp R p2 (i - k) \<in> carrier R"
      using supp_img_in_carrier[OF 1(2)] by auto
    thus "\<zero>\<^bsub>R\<^esub> \<otimes>\<^bsub>R\<^esub> supp R p2 (i - k) = \<zero>\<^bsub>R\<^esub>"
      by auto
  qed
  thus ?case
    using 1 add.finprod_one supp_img_in_carrier[OF 1(2)] by auto
next
  case (2 R k1 n1 p1 p2)
  then interpret ring R
    by simp

  have p1: "polynomial R p1"
    using tl_polynomial[OF 2(2)] by simp

  have in_carrier:
    "k1 \<in> carrier R" "\<And>i. supp R p1 i \<in> carrier R" "\<And>i. supp R p2 i \<in> carrier R"
    using supp_img_in_carrier[OF p1] supp_img_in_carrier[OF 2(3)] coeff_in_carrier[OF 2(2)] by auto

  have [simp]: "(\<lambda>i. (if i \<ge> n1 then k1 \<otimes>\<^bsub>R\<^esub> supp R p2 (i - n1) else \<zero>\<^bsub>R\<^esub>)) =
                (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. (if k = n1 then k1 else \<zero>\<^bsub>R\<^esub>) \<otimes>\<^bsub>R\<^esub> ((supp R p2) (i - k))))"
  (is "?f1 = (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k)))")
  proof
    fix i
    have "\<And>k. k \<in> {..i} \<Longrightarrow> ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k) = \<zero>\<^bsub>R\<^esub>" if "i < n1"
      using in_carrier that by auto
    hence "(\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k)) = \<zero>\<^bsub>R\<^esub>" if "i < n1"
      using that in_carrier
            add.finprod_cong'[of "{..i}" "{..i}" "\<lambda>k. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k)" "\<lambda>i. \<zero>\<^bsub>R\<^esub>"]
      by auto
    hence eq_lt: "?f1 i = (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k))) i" if "i < n1"
      using that by auto

    have "\<And>k. k \<in> {..i} \<Longrightarrow>
              ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k) = (if n1 = k then k1 \<otimes>\<^bsub>R\<^esub> supp R p2 (i - k) else \<zero>\<^bsub>R\<^esub>)" if "i \<ge> n1"
      using that in_carrier by auto
    hence "(\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k)) = 
           (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. (if n1 = k then k1 \<otimes>\<^bsub>R\<^esub> supp R p2 (i - k) else \<zero>\<^bsub>R\<^esub>))" if "i \<ge> n1"
      using that in_carrier
            add.finprod_cong'[of "{..i}" "{..i}" "\<lambda>k. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k)"
                             "\<lambda>k. (if n1 = k then k1 \<otimes>\<^bsub>R\<^esub> supp R p2 (i - k) else \<zero>\<^bsub>R\<^esub>)"]
      by fastforce
    also have " ... = k1 \<otimes>\<^bsub>R\<^esub> supp R p2 (i - n1)" if "i \<ge> n1"
      using add.finprod_singleton[of n1 "{..i}" "\<lambda>j. k1 \<otimes>\<^bsub>R\<^esub> supp R p2 (i - j)"]
            in_carrier that by auto
    finally have "(\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k)) =  k1 \<otimes>\<^bsub>R\<^esub> supp R p2 (i - n1)" if "i \<ge> n1"
      using that by simp
    hence eq_ge: "?f1 i = (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k))) i" if "i \<ge> n1"
      using that by auto

    from eq_lt eq_ge show "?f1 i = (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f2 k \<otimes>\<^bsub>R\<^esub> ?f3 (i - k))) i" by auto
  qed

  have "supp R (p_mult R ((k1, n1) # p1) p2) =
          (\<lambda>i. (supp R (p_mult_aux R (k1, n1) p2) i) \<oplus>\<^bsub>R\<^esub> (supp R (p_mult R p1 p2) i))"
    using p_mult_is_polynomial[OF p1 2(3)] coeff_in_carrier[OF 2(2)] supp_add
          p_mult_aux_is_polynomial[of k1 p2] 2(3) by auto
  also
  have " ... = (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. (if k = n1 then k1 else \<zero>\<^bsub>R\<^esub>) \<otimes>\<^bsub>R\<^esub> ((supp R p2) (i - k))) \<oplus>\<^bsub>R\<^esub>
                    (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ((supp R p1) k) \<otimes>\<^bsub>R\<^esub> ((supp R p2) (i - k))))"
    using supp_mult_aux[OF 2(3), of k1 n1] coeff_in_carrier[OF 2(2)]
          2(1) tl_polynomial[OF 2(2)] 2(3-4) by simp
  also have " ... = (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}.
                    ((if k = n1 then k1 else \<zero>\<^bsub>R\<^esub>) \<otimes>\<^bsub>R\<^esub> ((supp R p2) (i - k)) ) \<oplus>\<^bsub>R\<^esub>
                                   ((supp R p1) k) \<otimes>\<^bsub>R\<^esub> ((supp R p2) (i - k)) ))"
    using add.finprod_mult in_carrier by auto
  also have " ... = (\<lambda>i. (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. (supp R ((k1, n1) # p1) k) \<otimes>\<^bsub>R\<^esub> (supp R p2) (i - k)))"
  proof
    fix i
    let ?f = "\<lambda>k. ((if k = n1 then k1 else \<zero>\<^bsub>R\<^esub>) \<otimes>\<^bsub>R\<^esub> ((supp R p2) (i - k))) \<oplus>\<^bsub>R\<^esub>
                                 ((supp R p1) k) \<otimes>\<^bsub>R\<^esub> ((supp R p2) (i - k))"
    let ?g = "\<lambda>k. (supp R ((k1, n1) # p1) k) \<otimes>\<^bsub>R\<^esub> (supp R p2) (i - k)"
    have "\<And>k. ?f k = ?g k"
      using in_carrier supp_bounded3[OF 2(2)] by auto
    thus "(\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?f k) = (\<Oplus>\<^bsub>R\<^esub> k \<in> {..i}. ?g k)"
      by auto
  qed
  finally show ?case .
qed


(*
record ('k, 'a) algebra = "'a ring" +
  phi :: "'k \<Rightarrow> 'a"

locale algebra = A?: cring A + R?: field R
  for A :: "('k, 'a, 'b) algebra_scheme" (structure)
  and R :: "('k, 'c)        ring_scheme" (structure) +
  assumes phi_hom: "(phi A) \<in> ring_hom R A"

datatype ('k, 'x) exp =
  Mult "('k, 'x) exp" "('k, 'x) exp" |
  Add  "('k, 'x) exp" "('k, 'x) exp" |
  Cons 'k |
  Var 'x

fun coeff_set :: "('k, 'x) exp \<Rightarrow> 'k set"
  where
    "coeff_set (Cons k) = { k }"
  | "coeff_set (Var  x) = {}"
  | "coeff_set (Mult e1 e2) = (coeff_set e1) \<union> (coeff_set e2)"
  | "coeff_set (Add  e1 e2) = (coeff_set e1) \<union> (coeff_set e2)"

fun poly_of_exp :: "('k, 'a, 'b) algebra_scheme \<Rightarrow> ('k, 'x) exp \<Rightarrow> ('x \<Rightarrow> 'a) \<Rightarrow> 'a"
  where
    "poly_of_exp A (Cons k) = (\<lambda>X. (phi A) k)"
  | "poly_of_exp A (Var  x) = (\<lambda>X. X x)"
  | "poly_of_exp A (Mult e1 e2) = (\<lambda>X. ((poly_of_exp A e1) X) \<otimes>\<^bsub>A\<^esub> ((poly_of_exp A e2) X))"
  | "poly_of_exp A (Add  e1 e2) = (\<lambda>X. ((poly_of_exp A e1) X) \<oplus>\<^bsub>A\<^esub> ((poly_of_exp A e2) X))"

fun coeffs :: "('k, 'c) ring_scheme \<Rightarrow> ('k, 'x) exp \<Rightarrow> ('k \<times> ('x multiset)) set"
  where
    "coeffs R (Cons k) = { (k, {#}) }"
  | "coeffs R (Var  x) = { (\<one>\<^bsub>R\<^esub>, {# x #}) }"
  | "coeffs R (Mult e1 e2) = { (\<one>\<^bsub>R\<^esub>, {#}) }"
  | "coeffs R (Add e1 e2)  = { (\<one>\<^bsub>R\<^esub>, {#}) }"


subsection \<open>Multivariate Polynomials\<close>

definition mult_poly ::
  "('k, 'c) ring_scheme \<Rightarrow> ('k, 'a, 'b) algebra_scheme \<Rightarrow> ('k, (('x \<Rightarrow> 'a) \<Rightarrow> 'a)) algebra"
  where
    "mult_poly R A =
       \<lparr> carrier = { (\<lambda>X \<in> UNIV \<rightarrow> carrier A. (poly_of_exp A) e X) | e. coeff_set e \<subseteq> carrier R },
         monoid.mult = (\<lambda>p1. \<lambda>p2. \<lambda>X \<in> UNIV \<rightarrow> carrier A. (p1 X) \<otimes>\<^bsub>A\<^esub> (p2 X)),
         one  = (\<lambda>X \<in> UNIV \<rightarrow> carrier A. (phi A) \<one>\<^bsub>R\<^esub>),
         zero = (\<lambda>X \<in> UNIV \<rightarrow> carrier A. (phi A) \<zero>\<^bsub>R\<^esub>),
         add  = (\<lambda>p1. \<lambda>p2. \<lambda>X \<in> UNIV \<rightarrow> carrier A. (p1 X) \<oplus>\<^bsub>A\<^esub> (p2 X)),
         phi  = (\<lambda>k. \<lambda>X \<in> UNIV \<rightarrow> carrier A. (phi A) k) \<rparr>"

*)

(*
lemma (in algebra) mult_poly_one_closed: "one (mult_poly R A) \<in> carrier (mult_poly R A)"
proof -
  define e :: "('k, 'x) exp" where "e = Cons \<one>\<^bsub>R\<^esub>"
  hence "(\<lambda>x. (phi A) \<one>\<^bsub>R\<^esub>) = (poly_of_exp A) e" "coeff_set e \<subseteq> carrier R" by simp+
  thus ?thesis unfolding mult_poly_def by auto
qed

lemma (in algebra) mult_poly_zero_closed: "zero (mult_poly R A) \<in> carrier (mult_poly R A)"
proof -
  define e :: "('k, 'x) exp" where "e = Cons \<zero>\<^bsub>R\<^esub>"
  hence "(\<lambda>x. (phi A) \<zero>\<^bsub>R\<^esub>) = (poly_of_exp A) e" "coeff_set e \<subseteq> carrier R" by simp+
  thus ?thesis unfolding mult_poly_def by auto
qed

lemma (in algebra) mult_poly_is_monoid: "monoid (mult_poly R A)"
proof
  show "one (mult_poly R A) \<in> carrier (mult_poly R A)"
    using mult_poly_one_closed .
next
  fix p1 p2 p3
  assume "p1 \<in> carrier (mult_poly R A)"
     and "p2 \<in> carrier (mult_poly R A)"
     and "p3 \<in> carrier (mult_poly R A)"
  then obtain e1 e2 e3
    where e1: "coeff_set e1 \<subseteq> carrier R" "(poly_of_exp A) e1 = p1"
      and e2: "coeff_set e2 \<subseteq> carrier R" "(poly_of_exp A) e2 = p2"
      and e3: "coeff_set e3 \<subseteq> carrier R" "(poly_of_exp A) e3 = p3"
    unfolding mult_poly_def by auto

  define e_mult :: "('k, 'x) exp" where "e_mult = Mult e1 e2"
  hence "p1 \<otimes>\<^bsub>(mult_poly R A)\<^esub> p2 = (poly_of_exp A) e_mult"
    using e1 e2 unfolding mult_poly_def by simp
  moreover have "coeff_set e_mult \<subseteq> carrier R"
    using e1 e2 e_mult_def by simp
  ultimately show "p1 \<otimes>\<^bsub>(mult_poly R A)\<^esub> p2 \<in> carrier (mult_poly R A)"
    unfolding mult_poly_def by auto

  show "(p1 \<otimes>\<^bsub>mult_poly R A\<^esub> p2) \<otimes>\<^bsub>mult_poly R A\<^esub> p3 = p1 \<otimes>\<^bsub>mult_poly R A\<^esub> (p2 \<otimes>\<^bsub>mult_poly R A\<^esub> p3)"
    unfolding mult_poly_def apply auto 
  proof (auto)

qed


subsection \<open>Univariate Polynomials\<close>

definition uni_poly ::
  "('k, 'd) ring_scheme \<Rightarrow> ('k, 'x, 'c) algebra_scheme \<Rightarrow> ('k, ('x \<Rightarrow> 'x)) algebra"
  where
    "uni_poly R A =
       \<lparr> carrier = { (\<lambda>x. poly_of_exp A e (\<lambda>a. x)) | e. coeff_set e \<subseteq> carrier R },
         mult = (\<lambda>p1. \<lambda>p2. \<lambda>x. (p1 x) \<otimes>\<^bsub>A\<^esub> (p2 x)),
         one = (\<lambda>x. (phi A) \<one>\<^bsub>R\<^esub>),
         zero = (\<lambda>x. (phi A) \<zero>\<^bsub>R\<^esub>),
         add = (\<lambda>p1. \<lambda>p2. \<lambda>x. (p1 x) \<oplus>\<^bsub>A\<^esub> (p2 x)),
         phi = (\<lambda>k. \<lambda>x. (phi A) k) \<rparr>"

lemma (in algebra) univar_poly_is_ring: "ring (uni_poly R A)"
  sorry
*)
end