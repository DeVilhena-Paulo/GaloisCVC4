(* ************************************************************************** *)
(* Title:      Finite_Extensions.thy                                          *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Finite_Extensions
  imports More_Polynomials More_Finite_Product Generated_Groups Subrings
    
begin

section \<open>Notion of Dimension\<close>

subsection \<open>Definitions\<close>

text \<open>The definitions of linear Span and dimension have two subtleties. First, they are
      defined over a subset K of the ring and not over a external structure from which
      a scalar multiplication is defined. Second, they are defined in the context of
      the locale ring. Both observations are explained by the fact that the objects we
      wish to study using these definitions are K-Algebras and not Vector Spaces in
      all of its generality. That being said, we justify our choices by the fact that
      a K-Algebra R can be seen as a ring R and a homomorphism from K to R which can
      be seen in its turn as a ring R and a distinguished subset formed by the image of
      this homomorphism. \<close>

text \<open>We define the set of generators (as well as the set of bases) and not a predicate
      generator only for syntactic reasons\<close>

definition span :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("Span\<index>")
   where "span R K S = generate (add_monoid R) (K <#>\<^bsub>R\<^esub> S)"

definition generators :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a set) set" ("generators\<index>")
  where "generators\<^bsub>R\<^esub> K A = { B. B \<subseteq> A \<and> A = Span\<^bsub>R\<^esub> K B }"

definition dim :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> nat" ("dim\<index>")
  where "dim\<^bsub>R\<^esub> K A = (LEAST k. \<exists>B. finite B \<and> card B = k \<and> B \<in> generators\<^bsub>R\<^esub> K A)"

definition finite_dim :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" ("finite'_dim\<index>")
  where "finite_dim\<^bsub>R\<^esub> K A \<longleftrightarrow> (\<exists>B. finite B \<and> B \<in> generators\<^bsub>R\<^esub> K A)"

definition linear_ind :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" ("linear'_ind\<index>")
  where "linear_ind\<^bsub>R\<^esub> K B \<longleftrightarrow> dim\<^bsub>R\<^esub> K (Span\<^bsub>R\<^esub> K B) = card B"

abbreviation linear_dep :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" ("linear'_dep\<index>")
  where "linear_dep\<^bsub>R\<^esub> K B \<equiv> \<not> linear_ind\<^bsub>R\<^esub> K B"

definition bases :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set  \<Rightarrow> ('a set) set" ("bases\<index>")
  where "bases\<^bsub>R\<^esub> K A = { B. linear_ind\<^bsub>R\<^esub> K B \<and> B \<in> generators\<^bsub>R\<^esub> K A }"

definition scalar_prop :: "_ \<Rightarrow> 'a set \<Rightarrow> bool"
  where "scalar_prop R K \<longleftrightarrow> (\<forall>k \<in> K. \<forall>a \<in> carrier R. k \<otimes>\<^bsub>R\<^esub> a = a \<otimes>\<^bsub>R\<^esub> k)"

definition over :: "('a set \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'c)" (infixl "over" 65)
  where "f over K \<equiv> f K"

locale embedded_algebra =
  K?: subfield K R + R?: ring R for K :: "'a set" and R :: "('a, 'b) ring_scheme" (structure)


subsection \<open>Basic Properties - First Part\<close>

(*
lemma embedded_algebraI:
  assumes "h \<in> ring_hom R S" and "field R"
  shows "embedded_algebra (h ` (carrier R)) S"
proof -
  have "field (R \<lparr> carrier := (h ` (carrier S)) \<rparr>)"
    sorry
  show ?thesis
    sorry
qed
*)

lemma (in ring) span_incl: "K <#> S \<subseteq> Span K S"
  unfolding span_def using generate.incl[of _ _ "add_monoid R"] by auto

lemma (in ring) span_is_subgroup:
  assumes "K <#> S \<subseteq> carrier R"
  shows "subgroup (Span K S) (add_monoid R)"
  unfolding span_def using add.generate_is_subgroup[OF assms] .

lemma (in ring) span_is_subgroup':
  assumes "K \<subseteq> carrier R" and "S \<subseteq> carrier R"
  shows "subgroup (Span K S) (add_monoid R)"
  using span_is_subgroup[OF set_mult_closed[OF assms]] .

lemma (in ring) span_min:
  assumes "K <#> S \<subseteq> carrier R"
  shows "Span K S = \<Inter>{ H. subgroup H (add_monoid R) \<and> K <#> S \<subseteq> H }"
  unfolding span_def using add.generate_min_subgroup2[OF assms] .

corollary (in ring) span_min':
  assumes "subgroup H (add_monoid R)" and "K <#> S \<subseteq> H"
  shows "Span K S \<subseteq> H"
  using span_min[of K S] add.subgroupE(1)[OF assms(1)] assms by auto

lemma (in ring) mono_span:
  assumes "K \<subseteq> K'" "K' \<subseteq> carrier R" and "S \<subseteq> S'" "S' \<subseteq> carrier R"
  shows "Span K S \<subseteq> Span K' S'"
  unfolding span_def
  using add.mono_generate[OF mono_set_mult[OF assms(1) assms(3), of R]]
        set_mult_closed[OF assms(2) assms(4)] by simp

lemma (in ring) span_equality:
  assumes "subgroup H (add_monoid R)" "K <#> S \<subseteq> H"
  shows "Span\<^bsub>(R \<lparr> carrier := H \<rparr>)\<^esub> K S = Span K S"
  unfolding span_def
  using add.subgroup_gen_equality[OF assms]
        set_mult_consistent[of R K S H]
  by auto

corollary (in ring) span_equality_betw_subgroups:
  assumes "subgroup I (add_monoid R)" and "subgroup J (add_monoid R)"
    and "K <#> S \<subseteq> (I \<inter> J)"
  shows "Span\<^bsub>(R \<lparr> carrier := I \<rparr>)\<^esub> K S = Span\<^bsub>(R \<lparr> carrier := J \<rparr>)\<^esub> K S"
  using span_equality[OF assms(1)] span_equality[OF assms(2)] assms(3) by auto

lemma (in ring) span_empty: "Span K {} = { \<zero> }"
  unfolding span_def set_mult_def using add.generate_empty by auto

lemma (in ring) span_line:
  assumes "subgroup K (add_monoid R)" and "a \<in> carrier R"
  shows "Span K { a } = K #> a"
  unfolding r_coset_eq_set_mult
proof
  show "K <#> { a } \<subseteq> Span K { a }"
    using span_incl[of K "{ a }"] .
  have a_set: "{ a } \<subseteq> carrier R"
    using assms(2) by blast
  show "Span K { a } \<subseteq> K <#> { a }"
  proof (rule span_min')
    show "K <#> { a } \<subseteq> K <#> { a }" by simp
  next
    show "subgroup (K <#> { a }) (add_monoid R)"
    proof (rule add.subgroupI)
      show "K <#> { a } \<subseteq> carrier R"
        using set_mult_closed[OF add.subgroupE(1)[OF assms(1)] a_set] .
      show "K <#> { a } \<noteq> {}"
        unfolding set_mult_def using add.subgroupE(2)[OF assms(1)] by blast
    next
      fix b1 b2 assume "b1 \<in> K <#> { a }" "b2 \<in> K <#> { a }"
      then obtain k1 k2
        where k1: "k1 \<in> K" "b1 = k1 \<otimes> a"
          and k2: "k2 \<in> K" "b2 = k2 \<otimes> a"
        unfolding set_mult_def by blast
      have "\<ominus> b1 = (\<ominus> k1) \<otimes> a"
        using add.subgroupE(1)[OF assms(1)] k1 l_minus[OF _ assms(2)] by auto
      thus "\<ominus> b1 \<in> K <#> { a }" unfolding set_mult_def
        using add.subgroupE(3)[OF assms(1) k1(1)] by blast
      have "b1 \<oplus> b2 = (k1 \<oplus> k2) \<otimes> a"
        using add.subgroupE(1)[OF assms(1)] k1 k2
              l_distr[OF _ _ assms(2), of k1 k2]
        by force
      thus "b1 \<oplus> b2 \<in> K <#> { a }" unfolding set_mult_def
        using add.subgroupE(4)[OF assms(1) k1(1) k2(1)] by blast
    qed
  qed
qed

lemma (in ring) span_one:
  assumes "subgroup K (add_monoid R)"
  shows "Span K { \<one> } = K"
proof -
  have eq: "K <#> { \<one> } = K"
    using add.subgroupE(1)[OF assms] by (force simp add: set_mult_def) 
  show ?thesis
    using span_line[OF assms, of \<one>]
    unfolding r_coset_eq_set_mult eq
    by simp
qed


subsection \<open>Linear Combinations\<close>

lemma (in ring) span_as_linear_combinations:
  assumes "subgroup K (add_monoid R)" and "finite S" "S \<subseteq> carrier R"
  shows "Span K S = { \<Oplus>s \<in> S. (f s) \<otimes> s | f. f: S \<rightarrow> K }"
    (is "Span K S = { ?sum S f | f. ?S_to_K f }")
proof
  have K: "K \<subseteq> carrier R" and KS: "K <#> S \<subseteq> carrier R"
    using set_mult_closed[OF _ assms(3)] add.subgroupE(1)[OF assms(1)] by auto
  hence carr:
    "\<And>k. k \<in> K \<Longrightarrow> k \<in> carrier R"
    "\<And>s. s \<in> S \<Longrightarrow> s \<in> carrier R"
    "\<And>k s. \<lbrakk> k \<in> K; s \<in> S \<rbrakk> \<Longrightarrow> k \<otimes> s \<in> carrier R"
    using assms(3) by auto

  show "Span K S \<subseteq> { ?sum S f | f. ?S_to_K f }"
    unfolding span_def
  proof
    fix a assume "a \<in> generate (add_monoid R) (K <#> S)"
    hence "\<exists>f. ?S_to_K f \<and> a = ?sum S f"
    proof (induction a)
      case one
      hence "\<zero> = ?sum S (\<lambda>_. \<zero>)"
        using add.finprod_one[OF assms(2)] assms(3)
        by (metis contra_subsetD l_null)
      thus ?case
        using assms(1) by (auto simp add: subgroup_def)
    next
      case (incl h)
      then obtain k s where k: "k \<in> K" and s: "s \<in> S" and h: "h = k \<otimes> s"
        unfolding set_mult_def by blast

      define f where "f = (\<lambda>i. if s = i then k else \<zero>)"
      hence Step1: "?S_to_K f"
        using assms(1) k by (simp add: subgroup_def)

      let ?g = "\<lambda>i. if s = i then k \<otimes> s else \<zero>"
      have "h = (\<Oplus>i \<in> S. ?g i)"
        unfolding h using add.finprod_singleton[OF s assms(2)] carr(3)[OF k s] by auto
      also have " ... = ?sum S f"
        using add.finprod_cong'[of S S "\<lambda>i. (f i) \<otimes> i" ?g] by (auto simp add: carr k s f_def)
      finally have Step2: "h = ?sum S f" .
      
      from Step1 Step2 show ?case by auto
    next
      case (inv h)
      then obtain k s where "k \<in> K" and s: "s \<in> S" and "h = k \<otimes> s"
        unfolding set_mult_def by blast
      hence k: "\<ominus> k \<in> K" and h: "\<ominus> h = (\<ominus> k) \<otimes> s"
        by (auto simp add: add.subgroupE(3) assms(1) carr(1-2) l_minus)

      define f where "f = (\<lambda>i. if s = i then (\<ominus> k) else \<zero>)"
      hence Step1: "?S_to_K f"
        using assms(1) k by (simp add: subgroup_def)

      let ?g = "\<lambda>i. if s = i then (\<ominus> k) \<otimes> s else \<zero>"
      have "\<ominus> h = (\<Oplus>i \<in> S. ?g i)"
        unfolding h using add.finprod_singleton[OF s assms(2), of "\<lambda>i. (\<ominus> k) \<otimes> s"] carr k s by auto
      also have " ... = ?sum S f"
        using add.finprod_cong'[of S S "\<lambda>i. (f i) \<otimes> i" ?g] by (auto simp add: carr k s f_def)
      finally have Step2: "\<ominus> h = ?sum S f" .
      
      from Step1 Step2 show ?case
        using a_inv_def[of R] by auto
    next
      case (eng h1 h2)
      then obtain f g
        where f: "?S_to_K f" "h1 = ?sum S f"
          and g: "?S_to_K g" "h2 = ?sum S g"
        by blast
      let ?h = "\<lambda>s. (f s) \<oplus> (g s)" and ?comp = "\<lambda>f. \<lambda>s. (f s) \<otimes> s"
      have Step1: "?S_to_K ?h"
        using add.subgroupE(4)[OF assms(1)] f(1) g(1) by auto

      have "\<And>s. s \<in> S \<Longrightarrow> ?comp ?h s = (?comp f s) \<oplus> (?comp g s)"
        using f(1) g(1) carr l_distr by (meson PiE)  
      hence "?sum S ?h = (\<Oplus>s \<in> S. (?comp f s) \<oplus> (?comp g s))"
        using add.finprod_cong'[of S S "\<lambda>s. (?comp f s) \<oplus> (?comp g s)" "?comp ?h"] carr f(1) g(1)
        by (simp add: Pi_def)
      also have "... = h1 \<oplus> h2" unfolding f g
        using add.finprod_multf[of "?comp f" S "?comp g"] carr K f(1) g(1) by (simp add: Pi_def)
      finally have Step2: "?sum S ?h = h1 \<oplus> h2" .

      from Step1 Step2 show ?case by auto
    qed
    thus "a \<in> { ?sum S f | f. ?S_to_K f }" by blast
  qed

  show "{ ?sum S f | f. ?S_to_K f } \<subseteq> Span K S"
  proof
    fix a assume "a \<in> { ?sum S f | f. ?S_to_K f }"
    then obtain f where a: "a = ?sum S f" and f: "?S_to_K f"
      by blast
    from assms(2-3) and a and f show "a \<in> Span K S"
    proof (induct S arbitrary: a)
      case empty thus ?case
        using span_empty by auto
    next
      case (insert s_n S)
      let ?comp = "\<lambda>f. \<lambda>s. (f s) \<otimes> s"
      have s_n: "s_n \<in> carrier R" and S: "S \<subseteq> carrier R"
        using insert(4) by auto
      hence "f \<in> S \<rightarrow> carrier R" and "f \<in> { s_n } \<rightarrow> carrier R"
        using insert(6) K by auto
      hence comp_f: "?comp f \<in> S \<rightarrow> carrier R" and "f s_n \<otimes> s_n \<in> carrier R"
        using S s_n by blast+
      hence a: "a = (?sum S f) \<oplus> ((f s_n) \<otimes> s_n)" unfolding insert(5)
        using insert(2) finsum_Un_disjoint[OF insert(1), of "{ s_n }" "\<lambda>s. (f s) \<otimes> s"] by auto

      moreover have "?sum S f \<in> Span K S"
        using insert(3)[OF S] insert(6) by auto
      hence "?sum S f \<in> Span K (insert s_n S)"
        using mono_span[OF _ K _ insert(4), of K S] by auto

      moreover have "f s_n \<in> K"
        using insert(6) by auto
      hence "(f s_n) \<otimes> s_n \<in> K <#> insert s_n S"
        unfolding set_mult_def by auto
      hence "(f s_n) \<otimes> s_n \<in> Span K (insert s_n S)"
        unfolding span_def using generate.incl[of _ _ "add_monoid R"] by simp

      ultimately show ?case
        unfolding span_def using generate.eng[of _ "add_monoid R"] by auto
    qed
  qed
qed

lemma (in ring) finite_combination:
  assumes "a \<in> Span K S" and "subgroup K (add_monoid R)" "S \<subseteq> carrier R"
  shows "\<exists>S'. S' \<subseteq> S \<and> finite S' \<and> a \<in> Span K S'"
  using assms(1) unfolding span_def
proof (induct a)
  case one thus ?case
    using span_empty[of K] unfolding span_def by auto
next
  case (incl h)
  then obtain k s where k: "k \<in> K" and s: "s \<in> S" and h: "h = k \<otimes> s"
    unfolding set_mult_def by blast
  hence "h \<in> K <#> { s }"
    unfolding set_mult_def by blast
  hence "h \<in> Span K { s }"
    unfolding span_def using generate.incl[of _ _ "add_monoid R"] by simp
  thus ?case
    unfolding span_def using s by blast
next
  case (inv h)
  then obtain k s where "k \<in> K" and k: "\<ominus> k \<in> K" and s: "s \<in> S" and "h = k \<otimes> s"
    unfolding set_mult_def using add.subgroupE(3)[OF assms(2)] by blast
  hence "\<ominus> h = (\<ominus> k) \<otimes> s"
    using assms(3) add.subgroupE(1,3)[OF assms(2)] l_minus[of k s] set_rev_mp by metis
  hence "\<ominus> h \<in> K <#> { s }"
    unfolding set_mult_def using k s by blast
  hence "\<ominus> h \<in> Span K { s }"
    unfolding span_def using generate.incl[of _ _ "add_monoid R"] by simp
  then show ?case
    unfolding span_def a_inv_def using s by blast  
next
  case (eng h1 h2)
  then obtain S1 S2
    where S1: "S1 \<subseteq> S" "finite S1" "h1 \<in> Span K S1"
      and S2: "S2 \<subseteq> S" "finite S2" "h2 \<in> Span K S2"
    unfolding span_def by blast
  hence "h1 \<in> Span K (S1 \<union> S2)" "h2 \<in> Span K (S1 \<union> S2)"
    using mono_span[OF _ add.subgroupE(1)[OF assms(2)], of K S1 "S1 \<union> S2"]
          mono_span[OF _ add.subgroupE(1)[OF assms(2)], of K S2 "S1 \<union> S2"]
    using assms(3) by auto
  hence "h1 \<oplus> h2 \<in> Span K (S1 \<union> S2)"
    unfolding span_def using generate.eng[of _ "add_monoid R"] by simp
  moreover have "finite (S1 \<union> S2)" and "S1 \<union> S2 \<subseteq> S"
    using S1 S2 by auto
  ultimately show ?case
    unfolding span_def by (metis monoid.select_convs(1))  
qed

lemma (in ring) span_iff_finite_linear_combination:
  assumes "subgroup K (add_monoid R)" and "S \<subseteq> carrier R"
  shows "a \<in> Span K S \<longleftrightarrow> (\<exists>f S'. finite S' \<and> S' \<subseteq> S \<and> f: S' \<rightarrow> K \<and> a = (\<Oplus>s \<in> S'. (f s) \<otimes> s))"
    (is "a \<in> Span K S \<longleftrightarrow> (\<exists>f S'. ?finite_linear_combination f S' a)")
proof
  assume "a \<in> Span K S"
  then obtain S' where S': "finite S'" "S' \<subseteq> S" "a \<in> Span K S'"
    using finite_combination[OF _ assms] by blast
  then obtain f where "a = (\<Oplus>s \<in> S'. (f s) \<otimes> s)" and "f: S' \<rightarrow> K"
    using span_as_linear_combinations[OF assms(1), of S'] assms(2) by blast
  hence "?finite_linear_combination f S' a"
    using S' by auto
  thus "\<exists>f S'. ?finite_linear_combination f S' a" by blast
next
  assume "\<exists>f S'. ?finite_linear_combination f S' a"
  then obtain f S' where S': "finite S'" "S' \<subseteq> S" "f: S' \<rightarrow> K" and a: "a = (\<Oplus>s \<in> S'. (f s) \<otimes> s)"
    by blast
  hence "a \<in> Span K S'"
    using span_as_linear_combinations[OF assms(1), of S'] assms(2) S' by blast
  thus "a \<in> Span K S"
    using mono_span[OF _ add.subgroupE(1)[OF assms(1)] S'(2) assms(2), of K] by blast 
qed


subsection \<open>Product of Finite Sums and More Algebraic Properties of Span\<close>

lemma (in semiring) prod_of_finsums:
  assumes "finite A" "finite B"
    and "\<And>a. a \<in> A \<Longrightarrow> f a \<in> carrier R"
    and "\<And>a. a \<in> B \<Longrightarrow> g a \<in> carrier R"
  shows "(\<Oplus>a \<in> A. f a) \<otimes> (\<Oplus>b \<in> B. g b) = (\<Oplus>a \<in> A. (\<Oplus>b \<in> B. (f a) \<otimes> (g b)))"
    (is "?sum_f A \<otimes> ?sum_g = ?prod_sum A")
  using assms
proof (induct A)
  case empty thus ?case by simp
next
  case (insert a' A)
  hence "?sum_f (insert a' A) \<otimes> ?sum_g = (f a' \<otimes> ?sum_g) \<oplus> (?sum_f A \<otimes> ?sum_g)"
    using insert(5-6)  by (simp add: l_distr)
  also have " ... = (f a' \<otimes> ?sum_g) \<oplus> ?prod_sum A"
    using insert by simp
  also have " ... = (\<Oplus>b \<in> B. (f a') \<otimes> (g b)) \<oplus> ?prod_sum A"
    by (simp add: finsum_rdistr insert)
  finally have "?sum_f (insert a' A) \<otimes> ?sum_g = (\<Oplus>b \<in> B. (f a') \<otimes> (g b)) \<oplus> ?prod_sum A" .
  thus ?case
    using insert by simp
qed

lemma (in ring) span_m_closed:
  assumes "subring K R" and "S \<subseteq> carrier R"
  shows "\<And>a b. \<lbrakk> a \<in> Span K S; b \<in> Span K S \<rbrakk> \<Longrightarrow> a \<otimes> b \<in> Span K S"
proof -
  fix a b assume "a \<in> Span K S" "b \<in> Span K S"



corollary (in ring) linear_dependence:
  assumes "subring K R" and "S \<subseteq> carrier R"
    and "finite S'" "S' \<subseteq> S" "f: S' \<rightarrow> K" "a = (\<Oplus>s \<in> S'. (f s) \<otimes> s)"
  shows "Span K S = Span K (insert a S)"
proof
  have in_carrier: "\<And>s. s \<in> S' \<Longrightarrow> (f s) \<otimes> s \<in> carrier R"
    using assms(2,4-5) subringE(1)[OF assms(1)] by blast 
  hence a: "a \<in> carrier R"
    using assms(6) by auto
  thus "Span K S \<subseteq> Span K (insert a S)"
    using mono_span[OF _ subringE(1)[OF assms(1)], of K S "insert a S"] assms(2) by auto

  have "\<And>k. k \<in> K \<Longrightarrow> k \<otimes> a \<in> Span K S"
  proof -
    fix k assume k: "k \<in> K" hence k_carr: "k \<in> carrier R"
      using subringE(1)[OF assms(1)] by auto
    have f: "\<And>s. s \<in> S' \<Longrightarrow> f s \<in> carrier R"
      using assms(5) subringE(1)[OF assms(1)] by auto
    define g where "g = (\<lambda>s. k \<otimes> (f s))"
    have assoc: "\<And>s. s \<in> S' \<Longrightarrow> k \<otimes> (f s \<otimes> s) = g s \<otimes> s"
      unfolding g_def using k_carr m_assoc f assms(2,4) by auto 
    have g: "g: S' \<rightarrow> K"
      unfolding g_def using assms(5) subringE(6)[OF assms(1)] k by auto
    have "(\<lambda>s. f s \<otimes> s) \<in> S' \<rightarrow> carrier R"
      using in_carrier by simp
    hence "k \<otimes> a = (\<Oplus>s \<in> S'. k \<otimes> (f s \<otimes> s))" unfolding assms(6)
      using finsum_rdistr[OF assms(3) k_carr, of "\<lambda>s. (f s) \<otimes> s"] by simp
    also have "... = (\<Oplus>s \<in> S'. g s \<otimes> s)" unfolding g_def assms(6)
      using add.finprod_cong'[of S' S' "\<lambda>s. k \<otimes> (f s \<otimes> s)" "\<lambda>s. (k \<otimes> f s) \<otimes> s"]
      by (smt Pi_iff g_def local.ring_axioms monoid.m_closed ring_def assoc in_carrier k_carr)
    finally have "k \<otimes> a = (\<Oplus>s \<in> S'. g s \<otimes> s)" .
    thus "k \<otimes> a \<in> Span K S"
      using span_iff_finite_linear_combination[OF subring.axioms(1)[OF assms(1)] assms(2)]
            assms(3-4) g by auto
  qed



subsection \<open>Basic Properties - Second Part\<close>

lemma (in ring) generatorsI: "\<lbrakk> B \<subseteq> A; A = Span K B \<rbrakk> \<Longrightarrow> B \<in> generators K A"
  unfolding generators_def by simp

lemma (in ring) generatorsI':
  assumes "subgroup A (add_monoid R)"
  shows "\<lbrakk> B \<subseteq> A; K <#> B \<subseteq> A; A \<subseteq> Span K B \<rbrakk> \<Longrightarrow> B \<in> generators K A"
proof -
  assume "K <#> B \<subseteq> A" hence "Span K B \<subseteq> A"
    using span_min'[OF assms, of K B] by simp
  moreover assume "B \<subseteq> A" "A \<subseteq> Span K B"
  ultimately show "B \<in> generators K A"
    unfolding generators_def by auto
qed

lemma (in ring) trivial_generator_iff: "{} \<in> generators K A \<longleftrightarrow> A = { \<zero> }"
  using span_empty[of K] unfolding generators_def by auto

lemma (in ring) exists_generator_imp_subgroup:
  assumes "K \<subseteq> carrier R" and "A \<subseteq> carrier R"
  shows "generators K A \<noteq> {} \<Longrightarrow> subgroup A (add_monoid R)"
  unfolding generators_def using span_is_subgroup'[OF assms(1)] assms(2) by blast

lemma (in ring) generatorsE:
  assumes "B \<in> generators K A"
    shows "B \<subseteq> A" and "A = Span K B"
  using assms unfolding generators_def by auto

lemma (in ring) dim_le: "\<lbrakk> finite S; S \<in> generators K A \<rbrakk> \<Longrightarrow> (dim over K) A \<le> card S"
  unfolding dim_def over_def by (metis (mono_tags, lifting) Least_le) 

lemma (in ring) dim_gt_zero:
  assumes "(finite_dim over K) A" "{} \<notin> generators K A"
  shows "(dim over K) A > 0"
  using assms unfolding over_def dim_def finite_dim_def by (smt LeastI card_gt_0_iff)

lemma (in ring) dim_zero:
  "(dim over K) { \<zero> } = 0" and "\<lbrakk> (finite_dim over K) A; (dim over K) A = 0 \<rbrakk> \<Longrightarrow> A = { \<zero> }"
proof -
  have "{} \<in> generators K { \<zero> }"
    using span_empty[of K] unfolding generators_def by blast
  thus "(dim over K) { \<zero> } = 0"
    using dim_le[of "{}"] by simp
next
  assume "(finite_dim over K) A" "(dim over K) A = 0"
  hence "{} \<in> generators K A"
    using dim_gt_zero[of K A] by auto
  thus "A = { \<zero> }"
    using span_empty[of K] unfolding generators_def by simp
qed

lemma (in ring) linear_ind_imp_unique_combination:
  assumes "finite B" "linear_ind K B"
  shows "\<And>f. \<lbrakk> f: B \<rightarrow> K; \<zero> = (\<Oplus>s \<in> S. (f s) \<otimes> s) \<rbrakk> \<Longrightarrow> f ` B = { \<zero> }"



lemma (in ring) linear_ind_imp_finite: "linear_ind K B \<Longrightarrow> finite B"
  unfolding linear_ind_def dim_def


lemma (in ring)
  assumes "linear_ind K B" "Span K B \<subseteq> S"
  shows "(dim over K) A \<ge> card B"

(*
section \<open>Finite Extensions\<close>

definition (in ring) algebraic :: "['a, 'a set] \<Rightarrow> bool" (infix "algebraic'_over" 65)
  where "x algebraic_over K \<longleftrightarrow> (\<exists>p \<noteq> []. polynomial (R \<lparr> carrier := K \<rparr>) p \<and> eval p x = \<zero>)"

definition (in ring) transcedental :: "['a, 'a set] \<Rightarrow> bool" (infix "transcedental'_over" 65)
  where "x transcedental_over K \<longleftrightarrow> \<not> (x algebraic_over K)"

inductive_set simple_ext :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  for R (structure) and K and a where
    zero: "\<zero>\<^bsub>R\<^esub> \<in> simple_ext R K a" |
    lin:  "\<lbrakk> k1 \<in> K; k2 \<in> K \<rbrakk> \<Longrightarrow> (k1 \<otimes>\<^bsub>R\<^esub> a) \<oplus>\<^bsub>R\<^esub> k2 \<in> simple_ext R K a"

fun finite_ext :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> 'a set"
  where
    "finite_ext R K [] = K"
  | "finite_ext R K (a # as) = simple_ext R (finite_ext R K as) a"

lemma (in field)
  assumes "subfield K R"
  shows "subfield (simple_ext R K a) R \<longleftrightarrow> a algebraic_over K"
  sorry
*)
end