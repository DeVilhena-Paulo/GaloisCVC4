theory Embedded_Algebras
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
      "generator" only for syntactic reasons. \<close>

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

definition over :: "('a set \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" (infixl "over" 65)
  where "f over K \<equiv> f K"

locale embedded_algebra =
  K?: subfield K R + R?: ring R for K :: "'a set" and R :: "('a, 'b) ring_scheme" (structure)


subsection \<open>Basic Properties - First Part\<close>

lemma (in ring_hom_ring) embedded_algebraI:
  assumes "field R" and "\<one>\<^bsub>S\<^esub> \<noteq> \<zero>\<^bsub>S\<^esub>"
  shows "embedded_algebra (h ` (carrier R)) S"
  using img_is_subfield(2)[OF field.carrier_is_subfield[OF assms(1)] assms(2)] is_ring
  unfolding embedded_algebra_def by simp

lemma [simp]: "f over K = f K"
  unfolding over_def by simp

lemma (in ring) span_incl: "K <#> S \<subseteq> Span K S"
  unfolding span_def using generate.incl[of _ _ "add_monoid R"] by auto

corollary (in ring) span_base_incl:
  assumes "\<one> \<in> K" and" S \<subseteq> carrier R" shows "S \<subseteq> Span K S"
proof -
  have "S \<subseteq> K <#> S"
    using assms(1-2) unfolding set_mult_def by force
  thus ?thesis
    using span_incl[of K S] by simp
qed

lemma (in ring) span_is_subgroup:
  assumes "K <#> S \<subseteq> carrier R"
  shows "subgroup (Span K S) (add_monoid R)"
  unfolding span_def using add.generate_is_subgroup[OF assms] .

lemma (in ring) span_is_subgroup':
  assumes "K \<subseteq> carrier R" and "S \<subseteq> carrier R"
  shows "subgroup (Span K S) (add_monoid R)"
  using span_is_subgroup[OF set_mult_closed[OF assms]] .

lemma (in ring) span_in_carrier:
  assumes "K \<subseteq> carrier R" and "S \<subseteq> carrier R"
  shows "Span K S \<subseteq> carrier R"
  using subgroup.subset[OF span_is_subgroup'[OF assms]] by simp

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
        using insert(2) add.finprod_Un_disjoint[OF insert(1), of "{ s_n }" "\<lambda>s. (f s) \<otimes> s"] by auto

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

corollary (in ring) semi_linear_decomp:
  assumes "subgroup K (add_monoid R)"
    and "u' \<in> carrier R" and "U \<subseteq> carrier R" and "finite U"
  shows "a \<in> Span K (insert u' U) \<Longrightarrow> \<exists>k v. k \<in> K \<and> v \<in> Span K U \<and> a = k \<otimes> u' \<oplus> v"
    (is "a \<in> Span K (insert u' U) \<Longrightarrow> \<exists>k v. ?semi_linear_decomp k v")
proof -
  assume "a \<in> Span K (insert u' U)"
  then obtain f where f: "f: (insert u' U) \<rightarrow> K" and a: "a = (\<Oplus>u \<in> (insert u' U). (f u) \<otimes> u)"
    using span_as_linear_combinations[OF assms(1), of "insert u' U"]
          assms(2-4) insert_subset by blast
  hence in_Span: "(\<Oplus>u \<in> U. (f u) \<otimes> u) \<in> Span K U"
    using span_as_linear_combinations[OF assms(1,4,3)] f by auto
  show ?thesis
  proof (cases "u' \<in> U")
    assume "u' \<in> U"
    hence "a = (\<Oplus>u \<in> U. (f u) \<otimes> u)" unfolding a
      by (simp add: insert_absorb)
    hence "?semi_linear_decomp \<zero> a"
      using subgroup.one_closed[OF assms(1)] assms(2) in_Span
            span_in_carrier[OF _ assms(3), of K] subgroup.subset[OF assms(1)] by auto
    thus ?thesis by blast
  next
    assume u': "u' \<notin> U"
    have "\<And>u. u \<in> (insert u' U) \<Longrightarrow> (f u) \<otimes> u \<in> carrier R"
      using subgroup.subset[OF assms(1)] assms(2-3) f by auto
    hence "a = ((f u') \<otimes> u') \<oplus> (\<Oplus>u \<in> U. (f u) \<otimes> u)" unfolding a
      using assms(4) u' by auto
    hence "?semi_linear_decomp (f u') (\<Oplus>u \<in> U. (f u) \<otimes> u)"
      using in_Span f by auto
    thus ?thesis by blast
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
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> carrier R"
      and "\<And>a. a \<in> B \<Longrightarrow> g a \<in> carrier R"
  shows "(\<Oplus>a \<in> A. f a) \<otimes> (\<Oplus>b \<in> B. g b) = (\<Oplus>a \<in> A. (\<Oplus>b \<in> B. (f a) \<otimes> (g b)))"
    (is "?sum_f A \<otimes> ?sum_g = ?prod_sum A")
proof (cases "finite A")
  assume "infinite A"
  hence "?sum_f A = \<zero>" and "?prod_sum A = \<zero>"
    unfolding finsum_def finprod_def by simp+
  thus ?thesis
    using assms by auto
next
  assume finA: "finite A" show ?thesis
  proof (cases "finite B")
    assume "infinite B"
    hence "?sum_g = \<zero>" and "?prod_sum A = (\<Oplus>a \<in> A. \<zero>)"
      unfolding finsum_def finprod_def by simp+
    thus ?thesis
      using assms add.finprod_one[OF finA, of "\<lambda>_. \<zero>"] by auto
  next
    assume finB: "finite B"
    from finA and finB and assms show ?thesis
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
  qed
qed

lemma (in semiring) finsum_swap:
  assumes "\<And>a b. \<lbrakk> a \<in> A; b \<in> B \<rbrakk> \<Longrightarrow> f a b \<in> carrier R"
  shows "(\<Oplus>a \<in> A. (\<Oplus>b \<in> B. (f a b))) = (\<Oplus>b \<in> B. (\<Oplus>a \<in> A. (f a b)))"
proof (cases "finite A")
  assume "infinite A" thus ?thesis
    using add.finprod_infinite by simp
next
  assume fin_A: "finite A" show ?thesis
  proof (cases "finite B")
    assume "infinite B" thus ?thesis
      using add.finprod_infinite by simp
  next
    assume fin_B: "finite B"
    hence "\<And>a. a \<in> A \<Longrightarrow> (\<Oplus>b \<in> B. (f a b)) \<in> carrier R"
      using assms by auto
    from fin_A and this and assms show ?thesis
    proof (induction)
      case empty thus ?case by simp
    next
      case (insert a' A)
      let ?sum = "finsum R"
      let ?Sum = "\<lambda>A B f. ?sum (\<lambda>a. (?sum (\<lambda>b. f a b) B)) A"
      have "?Sum (insert a' A) B f = (\<Oplus>b \<in> B. (f a' b)) \<oplus> ?Sum A B f"
        using insert(1,2,4) fin_B by auto
      also have "...  = (\<Oplus>b \<in> B. (f a' b)) \<oplus> ?Sum B A (\<lambda>b a. f a b)"
        using insert by simp
      also have " ... = (\<Oplus>b \<in> B. ((f a' b) \<oplus> (\<Oplus>a \<in> A. (f a b))))"
        using insert fin_B add.finprod_multf[of "\<lambda>b. f a' b" B "\<lambda>b. (\<Oplus>a \<in> A. (f a b))"] by auto
      also have " ... = ?Sum B (insert a' A) (\<lambda>b a. f a b)"
      proof -
        have "\<And>b. b \<in> B \<Longrightarrow> (f a' b) \<oplus> (\<Oplus>a \<in> A. (f a b)) = (\<Oplus>a \<in> (insert a' A). (f a b))"
          using insert by auto
        moreover have "(\<lambda>b. \<Oplus>a \<in> (insert a' A). (f a b)): B \<rightarrow> carrier R"
          using insert(5) by auto
        ultimately show ?thesis
          using add.finprod_cong'[of B B "\<lambda>b. ?sum (\<lambda>a. f a b) (insert a' A)" "\<lambda>b. (f a' b) \<oplus> (\<Oplus>a \<in> A. (f a b))"]
          by auto
      qed
      finally show ?case .
    qed
  qed
qed

lemma (in ring) (* span_m_closed: *)
  assumes "subring K R" and "S \<subseteq> carrier R"
  shows "\<And>a b. \<lbrakk> a \<in> Span K S; b \<in> Span K S \<rbrakk> \<Longrightarrow> a \<otimes> b \<in> Span K S"
proof -
  fix a b assume "a \<in> Span K S" "b \<in> Span K S"
  thus "a \<otimes> b \<in> Span K S" sorry
qed

lemma (in ring) span_smult_closed:
  assumes "subring K R" and "S \<subseteq> carrier R"
  shows "\<lbrakk> k \<in> K; a \<in> Span K S \<rbrakk> \<Longrightarrow> k \<otimes> a \<in> Span K S"
proof -
  assume k: "k \<in> K" and a_in_Span: "a \<in> Span K S"
  then obtain f S'
    where S': "finite S'" "S' \<subseteq> S" and f: "\<And>s. s \<in> S' \<Longrightarrow> f s \<in> K" and a: "a = (\<Oplus>s \<in> S'. (f s) \<otimes> s)"
    using span_iff_finite_linear_combination[OF subring.axioms(1)] assms by (auto simp add: Pi_def)
  hence in_carrier:
    "\<And>s. s \<in> S' \<Longrightarrow> s   \<in> carrier R"
    "\<And>s. s \<in> S' \<Longrightarrow> f s \<in> carrier R"
    "\<And>k. k \<in> K  \<Longrightarrow> k   \<in> carrier R"
    using subringE(1) assms by blast+

  hence "k \<otimes> a = (\<Oplus>s \<in> S'. k \<otimes> ((f s) \<otimes> s))" unfolding a
    using k finsum_rdistr[of S' k "\<lambda>s. (f s) \<otimes> s"] S'(1) by blast
  also have " ... = (\<Oplus>s \<in> S'. (k \<otimes> (f s)) \<otimes> s)"
    using add.finprod_cong'[of S' S' "\<lambda>s. k \<otimes> ((f s) \<otimes> s)" "\<lambda>s. (k \<otimes> (f s)) \<otimes> s"]
          in_carrier k m_assoc by auto
  finally have "k \<otimes> a = (\<Oplus>s \<in> S'. (k \<otimes> (f s)) \<otimes> s)" .
  moreover have "(\<lambda>s. (k \<otimes> (f s))): S' \<rightarrow> K"
    using f k subringE(6)[OF assms(1)] by auto
  ultimately show ?thesis
    using span_iff_finite_linear_combination[OF subring.axioms(1)] assms S' by blast
qed

corollary (in ring) span_smult_incl:
  assumes "subring K R" and "S \<subseteq> carrier R"
  shows "A \<subseteq> Span K S \<Longrightarrow> K <#> A \<subseteq> Span K S"
  using span_smult_closed[OF assms] unfolding set_mult_def by blast

lemma (in ring) insert_linear_dep:
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

  have "K <#> (insert a S) \<subseteq> Span K S"
  proof
    fix h assume "h \<in> K <#> (insert a S)"
    then obtain k s where k: "k \<in> K" and s: "s \<in> insert a S" and h: "h = k \<otimes> s"
      unfolding set_mult_def by auto
    show "h \<in> Span K S"
    proof (cases "s = a")
      assume "s \<noteq> a" hence "s \<in> S"
        using s by blast
      thus ?thesis
        using span_incl[of K S] k h unfolding set_mult_def by auto 
    next
      assume "s = a"
      hence "s \<in> Span K S"
        using assms(2-6) span_iff_finite_linear_combination[OF subring.axioms(1)[OF assms(1)]] by auto
      thus ?thesis
        using span_smult_closed[OF assms(1-2) k, of s] h by simp
    qed
  qed
  thus "Span K (insert a S) \<subseteq> Span K S"
    using span_is_subgroup[OF set_mult_closed[OF subringE(1)[OF assms(1)] assms(2)]]
    by (simp add: span_min')
qed

corollary (in ring) remove_linear_dep:
  assumes "subfield K R" and "S \<subseteq> carrier R"
    and "finite S" "f: S \<rightarrow> K" "\<zero> = (\<Oplus>s \<in> S. (f s) \<otimes> s)" "(f a) \<noteq> \<zero>"
  shows "Span K S = Span K (S - { a })"
proof (cases "a \<in> S")
  assume "a \<notin> S" thus "?thesis" by simp
next
  assume a: "a \<in> S"
  then obtain S' where S': "S = insert a S'" "finite S'" "a \<notin> S'"
    using assms(3) mk_disjoint_insert by force
  have in_carrier: "\<And>s. s \<in> S \<Longrightarrow> f s \<in> carrier R" "S' \<subseteq> carrier R"
    using assms(2, 4) subringE(1)[OF subfieldE(1)[OF assms(1)]] S'(1) by auto
  hence "\<zero> = ((f a) \<otimes> a) \<oplus> (\<Oplus>s \<in> S'. (f s) \<otimes> s)"
    using finsum_insert[OF S'(2-3), of "\<lambda>s. (f s) \<otimes> s"] assms(2,4) unfolding S'(1) assms(5) by blast
  moreover have in_carrier': "(\<Oplus>s \<in> S'. (f s) \<otimes> s) \<in> carrier R" "(f a) \<otimes> a \<in> carrier R"
    using in_carrier assms(2-3) unfolding S'(1) by (simp add: subset_eq)+
  ultimately have "\<ominus> ((f a) \<otimes> a) = (\<Oplus>s \<in> S'. (f s) \<otimes> s)"
    using local.minus_minus minus_equality by fastforce
  hence "(\<ominus> (f a)) \<otimes> a = (\<Oplus>s \<in> S'. (f s) \<otimes> s)"
    using assms(2) in_carrier(1) S'(1) l_minus by auto

  moreover have "\<ominus> (f a) \<in> K"
    using subringE(5)[OF subfieldE(1)[OF assms(1)]] assms(4) a by auto
  hence "\<ominus> (f a) \<in> K - { \<zero> }"
    using assms(6) subringE(1)[OF subfieldE(1)[OF assms(1)]] a in_carrier(1) r_neg by fastforce
  hence inv_fa: "inv (\<ominus> f a) \<in> K" "inv (\<ominus> f a) \<in> carrier R" and "inv (\<ominus> f a) \<otimes> (\<ominus> f a) = \<one>"
    using subfield_m_inv[OF assms(1)] subringE(1)[OF subfieldE(1)[OF assms(1)]] by auto

  ultimately have "a = inv (\<ominus> f a) \<otimes> (\<Oplus>s \<in> S'. (f s) \<otimes> s)"
    using subringE(1)[OF subfieldE(1)[OF assms(1)]] in_carrier'(1) in_carrier(1)[OF a]
    by (smt a add.inv_closed assms(2) l_one m_assoc subsetCE)
  moreover have "(\<lambda>s. f s \<otimes> s) \<in> S' \<rightarrow> carrier R"
    using in_carrier S'(1) by auto
  ultimately have eq1: "a = (\<Oplus>s \<in> S'. inv (\<ominus> f a) \<otimes> ((f s) \<otimes> s))"
    using finsum_rdistr[OF S'(2) inv_fa(2), of "\<lambda>s. (f s) \<otimes> s"] by auto
  moreover have "\<And>s. s \<in> S' \<Longrightarrow> (inv (\<ominus> f a) \<otimes> (f s)) \<otimes> s = inv (\<ominus> f a) \<otimes> ((f s) \<otimes> s)"
    using in_carrier S'(1) m_assoc[OF inv_fa(2)] by auto
  moreover have "(\<lambda>s. (inv (\<ominus> f a) \<otimes> f s) \<otimes> s) \<in> S' \<rightarrow> carrier R"
    using in_carrier S'(1) inv_fa(2) by auto
  ultimately have "a  = (\<Oplus>s \<in> S'. (inv (\<ominus> f a) \<otimes> (f s)) \<otimes> s)"
    using add.finprod_cong'[of S' S' "\<lambda>s. (inv (\<ominus> f a) \<otimes> (f s)) \<otimes> s" "\<lambda>s. inv (\<ominus> f a) \<otimes> ((f s) \<otimes> s)"]
    by simp
  moreover have "(\<lambda>s. inv (\<ominus> f a) \<otimes> f s): S' \<rightarrow> K"
    using  assms(4) subringE(6)[OF subfieldE(1)[OF assms(1)] inv_fa(1)] S'(1) by auto
  ultimately have "Span K S' = Span K (insert a S')"
    using insert_linear_dep[OF subfieldE(1)[OF assms(1)] in_carrier(2) S'(2), of _ a] by auto
  thus ?thesis
    using S' by auto
qed

lemma (in ring) insert_linear_combination:
  assumes "subfield K R" "U \<subseteq> carrier R" and "u \<in> carrier R"
    and "k \<in> K - { \<zero> }" and "v \<in> Span K U"
  shows "Span K (insert u U) = Span K (insert (k \<otimes> u \<oplus> v) U)"
proof
  note subring_props = subringE[OF subfieldE(1)[OF assms(1)]]
  have v: "v \<in> carrier R"
    using subgroup.subset[OF span_is_subgroup'[OF subring_props(1) assms(2)]] assms(5) by auto
  have "k \<otimes> u \<oplus> v \<in> carrier R"
    using assms(3-4) v subring_props(1) by auto
  hence in_carrier: "insert (k \<otimes> u \<oplus> v) U \<subseteq> carrier R" "insert u U \<subseteq> carrier R"
    using assms(2, 3) by auto
  show "Span K (insert u U) \<subseteq> Span K (insert (k \<otimes> u \<oplus> v) U)"
  proof (rule span_min'[OF span_is_subgroup'[OF subring_props(1) in_carrier(1)]])
    have "K <#> insert u U = (K <#> { u }) \<union> (K <#> U)"
      unfolding set_mult_def by blast

    moreover
    have "K <#> insert (k \<otimes> u \<oplus> v) U \<subseteq> Span K (insert (k \<otimes> u \<oplus> v) U)"
      using span_incl by simp
    hence "K <#> U \<subseteq> Span K (insert (k \<otimes> u \<oplus> v) U)"
      unfolding set_mult_def by blast

    moreover
    have "\<And>k'. k' \<in> K \<Longrightarrow> k' \<otimes> u \<in> Span K (insert (k \<otimes> u \<oplus> v) U)"
    proof -
      fix k' assume k': "k' \<in> K"
      hence "k' = k' \<otimes> (inv k \<otimes> k)"
        unfolding subfield_m_inv(3)[OF assms(1, 4)] using subring_props(1) by auto
      also have " ... = (k' \<otimes> inv k) \<otimes> k"
        using k' m_assoc[of k' "inv k" k] subfield_m_inv(1)[OF assms(1, 4)]
              subring_props(1) assms(4) by (metis DiffD1 subset_eq)
      finally have "k' = (k' \<otimes> inv k) \<otimes> k" .
      hence "k' \<otimes> u = ((k' \<otimes> inv k) \<otimes> k) \<otimes> u"
        by simp
      moreover have "k' \<in> carrier R" "k \<in> carrier R" "inv k \<in> carrier R"
        using k' subring_props(1) subfield_m_inv(1)[OF assms(1, 4)] assms(4) by auto
      ultimately have eq: "k' \<otimes> u = (k' \<otimes> inv k) \<otimes> (k \<otimes> u \<oplus> v) \<oplus> (\<ominus> (k' \<otimes> inv k) \<otimes> v)"
        by (simp add: add.inv_solve_right assms(3) l_minus m_assoc r_distr v)

      have in_K: "k' \<otimes> inv k \<in> K" "\<ominus> (k' \<otimes> inv k) \<in> K"
        using k' subfield_m_inv(1)[OF assms(1, 4)] subring_props(5, 6) by auto
      hence "(k' \<otimes> inv k) \<otimes> (k \<otimes> u \<oplus> v) \<in> Span K (insert (k \<otimes> u \<oplus> v) U)"
        using span_incl[of K "insert (k \<otimes> u \<oplus> v) U"]
        unfolding set_mult_def by blast

      moreover have "v \<in> Span K (insert (k \<otimes> u \<oplus> v) U)"
        using mono_span[OF _ subring_props(1) _ in_carrier(1), of K U] assms(5) by auto
      hence "\<ominus> (k' \<otimes> inv k) \<otimes> v \<in> Span K (insert (k \<otimes> u \<oplus> v) U)"
        using span_smult_closed[OF subfieldE(1)[OF assms(1)] in_carrier(1) in_K(2)] by simp

      ultimately show "k' \<otimes> u \<in> Span K (insert (k \<otimes> u \<oplus> v) U)"
        unfolding eq span_def using generate.eng[of _ "add_monoid R"] by simp
    qed
    hence "K <#> { u } \<subseteq> Span K (insert (k \<otimes> u \<oplus> v) U)"
      unfolding set_mult_def by blast
    ultimately show "K <#> (insert u U) \<subseteq> Span K (insert (k \<otimes> u \<oplus> v) U)"
      by auto
  qed

  show "Span K (insert (k \<otimes> u \<oplus> v) U) \<subseteq> Span K (insert u U)"
  proof (rule span_min'[OF span_is_subgroup'[OF subring_props(1) in_carrier(2)]])
    have "K <#> insert (k \<otimes> u \<oplus> v) U = (K <#> { k \<otimes> u \<oplus> v }) \<union> (K <#> U)"
      unfolding set_mult_def by blast

    moreover
    have "K <#> insert u U \<subseteq> Span K (insert u U)"
      using span_incl by simp
    hence "K <#> U \<subseteq> Span K (insert u U)"
      unfolding set_mult_def by blast

    moreover
    have "\<And>k'. k' \<in> K \<Longrightarrow> k' \<otimes> (k \<otimes> u \<oplus> v) \<in> Span K (insert u U)"
    proof -
      fix k' assume k': "k' \<in> K"
      hence "k' \<otimes> (k \<otimes> u \<oplus> v) = (k' \<otimes> (k \<otimes> u)) \<oplus> (k' \<otimes> v)"
        using r_distr[of k' "k \<otimes> u" v] assms(3-4) v subring_props(1)
        by (meson DiffD1 m_closed r_distr set_rev_mp)
      also have " ... = ((k' \<otimes> k) \<otimes> u) \<oplus> (k' \<otimes> v)"
        using m_assoc[of k' k u] k' assms(3-4) subring_props(1) by force
      finally have "k' \<otimes> (k \<otimes> u \<oplus> v) = ((k' \<otimes> k) \<otimes> u) \<oplus> (k' \<otimes> v)" .

      moreover have "k' \<otimes> k \<in> K"
        using subring_props(6) k' assms(4) by simp
      hence "(k' \<otimes> k) \<otimes> u \<in> Span K (insert u U)"
        using span_incl[of K "insert u U"] unfolding set_mult_def by blast

      moreover have "v \<in> Span K (insert u U)"
        using mono_span[OF _ subring_props(1) _ in_carrier(2), of K U] assms(5) by auto
      hence "k' \<otimes> v \<in> Span K (insert u U)"
        using span_smult_closed[OF subfieldE(1)[OF assms(1)] in_carrier(2) k', of v] by simp

      ultimately show "k' \<otimes> (k \<otimes> u \<oplus> v) \<in> Span K (insert u U)"
        unfolding span_def using generate.eng[of _ "add_monoid R" "K <#> (insert u U)"] by auto
    qed
    hence "K <#> { k \<otimes> u \<oplus> v } \<subseteq> Span K (insert u U)"
      unfolding set_mult_def by blast

    ultimately show "K <#> insert (k \<otimes> u \<oplus> v) U \<subseteq> Span K (insert u U)"
      by auto
  qed
qed

lemma (in ring) span_strict_incl:
  assumes "subring K R" and "B \<subseteq> carrier R" and "S \<subseteq> carrier R"
    and "Span K B \<subset> Span K S"
  shows "\<exists>s \<in> S. s \<notin> Span K B"
proof (rule ccontr)
  assume "\<not> (\<exists>s\<in>S. s \<notin> Span K B)"
  hence "S \<subseteq> Span K B"
    by blast
  hence "K <#> S \<subseteq> Span K B"
    using span_smult_incl[OF assms(1-2)] by simp
  hence "Span K S \<subseteq> Span K B"
    using span_min'[OF span_is_subgroup'[OF subringE(1)[OF assms(1)] assms(2)]] by simp
  thus False
    using assms(4) by simp
qed

lemma (in ring) span_strict_incl_insert:
  assumes "subfield K R" and "u \<in> carrier R" "U \<subseteq> carrier R" "finite U"
    and "Span K U \<subset> Span K (insert u U)"
  shows "a \<in> Span K (insert u U) \<Longrightarrow> \<exists>!k. \<exists>!v. k \<in> K \<and> v \<in> Span K U \<and> a = k \<otimes> u \<oplus> v"
    and "\<lbrakk> k \<in> K; v \<in> Span K U; k \<otimes> u \<oplus> v \<in> Span K U \<rbrakk> \<Longrightarrow> k = \<zero>"
proof -
  note subring_props = subringE[OF subfieldE(1)[OF assms(1)]]

  show aux_lemma:
    "\<And>k v. \<lbrakk> k \<in> K; v \<in> Span K U; k \<otimes> u \<oplus> v \<in> Span K U \<rbrakk> \<Longrightarrow> k = \<zero>"
  proof -
    fix k v
    assume A: "k \<in> K" "v \<in> Span K U" "k \<otimes> u \<oplus> v \<in> Span K U"
    have "U \<subseteq> Span K U"
      using span_incl[of K U] subring_props(3) assms(3)
      unfolding set_mult_def by force
    hence "u \<notin> Span K U"
      using span_strict_incl[OF subfieldE(1)[OF assms(1)] assms(3) _ assms(5)] assms(2-3) by blast
    show "k = \<zero>"
    proof (rule ccontr)
      assume "k \<noteq> \<zero>"
      hence "inv k \<in> K" "inv k \<in> carrier R" "inv k \<otimes> k = \<one>"
        using subfield_m_inv[OF assms(1)] A(1) subring_props(1) by auto
      moreover have "k \<otimes> u \<oplus> v \<oplus> \<ominus> v \<in> Span K U"
        using span_is_subgroup'[OF subring_props(1) assms(3)] A(2-3) add.subgroupE(3-4) by simp
      hence "k \<otimes> u \<in> Span K U"
        using span_in_carrier[OF subring_props(1) assms(3)] A(1-2) assms(2) subring_props(1)
        by (metis add.inv_solve_right add.m_closed contra_subsetD m_closed)
      ultimately have "u \<in> Span K U"
        using span_smult_closed[OF subfieldE(1)[OF assms(1)] assms(3), of "inv k" "k \<otimes> u"]
              assms(2) A(1) subring_props(1) m_assoc[OF _ _ assms(2), of "inv k" k] by auto
      from \<open>u \<in> Span K U\<close> and \<open>u \<notin> Span K U\<close> show False by simp
    qed
  qed

  assume "a \<in> Span K (insert u U)"
  then obtain k v where k: "k \<in> K" and v: "v \<in> Span K U" and a: "a = k \<otimes> u \<oplus> v"
    using semi_linear_decomp[OF subring.axioms(1)[OF subfieldE(1)[OF assms(1)]] assms(2-4)] by blast

  moreover
  have "\<And>k' v'. \<lbrakk> k' \<in> K; v' \<in> Span K U \<rbrakk> \<Longrightarrow> a = k' \<otimes> u \<oplus> v' \<Longrightarrow> k = k' \<and> v = v'"
  proof -
    fix k' v'
    assume k': "k' \<in> K" and v': "v' \<in> Span K U" and a': "a = k' \<otimes> u \<oplus> v'"
    hence in_carrier: "k' \<in> carrier R" "k \<in> carrier R" "v \<in> carrier R" "v' \<in> carrier R"
      using subring_props(1) span_in_carrier[OF subring_props(1) assms(3)] k v by auto

    hence "v = \<ominus> (k \<otimes> u) \<oplus> (k' \<otimes> u) \<oplus> v'"
      using assms(2) a' unfolding a
      by (metis add.inv_closed add.m_assoc m_closed r_neg1)
    also have " ... = ((\<ominus> k) \<oplus> k') \<otimes> u \<oplus> v'"
      using in_carrier assms(2) by algebra
    finally have eq1: "v = ((\<ominus> k) \<oplus> k') \<otimes> u \<oplus> v'" .
    hence eq2: "(\<ominus> k) \<oplus> k' = \<zero>"
      using aux_lemma k k' v v' subring_props(5,7) by auto
    hence "v = v'"
      using eq1 assms(2) in_carrier by auto
    thus "k = k' \<and> v = v'"
      using in_carrier(1,2) eq2 r_neg2 by fastforce
  qed

  ultimately show "\<exists>!k. \<exists>!v. k \<in> K \<and> v \<in> Span K U \<and> a = k \<otimes> u \<oplus> v"
    by metis
qed

theorem (in ring) baillon_replacement_theorem:
  assumes "subfield K R"
    and "u \<in> carrier R" "U \<subseteq> carrier R" "V \<subseteq> carrier R" and "finite U" and "V \<noteq> {}"
    and "Span K (insert u U) = Span K V"
  shows "\<exists>v \<in> V. Span K (insert v U) = Span K V"
proof -
  note subring_props = subringE[OF subfieldE(1)[OF assms(1)]]

  show ?thesis
  proof (cases "Span K U = Span K V")
    obtain v where v: "v \<in> V"
      using assms(6) by auto
    hence "\<one> \<otimes> v \<in> K <#> V"
      using subring_props(3) assms(4) unfolding set_mult_def by blast
    hence in_Span: "v \<in> Span K V"
      using span_incl[of K V] assms(4) v by fastforce 

    assume case1: "Span K U = Span K V"
    hence "v \<in> Span K U"
      using in_Span by simp
    hence "Span K U = Span K (insert v U)"
      using insert_linear_dep[OF subfieldE(1)[OF assms(1)] assms(3,5), of _ v]
            span_as_linear_combinations[OF subring.axioms(1)[OF subfieldE(1)[OF assms(1)]] assms(5,3)]
      by blast
    thus ?thesis
      using v case1 by blast
  next
    assume case2: "Span K U \<noteq> Span K V"
    hence subset: "Span K U \<subset> Span K (insert u U)"
      using mono_span[OF _ subring_props(1), of K U "insert u U"] assms(2-3,7) by auto
    then obtain v where v: "v \<in> V" "v \<notin> Span K U"
      using span_strict_incl[OF subfieldE(1)[OF assms(1)] assms(3-4)] case2 assms(7)
      by auto
    then obtain k v' where k: "k \<in> K" and v': "v' \<in> Span K U" "v = k \<otimes> u \<oplus> v'"
      using span_strict_incl_insert(1)[OF assms(1-3,5) subset]
            span_base_incl[OF subring_props(3) assms(4)] v(1) assms(7)
      by blast
    have "v = v'" if "k = \<zero>"
      using that v' assms(2) span_in_carrier[OF subring_props(1) assms(3)] by auto
    hence "k \<noteq> \<zero>"
      using v(2) v'(1) by auto
    thus ?thesis
      using insert_linear_combination[OF assms(1,3,2) _ v'(1), of k] k v'(2) v(1) assms(7) by auto
  qed
qed

lemma well_ordering_principle:
  fixes A :: "nat set" assumes "A \<noteq> {}" shows "\<exists>n \<in> A. \<forall>k \<in> A. n \<le> k"
proof -
  obtain m where m: "m \<in> A"
    using assms by blast
  then obtain n where n: "n \<in> A" "\<And>k. \<lbrakk> k \<in> A; k \<le> m \<rbrakk> \<Longrightarrow> n \<le> k"
    using Min_eq_iff[of "{..m} \<inter> A"] by auto
  hence "\<And>k. k \<in> A \<Longrightarrow> n \<le> k"
    using m le_trans nat_le_linear by blast
  thus ?thesis
    using n(1) by auto
qed

theorem (in ring) replacement_theorem:
  assumes "subfield K R"
    and "U \<subseteq> carrier R" "V \<subseteq> carrier R" and "finite U" and "V \<noteq> {}"
    and "Span K U = Span K V"
  shows "\<exists>V' \<subseteq> V. card V' \<le> card U \<and> Span K V' = Span K V"
proof -
  define B where
    "B = { (U', V'). U' \<subseteq> U \<and> V' \<subseteq> V \<and> finite V' \<and>
           card U' + card V' \<le> card U \<and> Span K (U' \<union> V') = Span K V }"
  hence "(U, {}) \<in> B"
    using assms(6) by auto
  hence "card ` (fst ` B) \<noteq> {}"
    by auto
  then obtain n where n: "n \<in> card ` (fst ` B)" "\<And>k. k \<in> card ` (fst ` B) \<Longrightarrow> n \<le> k"
    using well_ordering_principle[of "card ` (fst ` B)"] by blast
  then obtain U' V'
    where V': "U' \<subseteq> U" "V' \<subseteq> V" "Span K (U' \<union> V') = Span K V" "finite V'"
    and card: "card U' + card V' \<le> card U" "card U' = n"
    using B_def by auto
  show ?thesis
  proof (cases "n = 0")
    assume eq_zero: "n = 0" hence "U' = {}"
      using V'(1) assms(4) card(2) finite_subset by fastforce
    thus ?thesis
      using V'(2-3) card eq_zero by auto
  next
    assume diff_zero: "n \<noteq> 0"
    then obtain u U'' where u: "u \<notin> U''" "U' = insert u U''"
      using card(2) by (metis Set.set_insert all_not_in_conv card_empty)
    hence "Span K (insert u (U'' \<union> V')) = Span K V"
      using V'(3) by simp
    moreover have "finite (U'' \<union> V')"
      using V'(1,4) assms(4) u(2) finite_Un finite_subset by auto 
    ultimately obtain v where v:"v \<in> V" "Span K (insert v (U'' \<union> V')) = Span K V"
      using baillon_replacement_theorem[OF assms(1) _ _ assms(3) _ assms(5), of u "U'' \<union> V'"]
            assms(2-3) V'(1-2) u(2) by force
    hence "Span K (U'' \<union> (insert v V')) = Span K V"
      by simp
    moreover have "finite (insert v V')" and "insert v V' \<subseteq> V" and "U'' \<subseteq> U"
      using V'(1-2,4) v(1) u by auto
    moreover have fin_U': "finite U'"
      using V'(1) assms(4) finite_subset by auto
    hence "card U'' + card (insert v V') \<le> Suc (card U'') + card V'"
      by (simp add: V'(4) card_insert_if)
    hence "card U'' + card (insert v V') \<le> card U"
      using u(1) V'(4) fin_U' card(1) unfolding u(2) by auto
    ultimately have "(U'', (insert v V')) \<in> B"
      unfolding B_def by auto
    moreover have "card U'' < card U'"
      using u(1) fin_U' unfolding u(2) by auto
    ultimately have False
      using n(2) unfolding card(2) by force
    thus ?thesis by simp
  qed
qed


theorem (in ring) linear_ind_iff:
  assumes "subfield K R"
    and "S \<subseteq> carrier R" and "finite S"
  shows "linear_ind K S \<Longrightarrow> (\<And>f. \<lbrakk> f: S \<rightarrow> K; (\<zero> = (\<Oplus>s \<in> S. (f s) \<otimes> s)) \<rbrakk> \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> f s = \<zero>))"
    and "(\<And>f. \<lbrakk> f: S \<rightarrow> K; (\<zero> = (\<Oplus>s \<in> S. (f s) \<otimes> s)) \<rbrakk> \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> f s = \<zero>)) \<Longrightarrow> linear_ind K S"
  sorry
(*
proof -
  assume "linear_ind K S"
  show "\<And>f. \<lbrakk> f: S \<rightarrow> K; (\<zero> = (\<Oplus>s \<in> S. (f s) \<otimes> s)) \<rbrakk> \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> f s = \<zero>)"
  proof -
    fix f assume f: "f: S \<rightarrow> K" "(\<zero> = (\<Oplus>s \<in> S. (f s) \<otimes> s))"
    show "\<And>s. s \<in> S \<Longrightarrow> f s = \<zero>"
    proof -
      fix s assume "s \<in> S"
      show "f s = \<zero>"
      proof (rule ccontr)
    proof (cases "S = {}")
      assume "S = {}" thus "\<And>s. s \<in> S \<Longrightarrow> f s = \<zero>"
        using f(1) by auto
    next
      assume "S \<noteq> {}" show "\<forall>s. s \<in> S \<Longrightarrow> f s = \<zero>"
    proof (rule ccontr)
      assume "f ` S \<noteq> { \<zero> }"
      then obtain a where "a \<in> S" "f a \<noteq> \<zero>"
*)

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

(*
lemma (in ring) linear_ind_imp_unique_combination:
  assumes "finite B" "linear_ind K B"
  shows "\<And>f. \<lbrakk> f: B \<rightarrow> K; \<zero> = (\<Oplus>s \<in> S. (f s) \<otimes> s) \<rbrakk> \<Longrightarrow> f ` B = { \<zero> }"

lemma (in ring) linear_ind_imp_finite: "linear_ind K B \<Longrightarrow> finite B"
  unfolding linear_ind_def dim_def

lemma (in ring)
  assumes "linear_ind K B" "Span K B \<subseteq> S"
  shows "(dim over K) A \<ge> card B"
*)

end