
theory Signature
  imports Embedded_Algebras Polynomials Generated_Fields "HOL-Library.Multiset" Finite_Extensions

begin

definition (in ring) pdivides ::"'a list \<Rightarrow>'a list \<Rightarrow> bool" (infixl "pdivides" 50)
  where "p pdivides q \<equiv> (\<exists> r. r \<noteq> [] \<and> polynomial R r \<and> p = poly_mult q r)"

definition (in ring) pirreductible :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "pirreductible K p \<equiv> polynomial R p \<and> p \<noteq> []"

lemma (in ring) pirreductibleE :
  assumes "pirreductible K p"
  shows "p \<noteq> []" "polynomial R p" "degree p \<ge> 1" "set p \<subseteq> K" "lead_coeff p = \<one>"
        "\<And> q r. \<lbrakk>polynomial R q ; set q \<subseteq> K; polynomial R r ; set r \<subseteq> K ; p = poly_mult q r\<rbrakk> \<Longrightarrow>
                 q \<in> Units(univ_poly (R\<lparr>carrier := K\<rparr>)) \<or> r \<in> Units (univ_poly (R\<lparr>carrier := K\<rparr>))"
  sorry

lemma (in ring) Irr_exists :
  assumes "subfield K R"
    and "(algebraic over K) x"
    and "x \<in> carrier R"
  shows "\<exists>! p. (irreductible K p \<and> eval p x = \<zero>)"
  sorry


lemma (in ring) algebraic_self :
  assumes "subring k R"
    and "x \<in> k"
  shows "(algebraic over k) x"
  sorry


definition (in ring) Irr :: "'a set => 'a => 'a list"
  where "Irr K x \<equiv> THE p. (pirreductible K p \<and> eval p x = \<zero>)"

lemma (in ring) Irr_self :
  assumes "subfield K R"
    and "x \<in> K"
  shows "Irr K x = [\<one>,x]"
  sorry

lemma (in ring) IrrE :
  assumes "subfield K R"
    and "(algebraic over K) x"
    and "x \<in> carrier R"
  shows "pirreductible K (Irr K x)" "eval (Irr K x) x = \<zero>"
  using theI'[OF Irr_exists[OF assms]] unfolding Irr_def
  by blast+



lemma (in ring) IrrE' :
  assumes "subfield K R"
    and "(algebraic over K) x"
    and "x \<in> carrier R"
  shows "(Irr K x) \<noteq> []" "polynomial R (Irr K x)" "1 \<le> degree (Irr K x)"
        "set (Irr K x) \<subseteq> K" "lead_coeff (Irr K x) = \<one>"
  using pirreductibleE[OF IrrE(1)[OF assms]] by auto


definition (in ring) multiplicity :: "'a \<Rightarrow> nat \<Rightarrow>'a list \<Rightarrow> bool"
  where "multiplicity x n p \<equiv> ([\<one>,x][^]\<^bsub>univ_poly R\<^esub> n) pdivides p
                            \<and>\<not>(([\<one>,x][^]\<^bsub>univ_poly R\<^esub> (Suc n)) pdivides p)"

definition (in ring) roots :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a multiset"
  where "roots K p \<equiv> Abs_multiset (\<lambda>x \<in> K. (THE n. multiplicity x n p))"

lemma (in ring) roots_number_inf_degree :
  assumes "subfield K R"
    and "polynomial R p"
  shows "size (roots K p) \<le> degree p"
  sorry

definition (in ring) split :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "split K p \<equiv> polynomial R p \<and> (size (roots K p)) = degree p"

lemma (in field) simple_extension_field :
  assumes "subfield k R"
    and "x \<in> carrier R"
  shows "subfield (simple_extension k x) R"
  sorry

lemma (in field) finite_extension_field :
  assumes "subfield k R"
    and "set xs \<subseteq> carrier R"
  shows "subfield (finite_extension k xs) R" using assms(2)
proof (induction xs)
  case Nil
  hence "k = (finite_extension k [])" by auto
  then show ?case using assms by auto
next
  case (Cons a xs)
  hence "subfield (finite_extension k xs) R" by simp
  moreover have "finite_extension k (a # xs) = simple_extension (finite_extension k xs) a"
    by simp
  ultimately show ?case
    using simple_extension_field Cons by auto
qed

lemma (in field) algebraic_simple_extension :
  assumes "subfield k R"
    and "(algebraic over k) x"
  shows "\<And> y. y \<in> (simple_extension k x) \<Longrightarrow> (algebraic over k) y"
  sorry
end