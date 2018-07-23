
theory Signature
  imports Embedded_Algebras Polynomials Generated_Fields "HOL-Library.Multiset" Finite_Extensions

begin

(*
[Polynomial_Divisibility]
definition (in ring) pdivides ::"'a list \<Rightarrow>'a list \<Rightarrow> bool" (infixl "pdivides" 50)
  where "p pdivides q \<equiv> (\<exists> r. r \<noteq> [] \<and> polynomial R r \<and> p = poly_mult q r)"
*)

(*
[Polynomial_Divisibility]
definition (in ring) pirreductible :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "pirreductible K p \<equiv> polynomial R p \<and> p \<noteq> []"
*)

(*
[Polynomial_Divisibility]
lemma (in ring) pirreductibleE :
  assumes "pirreductible K p"
  shows "p \<noteq> []" "polynomial R p" "degree p \<ge> 1" "set p \<subseteq> K" "lead_coeff p = \<one>"
        "\<And> q r. \<lbrakk>polynomial R q ; set q \<subseteq> K; polynomial R r ; set r \<subseteq> K ; p = poly_mult q r\<rbrakk> \<Longrightarrow>
                 q \<in> Units(univ_poly (R\<lparr>carrier := K\<rparr>)) \<or> r \<in> Units (univ_poly (R\<lparr>carrier := K\<rparr>))"
  sorry
*)

lemma (in ring) Irr_exists:
  assumes "subfield K R"
    and "(algebraic over K) x"
    and "x \<in> carrier R"
  shows "\<exists>!p \<in> carrier (K[X]). lead_coeff p = \<one> \<and> pirreducible K p \<and> eval p x = \<zero>"
  sorry


lemma (in ring) algebraic_self:
  assumes "subring k R"
    and "x \<in> k"
  shows "(algebraic over k) x"
  sorry

(*
definition (in ring) Irr :: "'a set => 'a => 'a list"
  where "Irr K x \<equiv> THE p. (pirreducible K p \<and> eval p x = \<zero>)"
*)

lemma (in ring) Irr_self:
  assumes "subfield K R"
    and "x \<in> K"
  shows "Irr K x = [ \<one>, \<ominus> x]"
  sorry

lemma (in ring) IrrE:
  assumes "subfield K R"
    and "(algebraic over K) x"
    and "x \<in> carrier R"
  shows "pirreducible K (Irr K x)" "eval (Irr K x) x = \<zero>"
  sorry
(*
  using theI'[OF Irr_exists[OF assms]] unfolding Irr_def
  by blast+
*)


lemma (in ring) IrrE' :
  assumes "subfield K R"
    and "(algebraic over K) x"
    and "x \<in> carrier R"
  shows "(Irr K x) \<noteq> []" "polynomial K (Irr K x)" "1 \<le> degree (Irr K x)"
        "set (Irr K x) \<subseteq> K" "lead_coeff (Irr K x) = \<one>"
  sorry
(* using pirreductibleE[OF IrrE(1)[OF assms]] by auto *)


definition (in ring) multiplicity :: "'a set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow>'a list \<Rightarrow> bool"
  where "multiplicity K x n p \<equiv> ([ \<one>, \<ominus> x ][^]\<^bsub>K[X]\<^esub> n) divides\<^bsub>(univ_poly R K)\<^esub> p
                            \<and>\<not>(([ \<one>, \<ominus> x ][^]\<^bsub>K[X]\<^esub> (Suc n)) divides\<^bsub>(univ_poly R K)\<^esub> p)"

definition (in ring) roots :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a multiset"
  where "roots K p \<equiv> Abs_multiset (\<lambda>x \<in> K. (THE n. multiplicity K x n p))"

lemma (in field) roots_well_defined :
  assumes "subfield K R"
    and "polynomial K p"
    and "p \<noteq> []"
  shows "\<And>x. x \<in> K \<Longrightarrow> \<exists>! n. multiplicity K x n p""(\<lambda>y \<in> K. (THE n. multiplicity K y n p)) \<in> multiset"
  sorry

lemma (in ring) multiplicity_consistent :
  assumes "subring k R"
    and "set p \<subseteq> k"
    and "polynomial k p"
  shows "multiplicity k x n p = ring.multiplicity (R\<lparr>carrier := k\<rparr>) k x n p"
  sorry

lemma (in ring) roots_number_inf_degree :
  assumes "subfield K R"
    and "polynomial K p" "p \<noteq> []"
  shows "size (roots K p) \<le> degree p"
  sorry

definition (in ring) split :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "split K p \<equiv> polynomial K p \<and> (size (roots K p)) = degree p"

lemma (in field) simple_extension_field :
  assumes "subfield k R"
    and "x \<in> carrier R" and "(algebraic over K) x"
  shows "subfield (simple_extension k x) R"
  sorry

lemma (in field) simple_extension_incl :
  assumes "subfield k R"
    and "x \<in> carrier R"
  shows "k \<subseteq> simple_extension k x"
proof
  fix y assume hyp : "y \<in> k"
  thus "y \<in>simple_extension k x"
    using lin[OF zero hyp,of x]l_null subfieldE(3) assms
    by fastforce
qed


lemma (in field) finite_extension_field :
  assumes "subfield k R"
    and "set xs \<subseteq> carrier R" "\<And>x. x \<in> set xs \<Longrightarrow> (algebraic over K) x"
  shows "subfield (finite_extension k xs) R" using assms(2-3)
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
    and "x \<in> carrier R"
  shows "\<And> y. y \<in> (simple_extension k x) \<Longrightarrow> (algebraic over k) y"
  sorry

lemma (in field) algebraic_finite_extension :
  assumes "subfield k R"
    and "\<And> x. x \<in> set xs \<Longrightarrow> (algebraic over k) x \<and> x \<in> carrier R"
  shows "\<And> y. y \<in> (finite_extension k xs) \<Longrightarrow> (algebraic over k) y"
  sorry

lemma (in field) algebraic_simple_extension_backward :
  assumes "subfield k R"
    and "(algebraic over k) x"
    and "x \<in> carrier R"
    and "y \<in> carrier R"
    and "(algebraic over simple_extension k x) y"
  shows "(algebraic over k) y"
    sorry

lemma (in field) algebraic_finite_extension_backward :
  assumes "subfield k R"
    and "\<And> x. x \<in> set xs \<Longrightarrow> (algebraic over k) x \<and> x \<in> carrier R"
    and "y \<in> carrier R"
    and "(algebraic over finite_extension k xs) y"
  shows "(algebraic over k) y"
  sorry

lemma (in field) algebraic_simple_extension_trans :
  assumes "subfield k R"
    and "x \<in> carrier R"
    and "y \<in> carrier R"
    and "(algebraic over k) y"
  shows "(algebraic over simple_extension k x) y"
  sorry

lemma (in field) algebraic_finite_extension_trans :
  assumes "subfield k R"
    and "set xs \<subseteq> carrier R"
    and "y \<in> carrier R"
    and "(algebraic over k) y"
  shows "(algebraic over finite_extension k xs) y"
  sorry

lemma (in field) split_add_trans :
  assumes "subfield k R"
    and "x \<in> carrier R"
    and "y \<in> k"
    and "split k (Irr k x)"
  shows "split k (Irr k (x \<oplus> y)) "
  sorry

lemma (in field) split_mult_trans :
  assumes "subfield k R"
    and "x \<in> carrier R"
    and "y \<in> k"
    and "split k (Irr k x)"
  shows "split k (Irr k (y \<otimes> x)) "
  sorry

lemma (in field) split_Irr_incl_trans :
  assumes "subfield K R"
    and "x \<in> carrier R"
    and "(algebraic over k) x"
    and "k \<subseteq> K"
  shows "split K (Irr K x)  \<longleftrightarrow> split K (Irr k x)"
  sorry



end