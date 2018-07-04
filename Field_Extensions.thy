(* ************************************************************************** *)
(* Title:      Field_Extensions.thy                                           *)
(* Author:     Martin Baillon                                                 *)
(* ************************************************************************** *)

theory Field_Extensions
  imports Embedded_Algebras Polynomials Generated_Fields "HOL-Library.Multiset" Finite_Extensions

begin

definition (in ring) multiplicity :: "'a \<Rightarrow> nat \<Rightarrow>'a list \<Rightarrow> bool"
  where "multiplicity x n p \<equiv> ([\<one>,x][^]\<^bsub>univ_poly R\<^esub> n pdivides p)
                            \<and>\<not>(([\<one>,x][^]\<^bsub>univ_poly R\<^esub> (Suc n)) pdivides p)"

definition (in ring) roots :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a multiset"
  where "roots K p \<equiv> Abs_multiset (\<lambda>x \<in> K. (THE n. multiplicity x n p))"

definition (in ring) split :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "split K p \<equiv> polynomial R p \<and> (size (roots K p)) = degree p"

locale field_extension = 
  R?: field R
  for K :: "'a set" and k :: "'a set" and p :: "'a list" and R :: "('a, 'b) ring_scheme" (structure)
 + assumes split : "split (carrier R) p"
     and K : "subfield K R"
     and k : "subfield k R"



lemma (in ring) IrrE :
  assumes "(algebraic over K) x"
    and "x \<in> carrier R"
    and "subfield K R"
  shows "pirreductible (R\<lparr>carrier := K\<rparr>) Irr K x""eval (Irr K x)x =\<zero>""(Irr K x) \<noteq> []"
        "set (Irr K X) \<subseteq> K" "lead_coeff (Irr K x) = \<one>"
  sorry

definition (in ring) galoisian :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "galoisian K k \<equiv> (subfield K R) \<and> (\<forall> x \<in> K. (algebraic over k) x \<and> (split K (Irr k x)))"




end