(* ************************************************************************** *)
(* Title:      Finite_Extensions.thy                                          *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Finite_Extensions
  imports Embedded_Algebras
    
begin

section \<open>Finite Extensions\<close>

definition (in ring) algebraic :: "['a, 'a set] \<Rightarrow> bool" (infix "algebraic" 65)
  where "x algebraic K \<longleftrightarrow> (\<exists>p \<noteq> []. polynomial (R \<lparr> carrier := K \<rparr>) p \<and> eval p x = \<zero>)"

definition (in ring) transcedental :: "['a, 'a set] \<Rightarrow> bool" (infix "transcedental" 65)
  where "x transcedental K \<longleftrightarrow> \<not> (x algebraic K)"

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
  shows "subfield (simple_ext R K a) R \<longleftrightarrow> a algebraic K"
  sorry


end