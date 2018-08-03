theory Algebraic_Closure
  imports Indexed_Polynomials Polynomial_Divisibility

begin

section \<open>Algebraic Closure\<close>

subsection \<open>Definitions\<close>

inductive iso_incl :: "'a ring \<Rightarrow> 'a ring \<Rightarrow> bool" (infixl "\<lesssim>" 65) for A B
  where "id \<in> ring_hom A B \<Longrightarrow> iso_incl A B"

definition law_restrict :: "('a, 'b) ring_scheme \<Rightarrow> 'a ring"
  where "law_restrict R \<equiv> (ring.truncate R)
           \<lparr> mult := (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<otimes>\<^bsub>R\<^esub> b),
              add := (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<oplus>\<^bsub>R\<^esub> b) \<rparr>"

definition (in ring) \<sigma> :: "'a list \<Rightarrow> (('a list multiset) \<Rightarrow> 'a) list"
  where "\<sigma> P = map indexed_const P"

abbreviation (in ring) extensions :: "(('a list multiset) \<Rightarrow> 'a) ring set"
  where "extensions \<equiv> { L \<comment> \<open>such that\<close>.
           \<comment> \<open>i\<close>   (field L) \<and>
           \<comment> \<open>ii\<close>  (indexed_const \<in> ring_hom R L) \<and>
           \<comment> \<open>iii\<close> (\<forall>\<P> \<in> carrier L. carrier_coeff \<P>) \<and>
           \<comment> \<open>iv\<close>  (\<forall>\<P> \<in> carrier L. \<forall>P \<in> carrier (poly_ring R).
                       \<not> index_free \<P> P \<longrightarrow> \<X>\<^bsub>P\<^esub> \<in> carrier L \<and> (ring.eval L) (\<sigma> P) \<X>\<^bsub>P\<^esub> = \<zero>\<^bsub>L\<^esub>) }"

definition (in ring) range_extensions :: "(('a list multiset) \<Rightarrow> 'a) ring set" ("\<S>")
  where "\<S> = law_restrict ` extensions"


subsection \<open>Basic Properties\<close>

lemma (in ring) law_restrict_is_ring: "ring (law_restrict R)"
  by (unfold_locales) (auto simp add: law_restrict_def Units_def ring.defs,
      simp_all add: a_assoc a_comm m_assoc l_distr r_distr a_lcomm)

lemma (in field) law_restrict_is_field: "field (law_restrict R)"
proof -
  interpret L: ring "law_restrict R"
    using law_restrict_is_ring .
  have "inv a \<in> carrier R" and "a \<otimes> (inv a) = \<one>" if "a \<noteq> \<zero>" and "a \<in> carrier R" for a
    using that field_Units by auto
  thus ?thesis
    by (unfold_locales) (auto simp add: law_restrict_def Units_def ring.defs,
        simp_all add: m_comm integral_iff, blast)
qed

lemma law_restrict_iso_imp_eq:
  assumes "id \<in> ring_iso (law_restrict A) (law_restrict B)" and "ring A" and "ring B"
  shows "law_restrict A = law_restrict B"
proof -
  have "carrier A = carrier B"
    using ring_iso_memE(5)[OF assms(1)] unfolding bij_betw_def law_restrict_def by (simp add: ring.defs)
  hence mult: "a \<otimes>\<^bsub>law_restrict A\<^esub> b = a \<otimes>\<^bsub>law_restrict B\<^esub> b"
    and add:  "a \<oplus>\<^bsub>law_restrict A\<^esub> b = a \<oplus>\<^bsub>law_restrict B\<^esub> b" for a b
    using ring_iso_memE(2-3)[OF assms(1)] unfolding law_restrict_def by (auto simp add: ring.defs)
  have "monoid.mult (law_restrict A) = monoid.mult (law_restrict B)"
    using mult by auto
  moreover have "add (law_restrict A) = add (law_restrict B)"
    using add by auto
  moreover from \<open>carrier A = carrier B\<close> have "carrier (law_restrict A) = carrier (law_restrict B)"
    unfolding law_restrict_def by (simp add: ring.defs)
  moreover have "\<zero>\<^bsub>law_restrict A\<^esub> = \<zero>\<^bsub>law_restrict B\<^esub>"
    using ring_hom_zero[OF _ assms(2-3)[THEN ring.law_restrict_is_ring]] assms(1)
    unfolding ring_iso_def by auto
  moreover have "\<one>\<^bsub>law_restrict A\<^esub> = \<one>\<^bsub>law_restrict B\<^esub>"
    using ring_iso_memE(4)[OF assms(1)] by simp
  ultimately show ?thesis by simp
qed

lemma iso_incl_backwards:
  assumes "A \<lesssim> B" shows "id \<in> ring_hom A B"
  using assms by cases

lemma iso_incl_antisym:
  assumes "A \<lesssim> B" and "B \<lesssim> A" shows "id \<in> ring_iso A B"
proof -
  have hom: "id \<in> ring_hom A B" "id \<in> ring_hom B A"
    using assms(1-2)[THEN iso_incl_backwards] by auto
  thus ?thesis
    using hom[THEN ring_hom_memE(1)] by (auto simp add: ring_iso_def bij_betw_def inj_on_def)
qed

lemma (in ring) iso_incl_antisym_on:
  assumes "A \<in> \<S>" "B \<in> \<S>" and "A \<lesssim> B" "B \<lesssim> A" shows "A = B"
proof -
  obtain A' B' :: "('a list multiset \<Rightarrow> 'a) ring"
    where A: "A = law_restrict A'" "ring A'" and B: "B = law_restrict B'" "ring B'"
    using assms(1-2) cring.axioms(1)[OF fieldE(1)] by (auto simp add: range_extensions_def)
  thus ?thesis
    using law_restrict_iso_imp_eq iso_incl_antisym[OF assms(3-4)] by simp
qed


subsection \<open>Extensions Non Empty\<close>

lemma (in ring) indexed_const_is_inj: "inj indexed_const"
  unfolding indexed_const_def by (rule inj_onI, metis)

(*
lemma (in field) extensions_non_empty: "\<S> \<noteq> {}"
  sorry
*)

subsection \<open>Partial Order\<close>

subsection \<open>Chains\<close>

(* Definition (and proof) of the partial order *)

(* Inductive set proof: field (\<Union>R \<in> Chain) + ... *)

end