theory Pred_Zorn
  imports Weak_Morphisms HOL.Zorn

begin

lemma Chains_alt_def':
  assumes "refl_on A { (a, b). P a b }"
  shows "Chains { (a, b) \<in> A \<times> A. P a b } = { C. pred_on.chain A P C }"
  using assms unfolding Chains_def pred_on.chain_def refl_on_def by force 

lemma Field_alt_def':
  assumes "refl_on A { (a, b). P a b }" shows "Field { (a, b) \<in> A \<times> A. P a b } = A"
  using assms unfolding refl_on_def Field_def by auto

lemma Partial_order_on:
  assumes "partial_order_on A { (a, b). P a b }"
  shows "Partial_order { (a, b) \<in> A \<times> A. P a b }"
proof -
  let ?r = "{ (a, b). P a b }" and ?r' = "{ (a, b) \<in> A \<times> A. P a b }"

  have "trans ?r" and "antisym ?r" and "refl_on A ?r"
    using assms unfolding partial_order_on_def preorder_on_def by auto
  hence "refl_on A ?r'"
    unfolding refl_on_def by auto
  moreover from transD[OF \<open>trans ?r\<close>] have "trans ?r'"
    by (auto intro!: transI)
  moreover from antisymD[OF \<open>antisym ?r\<close>] have "antisym ?r'"
    by (auto intro!: antisymI)
  ultimately show ?thesis
    unfolding Field_alt_def'[OF \<open>refl_on A ?r\<close>]
    by (simp add: partial_order_on_def preorder_on_def)
qed

lemma Zorns_pred_lemma:
  assumes "partial_order_on A { (a, b). P a b }"
    and "\<And>C. pred_on.chain A P C \<Longrightarrow> \<exists>u \<in> A. \<forall>a \<in> C. P a u"
  shows "\<exists>m \<in> A. \<forall>a \<in> A. P m a \<longrightarrow> a = m"
proof -
  have refl: "refl_on A { (a, b). P a b }"
    using assms unfolding partial_order_on_def preorder_on_def by simp
  have "\<And>c C. pred_on.chain A P C \<Longrightarrow> c \<in> C \<Longrightarrow> c \<in> A"
    unfolding pred_on.chain_def by auto
  thus ?thesis
    using Zorns_po_lemma[OF Partial_order_on[OF assms(1)]] assms(2)
    unfolding Field_alt_def'[OF refl] Chains_alt_def'[OF refl] by auto
qed


end