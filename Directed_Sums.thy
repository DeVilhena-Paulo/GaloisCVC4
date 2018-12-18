theory Directed_Sums
  imports Directed_Products

begin

section \<open>Directed Sums\<close>


subsection \<open>Definitions\<close>

definition sum_group :: "'a set \<Rightarrow> ('a \<Rightarrow> ('b, 'c) monoid_scheme) \<Rightarrow> ('a \<Rightarrow> 'b) monoid"
  where "sum_group I G \<equiv> product_group I G
           \<lparr> carrier := {x \<in> carrier (product_group I G). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}} \<rparr>"


subsection \<open>Algebraic Structure\<close>

lemma subgroup_of_finite_sequences:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "subgroup {x \<in> carrier (product_group I G). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}} (product_group I G)"
    (is "subgroup ?S ?H")
proof -
  interpret H: group "product_group I G"
    using product_group_is_group(1)[of I G, OF assms] .

  show ?thesis
  proof
    show "?S \<subseteq> carrier ?H" and "\<one>\<^bsub>?H\<^esub> \<in> ?S"
      using H.one_closed unfolding product_group_def by auto
  next
    fix x y
    assume x: "x \<in> ?S" and y: "y \<in> ?S"
    have "{i \<in> I. (x \<otimes>\<^bsub>?H\<^esub> y) i \<noteq> \<one>\<^bsub>G i\<^esub>} \<subseteq> {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>} \<union> {i \<in> I. y i \<noteq> \<one>\<^bsub>G i\<^esub>}"
      using monoid.l_one[OF _ monoid.one_closed] group.axioms(1)[OF assms]
      by (auto simp add: product_group_fields(2))
    hence "finite {i \<in> I. (x \<otimes>\<^bsub>?H\<^esub> y) i \<noteq> \<one>\<^bsub>G i\<^esub>}"
      using x y finite_subset[OF _ finite_UnI] by auto
    with \<open>x \<in> ?S\<close> and \<open>y \<in> ?S\<close> show "x \<otimes>\<^bsub>?H\<^esub> y \<in> ?S"
      using H.m_closed by simp
  next
    fix x assume x: "x \<in> ?S"
    then have in_carrier: "x \<in> carrier ?H"
      by simp
    have "{i \<in> I. (\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> (x i)) i \<noteq> \<one>\<^bsub>G i\<^esub>} \<subseteq> {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}"
      using monoid.inv_one[OF group.axioms(1)[OF assms]] by auto
    hence "finite {i \<in> I. (inv\<^bsub>?H\<^esub> x) i \<noteq> \<one>\<^bsub>G i\<^esub>}"
      using x product_group_is_group(2)[of I G x, OF assms in_carrier]
      by (simp add: finite_subset)
    with \<open>x \<in> ?S\<close> show "inv\<^bsub>?H\<^esub> x \<in> ?S"
      using H.inv_closed[of x] by simp
  qed
qed

lemma sum_group_is_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" shows "group (sum_group I G)"
  using group.subgroup_imp_group[OF product_group_is_group(1)   [of I G, OF assms]
                                    subgroup_of_finite_sequences[of I G, OF assms]]
  by (simp add: sum_group_def)

end