theory Dioid
  imports Multiplicative_Group
begin

locale cancel_monoid = monoid +
  assumes l_cancel [simp]:
        "\<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow>x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z "
      and r_cancel [simp]:
        "\<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow>y \<otimes> x = z \<otimes> x \<Longrightarrow> y = z "


lemma cancel_monoidI :
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and r_one: "!!x. x \<in> carrier G ==> x \<otimes> \<one> = x"
    and l_cancel:
        "\<And> x y z. \<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow>x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z "
    and r_cancel:
        "\<And> x y z. \<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow>y \<otimes> x = z \<otimes> x \<Longrightarrow> y = z "
  shows "cancel_monoid G"
  using cancel_monoid.intro[OF monoidI] assms unfolding cancel_monoid_axioms_def
  by blast

locale comm_cancel_monoid = comm_monoid + 
  assumes cancel [simp]:
        "\<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z"

lemma (in comm_cancel_monoid) is_cancel : "cancel_monoid G"
  unfolding comm_cancel_monoid_def cancel_monoid_def cancel_monoid_axioms_def
  using comm_cancel_monoid.axioms(1) comm_cancel_monoid.cancel comm_monoid.is_monoid 
        cancel m_comm monoid_axioms by presburger

lemma comm_cancel_monoidI :
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
    and cancel :
         "\<And> x y z. \<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z"
  shows "comm_cancel_monoid G"
  unfolding comm_cancel_monoid_def
  using cancel comm_cancel_monoid_axioms.intro comm_monoidI l_one m_assoc m_closed m_comm one_closed
  by blast

lemma (in monoid) monoid_comm_cancel_monoidI :
  assumes m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
    and cancel :
         "\<And> x y z. \<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z"
       shows  "comm_cancel_monoid G"
  unfolding comm_cancel_monoid_def  comm_cancel_monoid_axioms_def
  using monoid_comm_monoidI assms by blast

lemma (in comm_monoid) comm_monoid_comm_cancel_monoidI :
  assumes cancel :
         "\<And> x y z. \<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z"
       shows "comm_cancel_monoid G"
  unfolding comm_cancel_monoid_def comm_cancel_monoid_axioms_def
  using assms comm_monoid_axioms by blast

lemma (in cancel_monoid) cancel_monoid_comm_cancel_monoidI :
  assumes m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
    shows  "comm_cancel_monoid G"
  using monoid_comm_cancel_monoidI cancel_monoid.axioms l_cancel m_comm
  by blast


locale abelian_cancel_monoid =
  fixes D (structure)
  assumes a_comm_cancel_monoid:
     "comm_cancel_monoid \<lparr>carrier = carrier D, mult = add D, one = zero D\<rparr>"


lemma abelian_cancel_monoidI:
  fixes D (structure)
  assumes a_closed:
      "!!x y. [| x \<in> carrier D; y \<in> carrier D |] ==> x \<oplus> y \<in> carrier D"
    and zero_closed: "\<zero> \<in> carrier D"
    and a_assoc:
      "!!x y z. [| x \<in> carrier D; y \<in> carrier D; z \<in> carrier D |] ==>
      (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
    and l_zero: "!!x. x \<in> carrier D ==> \<zero> \<oplus> x = x"
    and a_comm:
      "!!x y. [| x \<in> carrier D; y \<in> carrier D |] ==> x \<oplus> y = y \<oplus> x"
    and cancel :
         "\<And> x y z. \<lbrakk>x \<in> carrier D; y \<in> carrier D; z \<in> carrier D \<rbrakk> \<Longrightarrow> x \<oplus> y = x \<oplus> z \<Longrightarrow> y = z"
  shows "abelian_cancel_monoid D"
proof ( intro abelian_cancel_monoid.intro[of D] comm_cancel_monoid.intro ) 
  show "Group.comm_monoid \<lparr>carrier = carrier D, mult = op \<oplus>, one = \<zero>\<rparr>"
    by (auto intro!: abelian_monoid.intro comm_monoidI intro: assms)
  show "comm_cancel_monoid_axioms \<lparr>carrier = carrier D, mult = op \<oplus>, one = \<zero>\<rparr> "
    unfolding comm_cancel_monoid_axioms_def using cancel by auto
qed


lemma (in abelian_monoid) abelian_monoid_abelian_cancel_monoidI :
  assumes cancel :
         "\<And> x y z. \<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> x \<oplus> y = x \<oplus> z \<Longrightarrow> y = z"
       shows "abelian_cancel_monoid G"
proof(intro abelian_cancel_monoid.intro[OF comm_monoid.comm_monoid_comm_cancel_monoidI])
  show "Group.comm_monoid \<lparr>carrier = carrier G, mult = op \<oplus>\<^bsub>G\<^esub>, one = \<zero>\<^bsub>G\<^esub>\<rparr>"
    using abelian_monoid_axioms unfolding abelian_monoid_def.
  show "\<And>x y z. x \<in> carrier \<lparr>carrier = carrier G, mult = op \<oplus>, one = \<zero>\<rparr> \<Longrightarrow>
        y \<in> carrier \<lparr>carrier = carrier G, mult = op \<oplus>, one = \<zero>\<rparr> \<Longrightarrow>
        z \<in> carrier \<lparr>carrier = carrier G, mult = op \<oplus>, one = \<zero>\<rparr> \<Longrightarrow>
        x \<otimes>\<^bsub>\<lparr>carrier = carrier G, mult = op \<oplus>, one = \<zero>\<rparr>\<^esub> y =
        x \<otimes>\<^bsub>\<lparr>carrier = carrier G, mult = op \<oplus>, one = \<zero>\<rparr>\<^esub> z \<Longrightarrow> y = z"
    apply simp using cancel by blast
qed

lemma (in abelian_cancel_monoid) is_abelian_monoid :
"abelian_monoid D"
  using comm_cancel_monoid_def abelian_monoid_def[of D] a_comm_cancel_monoid
  by blast


subsection \<open>Canonically ordered monoids\<close>

definition
  canonic_order :: "('a, 'b) monoid_scheme => 'a => 'a \<Rightarrow> bool" (infixl "\<preceq>\<index>" 50)
  where "canonic_order G x y  = (\<exists> z. z \<in> carrier G \<and> x \<otimes>\<^bsub>G\<^esub> z = y)"

definition
  dioid_canonic_order :: "('a, 'b) ring_scheme => 'a => 'a \<Rightarrow> bool" (infixl "\<le>\<index>" 50)
  where "dioid_canonic_order R x y  = (\<exists> z. z \<in> carrier R \<and> x \<oplus>\<^bsub>R\<^esub> z = y)"

lemma same_order :
"dioid_canonic_order D = canonic_order (D\<lparr>mult := add D\<rparr>)"
  unfolding dioid_canonic_order_def canonic_order_def by auto

abbreviation canonical_order ::  "_ \<Rightarrow> 'a gorder" where
  "canonical_order D \<equiv>
   \<lparr> carrier = carrier D,
     eq = op =,
     le = canonic_order D \<rparr>"

abbreviation dioid_canonical_order ::  "_ \<Rightarrow> 'a gorder" where
  "dioid_canonical_order D \<equiv>
   \<lparr> carrier = carrier D,
     eq = op =,
     le = dioid_canonic_order D \<rparr>"

locale canonical_order_monoid = comm_monoid +
  assumes canonically_ordered :
       "partial_order (canonical_order G)"

lemma (in canonical_order_monoid) positive_condition :
"\<lbrakk>a \<in> carrier G ; b \<in> carrier G ; a \<otimes> b = \<one> \<rbrakk> \<Longrightarrow> a = \<one> \<and> b = \<one> "
proof
  fix a b assume aG : "a \<in> carrier G" and bG : "b \<in> carrier G" and abone : "a \<otimes> b = \<one>"
  hence ainfone : "a \<preceq> \<one>" unfolding canonic_order_def by auto
  moreover have "\<one> \<otimes> a = a" using l_one aG by auto
  hence "\<one> \<preceq> a" unfolding canonic_order_def using aG by blast
  ultimately show "a = \<one>" using partial_order.le_antisym[OF canonically_ordered,of a \<one>] aG by auto
  from aG bG abone have "b \<preceq> \<one>" unfolding canonic_order_def using m_comm by fastforce
  moreover have "\<one> \<otimes> b = b" using l_one bG by auto
  hence "\<one> \<preceq> b" unfolding canonic_order_def using bG by blast
  ultimately show "b = \<one>" using partial_order.le_antisym[OF canonically_ordered,of b \<one>] bG by auto
qed

proposition (in canonical_order_monoid) not_a_group :
"group G \<Longrightarrow> carrier G = {\<one>}"
proof
  assume grpG : "Group.group G"
  show "{\<one>} \<subseteq> carrier G" using one_closed by auto
  show "Group.group G \<Longrightarrow> carrier G \<subseteq> {\<one>}"
  proof (rule ccontr)
    assume "\<not> carrier G \<subseteq> {\<one>}"
    hence existx : "\<exists> x. x \<in> carrier G \<and> x \<notin> {\<one>}" by blast
    obtain x where x_def : "x \<in> carrier G \<and> x \<notin> {\<one>}" using existx by blast
    hence "x \<noteq> \<one>" by blast
    moreover have "x \<preceq> \<one>"
      unfolding canonic_order_def by (meson group.r_inv_ex grpG x_def)
    moreover have "\<one> \<preceq> x"
      unfolding canonic_order_def using l_one x_def by blast
    ultimately have "x = \<one> \<and> x \<noteq> \<one>"
      using canonically_ordered
      unfolding partial_order_def weak_partial_order_def weak_partial_order_axioms_def
      by (metis (full_types) eq_object.select_convs(1) gorder.select_convs(1)
          one_closed partial_object.select_convs(1) x_def)
    thus False by auto
  qed
qed

locale hemi_group = comm_cancel_monoid +
  assumes canonically_ordered :
       "partial_order (canonical_order G)"

lemma (in hemi_group) is_canonical_order_monoid :
"canonical_order_monoid G"
  unfolding  canonical_order_monoid_def
  by (simp add: canonical_order_monoid_axioms_def canonically_ordered comm_monoid_axioms)

locale abelian_hemi_group = abelian_cancel_monoid +
  assumes canonically_ordered :
       "partial_order (dioid_canonical_order D)"

subsection "Dioids"

locale dioid = semiring D + abelian_hemi_group D for D(structure)

lemma (in dioid) dioidE :
  shows zero_closed: "\<zero> \<in> carrier D"
    and one_closed : "\<one> \<in> carrier D"
    and l_zero : "\<And>x. x \<in> carrier D \<Longrightarrow> \<zero> \<oplus> x = x"
    and r_zero : "\<And>x. x \<in> carrier D \<Longrightarrow> x \<oplus> \<zero> = x"
    and l_one : "\<And>x. x \<in> carrier D \<Longrightarrow> \<one> \<otimes> x = x"
    and r_one : "\<And>x. x \<in> carrier D \<Longrightarrow> x \<otimes> \<one> = x"
    and l_null: "\<And>x. x \<in> carrier D ==> \<zero> \<otimes> x = \<zero>"
    and r_null: "\<And>x. x \<in> carrier D ==> x \<otimes> \<zero> = \<zero>"
    and a_closed:
         "\<And>x y. \<lbrakk>x \<in> carrier D; y \<in> carrier D\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrier D"
    and m_closed :
         "\<And>x y. \<lbrakk>x \<in> carrier D; y \<in> carrier D\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier D"
    and a_assoc:
         "\<And>x y z. \<lbrakk>x \<in> carrier D; y \<in> carrier D; z \<in> carrier D\<rbrakk> 
          \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
    and m_assoc:
         "\<And>x y z. \<lbrakk>x \<in> carrier D; y \<in> carrier D; z \<in> carrier D\<rbrakk> 
          \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_distr: "\<And>x y z. [| x \<in> carrier D; y \<in> carrier D; z \<in> carrier D |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
    and r_distr: "\<And>x y z. [| x \<in> carrier D; y \<in> carrier D; z \<in> carrier D |]
      ==> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"
    and a_comm: "\<And>x y. \<lbrakk>x \<in> carrier D; y \<in> carrier D\<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
    and cancel: "\<And>x y z. \<lbrakk>x \<in> carrier D; y \<in> carrier D; z \<in> carrier D \<rbrakk> \<Longrightarrow> x \<oplus> y = x \<oplus> z \<Longrightarrow>y = z"
    and canonically_ordered: "partial_order (dioid_canonical_order D)"
  apply (simp_all add: add.m_assoc m_assoc l_distr r_distr add.m_comm add.m_lcomm)
  using comm_cancel_monoid.cancel[OF a_comm_cancel_monoid]
  apply (metis monoid.simps(1) partial_object.select_convs(1))
  using abelian_hemi_group.canonically_ordered[OF abelian_hemi_group_axioms].

                







lemma (in dioid) mult_preserves_order :
  assumes "a \<in> carrier D" 
    and "b \<in> carrier D"
    and "c \<in> carrier D"
    and "a \<le>\<^bsub>D\<^esub> b"
  shows "(a \<otimes> c) \<le> (b \<otimes> c)"
proof -
  from assms obtain x where x_def : "x \<in> carrier D" " a \<oplus> x = b"
    unfolding dioid_canonic_order_def by blast
  hence "(b \<otimes> c) = ((a \<oplus> x) \<otimes> c)" by simp
  also have "... = (a \<otimes> c) \<oplus>  (x \<otimes> c)"
    by (simp add: assms(1) assms(3) l_distr x_def(1))
  finally have "(b \<otimes> c) = (a \<otimes> c) \<oplus>  (x \<otimes> c)" by simp
  thus "(a \<otimes> c) \<le> (b \<otimes> c)" unfolding dioid_canonic_order_def
    using assms(3) x_def(1) by auto
qed

lemma (in dioid) zero_is_idem :
"\<zero> \<otimes> \<zero> = \<zero>"
proof-
  have "\<zero> \<le> \<zero> \<otimes> \<zero>"
    unfolding dioid_canonic_order_def by auto
  moreover have "\<zero> \<otimes> \<zero> \<le> \<zero> \<otimes> \<zero> \<otimes> \<zero>"
    unfolding dioid_canonic_order_def by auto
  moreover have "\<zero> \<otimes> \<zero> \<otimes> \<zero>  \<le> \<zero>"
  proof-
    have "\<one> = (\<one> \<oplus> \<zero>) \<otimes> (\<one> \<oplus> \<zero>)" by simp
    also have "... = (\<one> \<oplus> \<zero>) \<otimes> \<one> \<oplus> (\<one> \<oplus> \<zero>) \<otimes> \<zero>" using semiring.l_distr by auto
    finally have "\<one> = \<one> \<oplus> \<zero> \<otimes> \<zero>" by simp
    hence "\<zero> \<otimes> \<zero> \<le> \<one> " unfolding dioid_canonic_order_def by auto
    thus "\<zero> \<otimes> \<zero> \<otimes> \<zero>  \<le> \<zero>"
      using mult_preserves_order[where ?a = "\<zero> \<otimes> \<zero>" and ?b = "\<one>" and ?c = "\<zero>"] by auto
  qed
  ultimately show "\<zero> \<otimes> \<zero> = \<zero>"
    using canonically_ordered unfolding partial_order_def weak_partial_order_def
    by force
qed