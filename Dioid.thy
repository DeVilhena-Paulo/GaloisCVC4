theory Dioid
  imports Multiplicative_Group Divisibility
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

lemma (in cancel_monoid) submonoid_is_cancel :
  assumes "submonoid H G"
  shows "cancel_monoid (G\<lparr>carrier := H\<rparr>)" 
proof (intro cancel_monoid.intro)
  show "monoid (G\<lparr>carrier := H\<rparr>)"
    using submonoid.submonoid_is_monoid[OF assms(1)] cancel_monoid_axioms cancel_monoid_def
    by blast
  show "cancel_monoid_axioms (G\<lparr>carrier := H\<rparr>)"
    unfolding cancel_monoid_axioms_def apply simp
    by (meson l_cancel r_cancel submonoid.mem_carrier assms)
qed


locale abelian_cancel_monoid =
  fixes D (structure)
  assumes a_comm_cancel_monoid:
     "comm_monoid_cancel (add_monoid D)"

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
proof ( intro abelian_cancel_monoid.intro[of D] comm_monoid_cancel.intro monoid_cancel.intro) 
  show comm :"Group.comm_monoid (add_monoid D)"
    by (auto intro!: abelian_monoid.intro comm_monoidI intro: assms)
  show "monoid (add_monoid D)" using comm_monoid.is_monoid[OF comm].
  show "monoid_cancel_axioms (add_monoid D) "
    unfolding monoid_cancel_axioms_def using cancel a_comm by auto
qed

lemma abelian_monoid_abelian_cancel_monoidI :
  assumes "abelian_monoid G"
    and cancel :
        "\<And> x y z. \<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> x \<oplus>\<^bsub>G\<^esub> y = x \<oplus>\<^bsub>G\<^esub> z \<Longrightarrow> y = z"
       shows "abelian_cancel_monoid G"
proof(intro abelian_cancel_monoid.intro[OF comm_monoid_cancelI])
  show "Group.comm_monoid (add_monoid G)"
    using assms unfolding abelian_monoid_def by blast
  show "\<And>a b c. a \<otimes>\<^bsub>add_monoid G\<^esub> c = b \<otimes>\<^bsub>add_monoid G\<^esub> c \<Longrightarrow> a \<in> carrier (add_monoid G) \<Longrightarrow>
          b \<in> carrier (add_monoid G) \<Longrightarrow> c \<in> carrier (add_monoid G) \<Longrightarrow> a = b"
    using cancel
    by (simp add: abelian_monoid.a_comm assms(1)) 
qed

lemma (in abelian_cancel_monoid) is_abelian_monoid :
"abelian_monoid D"
  using comm_monoid_cancel_def abelian_monoid_def[of D] a_comm_cancel_monoid
  by blast


subsection \<open>Canonically ordered monoids\<close>


definition
  canonic_order :: "('a, 'b) monoid_scheme => 'a => 'a \<Rightarrow> bool" (infixl "\<preceq>\<index>" 50)
where "canonic_order G x y  \<equiv> x = y \<or> (factor G x y \<and> (x \<in> carrier G) \<and> (y \<in> carrier G))"

definition
  canonic_strict_order :: "('a, 'b) monoid_scheme => 'a => 'a \<Rightarrow> bool" (infixl "\<prec>\<index>" 50)
where "canonic_strict_order G x y  = ((canonic_order G x y) \<and> \<not>(x = y))"

definition
  dioid_canonic_order :: "('a, 'b) ring_scheme => 'a => 'a \<Rightarrow> bool" (infixl "\<le>\<index>" 50)
  where "dioid_canonic_order R x y \<equiv> x = y \<or>
                                   (factor (add_monoid R) x y \<and> (x \<in> carrier R) \<and> (y \<in> carrier R))"

definition
  dioid_canonic_strict_order :: "('a, 'b) ring_scheme => 'a => 'a \<Rightarrow> bool" (infixl "<\<index>" 50)
where "dioid_canonic_strict_order R = (\<lambda> a b. a \<le>\<^bsub>R\<^esub> b \<and> a \<noteq> b)"

lemma same_order :
"dioid_canonic_order D = canonic_order (D\<lparr>mult := add D\<rparr>)"
  unfolding dioid_canonic_order_def canonic_order_def factor_def by auto

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

lemma same_canonical_order : 
"canonical_order (add_monoid D) = dioid_canonical_order D"
  unfolding dioid_canonic_order_def canonic_order_def
   by simp

locale canonical_order_monoid = comm_monoid +
  assumes canonically_ordered :
       "partial_order (canonical_order G)"

lemma (in canonical_order_monoid) positive_condition :
"\<lbrakk>a \<in> carrier G ; b \<in> carrier G ; a \<otimes> b = \<one> \<rbrakk> \<Longrightarrow> a = \<one> \<and> b = \<one> "
proof
  fix a b assume aG : "a \<in> carrier G" and bG : "b \<in> carrier G" and abone : "a \<otimes> b = \<one>"
  hence ainfone : "a \<preceq> \<one>" unfolding factor_def dioid_canonic_order_def canonic_order_def by force
  moreover have "\<one> \<otimes> a = a" using l_one aG by auto
  hence "\<one> \<preceq> a"
    unfolding factor_def dioid_canonic_order_def canonic_order_def using aG one_closed by auto
  ultimately show "a = \<one>" using partial_order.le_antisym[OF canonically_ordered,of a \<one>] aG by auto
  from aG bG abone have "b \<preceq> \<one>"
    unfolding factor_def dioid_canonic_order_def canonic_order_def using m_comm by force
  moreover have "\<one> \<otimes> b = b" using l_one bG by auto
  hence "\<one> \<preceq> b"
    unfolding dioid_canonic_order_def canonic_order_def factor_def using bG one_closed by auto
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
      unfolding factor_def dioid_canonic_order_def canonic_order_def
      using one_closed group.inv_closed grpG group.r_inv_ex  grpG x_def by force
    moreover have "\<one> \<preceq> x"
      unfolding factor_def dioid_canonic_order_def canonic_order_def
      using l_one x_def by force
    ultimately have "x = \<one> \<and> x \<noteq> \<one>"
      using canonically_ordered
      unfolding partial_order_def weak_partial_order_def weak_partial_order_axioms_def
                dioid_canonic_order_def canonic_order_def
      apply simp.
    thus False by auto
  qed
qed


lemma (in canonical_order_monoid) submonoid_is_canonical_order :
  assumes "submonoid H G"
  shows "canonical_order_monoid (G\<lparr>carrier := H\<rparr>)"
proof (intro canonical_order_monoid.intro)
  show "comm_monoid (G\<lparr>carrier := H\<rparr>)"    
    using comm_monoid.submonoid_is_comm_monoid canonical_order_monoid_axioms assms
          canonical_order_monoid_def 
    by auto
  have "weak_partial_order (canonical_order (G\<lparr>carrier := H\<rparr>))"
    unfolding factor_def weak_partial_order_def equivalence_def weak_partial_order_axioms_def
             canonic_order_def 
    apply simp apply auto
  proof-
    have "\<And>x c ca. c \<in> carrier G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> x \<otimes> c \<in> carrier G \<Longrightarrow> ca \<in> carrier G \<Longrightarrow>
          x = x \<otimes> c \<otimes> ca \<Longrightarrow> x = x \<otimes> c"
      using canonically_ordered
      unfolding partial_order_def factor_def weak_partial_order_def weak_partial_order_axioms_def
                dioid_canonic_order_def canonic_order_def
      apply simp by (metis (no_types, lifting) m_closed)
    thus "\<And>x c ca. c \<in> H \<Longrightarrow> x \<in> H \<Longrightarrow> x \<otimes> c \<in> H \<Longrightarrow> ca \<in> H \<Longrightarrow> x = x \<otimes> c \<otimes> ca \<Longrightarrow> x = x \<otimes> c"
      using submonoid.mem_carrier assms
      by smt
    show "\<And>x c ca. c \<in> H \<Longrightarrow> x \<in> H \<Longrightarrow> x \<otimes> c \<in> H \<Longrightarrow> x \<otimes> c \<otimes> ca \<in> H \<Longrightarrow> ca \<in> H \<Longrightarrow>
           \<forall>cb\<in>H. x \<otimes> c \<otimes> ca \<noteq> x \<otimes> cb \<Longrightarrow> x = x \<otimes> c \<otimes> ca"
      using canonical_order_monoid_axioms assms
      by (metis m_assoc submonoid.mem_carrier submonoid_def)
  qed
  moreover have "partial_order_axioms (canonical_order (G\<lparr>carrier := H\<rparr>))"
    unfolding partial_order_axioms_def by simp
  ultimately  show "canonical_order_monoid_axioms (G\<lparr>carrier := H\<rparr>)"
    unfolding canonical_order_monoid_axioms_def partial_order_def 
    by blast
qed

locale hemi_group = comm_monoid_cancel +
  assumes canonically_ordered :
       "partial_order (canonical_order G)"

lemma (in hemi_group) is_canonical_order_monoid :
"canonical_order_monoid G"
  unfolding  canonical_order_monoid_def
  by (simp add: canonical_order_monoid_axioms_def canonically_ordered comm_monoid_axioms)

lemma canonical_order_monoid_hemi_groupI :
  assumes "canonical_order_monoid G"
    and cancel :
        "\<And> x y z. \<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>G\<^esub> y = x \<otimes>\<^bsub>G\<^esub> z \<Longrightarrow> y = z"
  shows "hemi_group G"
  unfolding hemi_group_def hemi_group_axioms_def comm_monoid_cancel_def
  using canonical_order_monoid.canonically_ordered[OF assms(1)] comm_monoid_cancelI assms
  by (simp add: canonical_order_monoid_def Group.comm_monoid_def
      comm_monoid.m_comm monoid.monoid_cancelI)

locale abelian_hemi_group = abelian_cancel_monoid +
  assumes canonically_ordered :
       "partial_order (dioid_canonical_order D)"

lemma (in abelian_hemi_group) is_hemi_group :
"hemi_group (add_monoid D)"
  using abelian_cancel_monoid_axioms canonically_ordered
  unfolding hemi_group_def hemi_group_axioms_def abelian_cancel_monoid_def canonic_order_def
        dioid_canonic_order_def
  by auto

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
  using monoid_cancel.l_cancel abelian_cancel_monoid_def abelian_hemi_group_def
        comm_monoid_cancel_def
  apply (metis  dioid_def local.dioid_axioms monoid.simps(1) partial_object.select_convs(1))
  using abelian_hemi_group.canonically_ordered[OF abelian_hemi_group_axioms].


lemma (in dioid) mult_preserves_order :
  assumes "a \<in> carrier D" 
    and "b \<in> carrier D"
    and "c \<in> carrier D"
    and "a \<le>\<^bsub>D\<^esub> b"
  shows "(a \<otimes> c) \<le> (b \<otimes> c)"
proof -
  from assms obtain x where x_def : "x \<in> carrier D" " a \<oplus> x = b"
    unfolding factor_def dioid_canonic_order_def
    by (metis monoid.select_convs(1) partial_object.select_convs(1) r_zero zero_closed)
  hence "(b \<otimes> c) = ((a \<oplus> x) \<otimes> c)" by simp
  also have "... = (a \<otimes> c) \<oplus>  (x \<otimes> c)"
    by (simp add: assms(1) assms(3) l_distr x_def(1))
  finally have "(b \<otimes> c) = (a \<otimes> c) \<oplus>  (x \<otimes> c)" by simp
  thus "(a \<otimes> c) \<le> (b \<otimes> c)" 
    unfolding dioid_canonic_order_def
    using assms x_def(1) by auto
qed

lemma (in dioid) zero_is_idem :
"\<zero> \<otimes> \<zero> = \<zero>"
proof-
  have "\<zero> \<le> \<zero> \<otimes> \<zero>" unfolding   dioid_canonic_order_def by auto
  moreover have "\<zero> \<otimes> \<zero> \<le> \<zero> \<otimes> \<zero> \<otimes> \<zero>" unfolding dioid_canonic_order_def by auto
  moreover have "\<zero> \<otimes> \<zero> \<otimes> \<zero>  \<le> \<zero>"
  proof-
    have "\<one> = (\<one> \<oplus> \<zero>) \<otimes> (\<one> \<oplus> \<zero>)" by simp
    also have "... = (\<one> \<oplus> \<zero>) \<otimes> \<one> \<oplus> (\<one> \<oplus> \<zero>) \<otimes> \<zero>" using semiring.l_distr by auto
    finally have "\<one> = \<one> \<oplus> \<zero> \<otimes> \<zero>" by simp
    hence "\<zero> \<otimes> \<zero> \<le> \<one> " unfolding factor_def dioid_canonic_order_def by auto
    thus "\<zero> \<otimes> \<zero> \<otimes> \<zero>  \<le> \<zero>"
      using mult_preserves_order[where ?a = "\<zero> \<otimes> \<zero>" and ?b = "\<one>" and ?c = "\<zero>"] by auto
  qed
  ultimately show "\<zero> \<otimes> \<zero> = \<zero>"
    using canonically_ordered unfolding partial_order_def weak_partial_order_def
    by force
qed


locale subdioid =
  fixes H and D (structure)
  assumes sub_mult : "submonoid H D"
  and  sub_add : "submonoid H (add_monoid D)"
              
lemma (in dioid) subdioid_is_dioid :
  assumes "subdioid H D"
  shows "dioid (D\<lparr>carrier := H\<rparr>)"
proof(intro dioid.intro semiring.intro abelian_hemi_group.intro)
  show H1 : "abelian_monoid (D\<lparr>carrier := H\<rparr>)" unfolding abelian_monoid_def
    using comm_monoid.submonoid_is_comm_monoid[OF abelian_monoid.a_comm_monoid[OF
           abelian_monoid_axioms] subdioid.sub_add[OF assms]] by auto
  show "abelian_cancel_monoid (D\<lparr>carrier := H\<rparr>)"
    using subdioid.sub_add[OF assms] abelian_cancel_monoid_axioms
         comm_monoid_cancel.submonoid_is_comm_cancel[where ?G =  "add_monoid D"]
    unfolding abelian_cancel_monoid_def by auto
  show "monoid (D\<lparr>carrier := H\<rparr>)"
    using submonoid.submonoid_is_monoid subdioid.sub_mult assms monoid_axioms
    by auto
  show "semiring_axioms (D\<lparr>carrier := H\<rparr>)"
    unfolding semiring_axioms_def apply simp
    using semiring_axioms assms submonoid.mem_carrier submonoid_imp_subset
    by (smt l_distr l_null r_distr r_null subdioid_def)
  have "partial_order (canonical_order (add_monoid D\<lparr>carrier := H\<rparr>))"
    using canonical_order_monoid.submonoid_is_canonical_order add.comm_monoid_axioms assms
          same_canonical_order[of D] subdioid.sub_add[OF assms]  canonically_ordered
          hemi_group.is_canonical_order_monoid hemi_group.is_canonical_order_monoid
          canonical_order_monoid.canonically_ordered is_hemi_group
    by blast
  thus "abelian_hemi_group_axioms (D\<lparr>carrier := H\<rparr>)" unfolding abelian_hemi_group_axioms_def
    using same_canonical_order [where ?D = "D\<lparr>carrier := H\<rparr>"] by simp
qed

definition R :: "real ring"
  where "R =(\<lparr>carrier = {r :: real . r \<ge> 0}, monoid.mult = op *, one = 1, zero = 0, add = op +\<rparr>)"


lemma real_is_dioid :
"dioid (R)" unfolding R_def
   apply unfold_locales 
   unfolding factor_def canonic_order_def dioid_canonic_order_def
   apply (simp_all add : distrib_right distrib_left)
   apply linarith
   by auto



end