(*  Title:      HOL/Algebra/Group.thy
    Author:     Clemens Ballarin, started 4 February 2003

Based on work by Florian Kammueller, L C Paulson and Markus Wenzel.
*)

theory Group
imports Complete_Lattice "HOL-Library.FuncSet"
begin

section \<open>Monoids and Groups\<close>

subsection \<open>Definitions\<close>

text \<open>
  Definitions follow @{cite "Jacobson:1985"}.
\<close>

record 'a monoid =  "'a partial_object" +
  mult    :: "['a, 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
  one     :: 'a ("\<one>\<index>")

definition
  m_inv :: "('a, 'b) monoid_scheme => 'a => 'a" ("inv\<index> _" [81] 80)
  where "inv\<^bsub>G\<^esub> x = (THE y. y \<in> carrier G & x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> & y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)"

definition
  Units :: "_ => 'a set"
  \<comment>\<open>The set of invertible elements\<close>
  where "Units G = {y. y \<in> carrier G & (\<exists>x \<in> carrier G. x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> & y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)}"

consts
  pow :: "[('a, 'm) monoid_scheme, 'a, 'b::semiring_1] => 'a"  (infixr "'(^')\<index>" 75)

overloading nat_pow == "pow :: [_, 'a, nat] => 'a"
begin
  definition "nat_pow G a n = rec_nat \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a) n"
end

overloading int_pow == "pow :: [_, 'a, int] => 'a"
begin
  definition "int_pow G a z =
   (let p = rec_nat \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a)
    in if z < 0 then inv\<^bsub>G\<^esub> (p (nat (-z))) else p (nat z))"
end

lemma int_pow_int: "x (^)\<^bsub>G\<^esub> (int n) = x (^)\<^bsub>G\<^esub> n"
by(simp add: int_pow_def nat_pow_def)

locale monoid =
  fixes G (structure)
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
      and m_assoc:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk> 
          \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
      and one_closed [intro, simp]: "\<one> \<in> carrier G"
      and l_one [simp]: "x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
      and r_one [simp]: "x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x"

lemma monoidI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and r_one: "!!x. x \<in> carrier G ==> x \<otimes> \<one> = x"
  shows "monoid G"
  by (fast intro!: monoid.intro intro: assms)

lemma (in monoid) Units_closed [dest]:
  "x \<in> Units G ==> x \<in> carrier G"
  by (unfold Units_def) fast

lemma (in monoid) inv_unique:
  assumes eq: "y \<otimes> x = \<one>"  "x \<otimes> y' = \<one>"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "y' \<in> carrier G"
  shows "y = y'"
proof -
  from G eq have "y = y \<otimes> (x \<otimes> y')" by simp
  also from G have "... = (y \<otimes> x) \<otimes> y'" by (simp add: m_assoc)
  also from G eq have "... = y'" by simp
  finally show ?thesis .
qed

lemma (in monoid) Units_m_closed [intro, simp]:
  assumes x: "x \<in> Units G" and y: "y \<in> Units G"
  shows "x \<otimes> y \<in> Units G"
proof -
  from x obtain x' where x: "x \<in> carrier G" "x' \<in> carrier G" and xinv: "x \<otimes> x' = \<one>" "x' \<otimes> x = \<one>"
    unfolding Units_def by fast
  from y obtain y' where y: "y \<in> carrier G" "y' \<in> carrier G" and yinv: "y \<otimes> y' = \<one>" "y' \<otimes> y = \<one>"
    unfolding Units_def by fast
  from x y xinv yinv have "y' \<otimes> (x' \<otimes> x) \<otimes> y = \<one>" by simp
  moreover from x y xinv yinv have "x \<otimes> (y \<otimes> y') \<otimes> x' = \<one>" by simp
  moreover note x y
  ultimately show ?thesis unfolding Units_def
    \<comment> "Must avoid premature use of \<open>hyp_subst_tac\<close>."
    apply (rule_tac CollectI)
    apply (rule)
    apply (fast)
    apply (rule bexI [where x = "y' \<otimes> x'"])
    apply (auto simp: m_assoc)
    done
qed

lemma (in monoid) Units_one_closed [intro, simp]:
  "\<one> \<in> Units G"
  by (unfold Units_def) auto

lemma (in monoid) Units_inv_closed [intro, simp]:
  "x \<in> Units G ==> inv x \<in> carrier G"
  apply (unfold Units_def m_inv_def, auto)
  apply (rule theI2, fast)
   apply (fast intro: inv_unique, fast)
  done

lemma (in monoid) Units_l_inv_ex:
  "x \<in> Units G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  by (unfold Units_def) auto

lemma (in monoid) Units_r_inv_ex:
  "x \<in> Units G ==> \<exists>y \<in> carrier G. x \<otimes> y = \<one>"
  by (unfold Units_def) auto

lemma (in monoid) Units_l_inv [simp]:
  "x \<in> Units G ==> inv x \<otimes> x = \<one>"
  apply (unfold Units_def m_inv_def, auto)
  apply (rule theI2, fast)
   apply (fast intro: inv_unique, fast)
  done

lemma (in monoid) Units_r_inv [simp]:
  "x \<in> Units G ==> x \<otimes> inv x = \<one>"
  apply (unfold Units_def m_inv_def, auto)
  apply (rule theI2, fast)
   apply (fast intro: inv_unique, fast)
  done

lemma (in monoid) Units_inv_Units [intro, simp]:
  "x \<in> Units G ==> inv x \<in> Units G"
proof -
  assume x: "x \<in> Units G"
  show "inv x \<in> Units G"
    by (auto simp add: Units_def
      intro: Units_l_inv Units_r_inv x Units_closed [OF x])
qed

lemma (in monoid) Units_l_cancel [simp]:
  "[| x \<in> Units G; y \<in> carrier G; z \<in> carrier G |] ==>
   (x \<otimes> y = x \<otimes> z) = (y = z)"
proof
  assume eq: "x \<otimes> y = x \<otimes> z"
    and G: "x \<in> Units G"  "y \<in> carrier G"  "z \<in> carrier G"
  then have "(inv x \<otimes> x) \<otimes> y = (inv x \<otimes> x) \<otimes> z"
    by (simp add: m_assoc Units_closed del: Units_l_inv)
  with G show "y = z" by simp
next
  assume eq: "y = z"
    and G: "x \<in> Units G"  "y \<in> carrier G"  "z \<in> carrier G"
  then show "x \<otimes> y = x \<otimes> z" by simp
qed

lemma (in monoid) Units_inv_inv [simp]:
  "x \<in> Units G ==> inv (inv x) = x"
proof -
  assume x: "x \<in> Units G"
  then have "inv x \<otimes> inv (inv x) = inv x \<otimes> x" by simp
  with x show ?thesis by (simp add: Units_closed del: Units_l_inv Units_r_inv)
qed

lemma (in monoid) inv_inj_on_Units:
  "inj_on (m_inv G) (Units G)"
proof (rule inj_onI)
  fix x y
  assume G: "x \<in> Units G"  "y \<in> Units G" and eq: "inv x = inv y"
  then have "inv (inv x) = inv (inv y)" by simp
  with G show "x = y" by simp
qed

lemma (in monoid) Units_inv_comm:
  assumes inv: "x \<otimes> y = \<one>"
    and G: "x \<in> Units G"  "y \<in> Units G"
  shows "y \<otimes> x = \<one>"
proof -
  from G have "x \<otimes> y \<otimes> x = x \<otimes> \<one>" by (auto simp add: inv Units_closed)
  with G show ?thesis by (simp del: r_one add: m_assoc Units_closed)
qed

lemma (in monoid) carrier_not_empty: "carrier G \<noteq> {}"
by auto

text \<open>Power\<close>

lemma (in monoid) nat_pow_closed [intro, simp]:
  "x \<in> carrier G ==> x (^) (n::nat) \<in> carrier G"
  by (induct n) (simp_all add: nat_pow_def)

lemma (in monoid) nat_pow_0 [simp]:
  "x (^) (0::nat) = \<one>"
  by (simp add: nat_pow_def)

lemma (in monoid) nat_pow_Suc [simp]:
  "x (^) (Suc n) = x (^) n \<otimes> x"
  by (simp add: nat_pow_def)

lemma (in monoid) nat_pow_one [simp]:
  "\<one> (^) (n::nat) = \<one>"
  by (induct n) simp_all

lemma (in monoid) nat_pow_mult:
  "x \<in> carrier G ==> x (^) (n::nat) \<otimes> x (^) m = x (^) (n + m)"
  by (induct m) (simp_all add: m_assoc [THEN sym])

lemma (in monoid) nat_pow_pow:
  "x \<in> carrier G ==> (x (^) n) (^) m = x (^) (n * m::nat)"
  by (induct m) (simp, simp add: nat_pow_mult add.commute)


(* Jacobson defines submonoid here. *)
(* Jacobson defines the order of a monoid here. *)


subsection \<open>Groups\<close>

text \<open>
  A group is a monoid all of whose elements are invertible.
\<close>

locale group = monoid +
  assumes Units: "carrier G <= Units G"

lemma (in group) is_group: "group G" by (rule group_axioms)

theorem groupI:
  fixes G (structure)
  assumes m_closed [simp]:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed [simp]: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one [simp]: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "group G"
proof -
  have l_cancel [simp]:
    "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
    (x \<otimes> y = x \<otimes> z) = (y = z)"
  proof
    fix x y z
    assume eq: "x \<otimes> y = x \<otimes> z"
      and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
    with l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier G"
      and l_inv: "x_inv \<otimes> x = \<one>" by fast
    from G eq xG have "(x_inv \<otimes> x) \<otimes> y = (x_inv \<otimes> x) \<otimes> z"
      by (simp add: m_assoc)
    with G show "y = z" by (simp add: l_inv)
  next
    fix x y z
    assume eq: "y = z"
      and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
    then show "x \<otimes> y = x \<otimes> z" by simp
  qed
  have r_one:
    "!!x. x \<in> carrier G ==> x \<otimes> \<one> = x"
  proof -
    fix x
    assume x: "x \<in> carrier G"
    with l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier G"
      and l_inv: "x_inv \<otimes> x = \<one>" by fast
    from x xG have "x_inv \<otimes> (x \<otimes> \<one>) = x_inv \<otimes> x"
      by (simp add: m_assoc [symmetric] l_inv)
    with x xG show "x \<otimes> \<one> = x" by simp
  qed
  have inv_ex:
    "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one> & x \<otimes> y = \<one>"
  proof -
    fix x
    assume x: "x \<in> carrier G"
    with l_inv_ex obtain y where y: "y \<in> carrier G"
      and l_inv: "y \<otimes> x = \<one>" by fast
    from x y have "y \<otimes> (x \<otimes> y) = y \<otimes> \<one>"
      by (simp add: m_assoc [symmetric] l_inv r_one)
    with x y have r_inv: "x \<otimes> y = \<one>"
      by simp
    from x y show "\<exists>y \<in> carrier G. y \<otimes> x = \<one> & x \<otimes> y = \<one>"
      by (fast intro: l_inv r_inv)
  qed
  then have carrier_subset_Units: "carrier G <= Units G"
    by (unfold Units_def) fast
  show ?thesis
    by standard (auto simp: r_one m_assoc carrier_subset_Units)
qed

lemma (in monoid) group_l_invI:
  assumes l_inv_ex:
    "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "group G"
  by (rule groupI) (auto intro: m_assoc l_inv_ex)

lemma (in group) Units_eq [simp]:
  "Units G = carrier G"
proof
  show "Units G <= carrier G" by fast
next
  show "carrier G <= Units G" by (rule Units)
qed

lemma (in group) inv_closed [intro, simp]:
  "x \<in> carrier G ==> inv x \<in> carrier G"
  using Units_inv_closed by simp

lemma (in group) l_inv_ex [simp]:
  "x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  using Units_l_inv_ex by simp

lemma (in group) r_inv_ex [simp]:
  "x \<in> carrier G ==> \<exists>y \<in> carrier G. x \<otimes> y = \<one>"
  using Units_r_inv_ex by simp

lemma (in group) l_inv [simp]:
  "x \<in> carrier G ==> inv x \<otimes> x = \<one>"
  using Units_l_inv by simp


subsection \<open>Cancellation Laws and Basic Properties\<close>

lemma (in group) l_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (x \<otimes> y = x \<otimes> z) = (y = z)"
  using Units_l_inv by simp

lemma (in group) r_inv [simp]:
  "x \<in> carrier G ==> x \<otimes> inv x = \<one>"
proof -
  assume x: "x \<in> carrier G"
  then have "inv x \<otimes> (x \<otimes> inv x) = inv x \<otimes> \<one>"
    by (simp add: m_assoc [symmetric])
  with x show ?thesis by (simp del: r_one)
qed

lemma (in group) r_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (y \<otimes> x = z \<otimes> x) = (y = z)"
proof
  assume eq: "y \<otimes> x = z \<otimes> x"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  then have "y \<otimes> (x \<otimes> inv x) = z \<otimes> (x \<otimes> inv x)"
    by (simp add: m_assoc [symmetric] del: r_inv Units_r_inv)
  with G show "y = z" by simp
next
  assume eq: "y = z"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  then show "y \<otimes> x = z \<otimes> x" by simp
qed

lemma (in group) inv_one [simp]:
  "inv \<one> = \<one>"
proof -
  have "inv \<one> = \<one> \<otimes> (inv \<one>)" by (simp del: r_inv Units_r_inv)
  moreover have "... = \<one>" by simp
  finally show ?thesis .
qed

lemma (in group) inv_inv [simp]:
  "x \<in> carrier G ==> inv (inv x) = x"
  using Units_inv_inv by simp

lemma (in group) inv_inj:
  "inj_on (m_inv G) (carrier G)"
  using inv_inj_on_Units by simp

lemma (in group) inv_mult_group:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv y \<otimes> inv x"
proof -
  assume G: "x \<in> carrier G"  "y \<in> carrier G"
  then have "inv (x \<otimes> y) \<otimes> (x \<otimes> y) = (inv y \<otimes> inv x) \<otimes> (x \<otimes> y)"
    by (simp add: m_assoc) (simp add: m_assoc [symmetric])
  with G show ?thesis by (simp del: l_inv Units_l_inv)
qed

lemma (in group) inv_comm:
  "[| x \<otimes> y = \<one>; x \<in> carrier G; y \<in> carrier G |] ==> y \<otimes> x = \<one>"
  by (rule Units_inv_comm) auto

lemma (in group) inv_equality:
     "[|y \<otimes> x = \<one>; x \<in> carrier G; y \<in> carrier G|] ==> inv x = y"
apply (simp add: m_inv_def)
apply (rule the_equality)
 apply (simp add: inv_comm [of y x])
apply (rule r_cancel [THEN iffD1], auto)
done

(* Contributed by Joachim Breitner *)
lemma (in group) inv_solve_left:
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> a = inv b \<otimes> c \<longleftrightarrow> c = b \<otimes> a"
  by (metis inv_equality l_inv_ex l_one m_assoc r_inv)
lemma (in group) inv_solve_right:
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> a = b \<otimes> inv c \<longleftrightarrow> b = a \<otimes> c"
  by (metis inv_equality l_inv_ex l_one m_assoc r_inv)

text \<open>Power\<close>

lemma (in group) int_pow_def2:
  "a (^) (z::int) = (if z < 0 then inv (a (^) (nat (-z))) else a (^) (nat z))"
  by (simp add: int_pow_def nat_pow_def Let_def)

lemma (in group) int_pow_0 [simp]:
  "x (^) (0::int) = \<one>"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_one [simp]:
  "\<one> (^) (z::int) = \<one>"
  by (simp add: int_pow_def2)

(* The following are contributed by Joachim Breitner *)

lemma (in group) int_pow_closed [intro, simp]:
  "x \<in> carrier G ==> x (^) (i::int) \<in> carrier G"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_1 [simp]:
  "x \<in> carrier G \<Longrightarrow> x (^) (1::int) = x"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_neg:
  "x \<in> carrier G \<Longrightarrow> x (^) (-i::int) = inv (x (^) i)"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_mult:
  "x \<in> carrier G \<Longrightarrow> x (^) (i + j::int) = x (^) i \<otimes> x (^) j"
proof -
  have [simp]: "-i - j = -j - i" by simp
  assume "x : carrier G" then
  show ?thesis
    by (auto simp add: int_pow_def2 inv_solve_left inv_solve_right nat_add_distrib [symmetric] nat_pow_mult )
qed

lemma (in group) int_pow_diff:
  "x \<in> carrier G \<Longrightarrow> x (^) (n - m :: int) = x (^) n \<otimes> inv (x (^) m)"
by(simp only: diff_conv_add_uminus int_pow_mult int_pow_neg)

lemma (in group) inj_on_multc: "c \<in> carrier G \<Longrightarrow> inj_on (\<lambda>x. x \<otimes> c) (carrier G)"
by(simp add: inj_on_def)

lemma (in group) inj_on_cmult: "c \<in> carrier G \<Longrightarrow> inj_on (\<lambda>x. c \<otimes> x) (carrier G)"
by(simp add: inj_on_def)

subsection \<open>Subgroups\<close>

locale subgroup =
  fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
    and one_closed [simp]: "\<one> \<in> H"
    and m_inv_closed [intro,simp]: "x \<in> H \<Longrightarrow> inv x \<in> H"

lemma (in subgroup) is_subgroup:
  "subgroup H G" by (rule subgroup_axioms)

declare (in subgroup) group.intro [intro]

lemma (in subgroup) mem_carrier [simp]:
  "x \<in> H \<Longrightarrow> x \<in> carrier G"
  using subset by blast

lemma subgroup_imp_subset:
  "subgroup H G \<Longrightarrow> H \<subseteq> carrier G"
  by (rule subgroup.subset)

lemma (in subgroup) subgroup_is_group [intro]:
  assumes "group G"
  shows "group (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret group G by fact
  show ?thesis
    apply (rule monoid.group_l_invI)
    apply (unfold_locales) [1]
    apply (auto intro: m_assoc l_inv mem_carrier)
    done
qed

text \<open>
  Since @{term H} is nonempty, it contains some element @{term x}.  Since
  it is closed under inverse, it contains \<open>inv x\<close>.  Since
  it is closed under product, it contains \<open>x \<otimes> inv x = \<one>\<close>.
\<close>

lemma (in group) one_in_subset:
  "[| H \<subseteq> carrier G; H \<noteq> {}; \<forall>a \<in> H. inv a \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<otimes> b \<in> H |]
   ==> \<one> \<in> H"
by force

text \<open>A characterization of subgroups: closed, non-empty subset.\<close>

lemma (in group) subgroupI:
  assumes subset: "H \<subseteq> carrier G" and non_empty: "H \<noteq> {}"
    and inv: "!!a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and mult: "!!a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
  shows "subgroup H G"
proof (simp add: subgroup_def assms)
  show "\<one> \<in> H" by (rule one_in_subset) (auto simp only: assms)
qed

lemma (in group) subgroupE:
  assumes "subgroup H G"
  shows "H \<subseteq> carrier G"
    and "H \<noteq> {}"
    and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
  using assms subgroup_imp_subset apply blast
  using assms subgroup_def apply auto[1]
  by (simp add: assms subgroup.m_closed subgroup.m_inv_closed)+

declare monoid.one_closed [iff] group.inv_closed [simp]
  monoid.l_one [simp] monoid.r_one [simp] group.inv_inv [simp]

lemma subgroup_nonempty:
  "~ subgroup {} G"
  by (blast dest: subgroup.one_closed)

lemma (in subgroup) finite_imp_card_positive:
  "finite (carrier G) ==> 0 < card H"
proof (rule classical)
  assume "finite (carrier G)" and a: "~ 0 < card H"
  then have "finite H" by (blast intro: finite_subset [OF subset])
  with is_subgroup a have "subgroup {} G" by simp
  with subgroup_nonempty show ?thesis by contradiction
qed

lemma (in group) group_incl_imp_subgroup :
  assumes "H \<subseteq> carrier G"
and "group (G\<lparr>carrier := H\<rparr>)"
shows "subgroup H G"
proof (intro subgroupI[OF assms(1)])
  have "carrier  (G\<lparr>carrier := H\<rparr>) \<noteq> {}" using assms
    using Group.group.axioms(1) by blast
  thus "H \<noteq> {}" by simp
  have ab_eq : "\<And> a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> a \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> b = a \<otimes> b" using assms by simp
  fix a b assume aH : "a \<in> H" and bH : "b \<in> H"
  have " inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a \<in> carrier G"
    using assms aH group.inv_closed[OF assms(2)] by auto
  moreover have "\<one>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> = \<one>" using assms monoid.one_closed ab_eq one_def by simp
  hence "a \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a= \<one>"
    using assms ab_eq aH  group.r_inv[OF assms(2)] by simp
  hence "a \<otimes> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a= \<one>"
    using aH assms group.inv_closed[OF assms(2)] ab_eq by simp
  ultimately have "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a = inv a"
    by (smt aH assms(1) contra_subsetD group.inv_inv is_group local.inv_equality)
  moreover have "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a \<in> H" using aH group.inv_closed[OF assms(2)] by auto
  ultimately show "inv a \<in> H" by auto
  have "\<And>a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> a \<otimes> b \<in> carrier (G\<lparr>carrier := H\<rparr>) "
    using assms ab_eq unfolding group_def using monoid.m_closed by fastforce
  thus "\<And>a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> a \<otimes> b \<in> H" by simp
qed
(*
lemma (in monoid) Units_subgroup:
  "subgroup (Units G) G"
*)

subsection \<open>Direct Products\<close>

definition
  DirProd :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<times> 'b) monoid" (infixr "\<times>\<times>" 80) where
  "G \<times>\<times> H =
    \<lparr>carrier = carrier G \<times> carrier H,
     mult = (\<lambda>(g, h) (g', h'). (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')),
     one = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)\<rparr>"

lemma DirProd_monoid:
  assumes "monoid G" and "monoid H"
  shows "monoid (G \<times>\<times> H)"
proof -
  interpret G: monoid G by fact
  interpret H: monoid H by fact
  from assms
  show ?thesis by (unfold monoid_def DirProd_def, auto) 
qed


text\<open>Does not use the previous result because it's easier just to use auto.\<close>
lemma DirProd_group:
  assumes "group G" and "group H"
  shows "group (G \<times>\<times> H)"
proof -
  interpret G: group G by fact
  interpret H: group H by fact
  show ?thesis by (rule groupI)
     (auto intro: G.m_assoc H.m_assoc G.l_inv H.l_inv
           simp add: DirProd_def)
qed

lemma carrier_DirProd [simp]:
     "carrier (G \<times>\<times> H) = carrier G \<times> carrier H"
  by (simp add: DirProd_def)

lemma one_DirProd [simp]:
     "\<one>\<^bsub>G \<times>\<times> H\<^esub> = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)"
  by (simp add: DirProd_def)

lemma mult_DirProd [simp]:
     "(g, h) \<otimes>\<^bsub>(G \<times>\<times> H)\<^esub> (g', h') = (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')"
  by (simp add: DirProd_def)

lemma DirProd_assoc :
"(G \<times>\<times> H \<times>\<times> I) = (G \<times>\<times> (H \<times>\<times> I))"
  by auto

lemma inv_DirProd [simp]:
  assumes "group G" and "group H"
  assumes g: "g \<in> carrier G"
      and h: "h \<in> carrier H"
  shows "m_inv (G \<times>\<times> H) (g, h) = (inv\<^bsub>G\<^esub> g, inv\<^bsub>H\<^esub> h)"
proof -
  interpret G: group G by fact
  interpret H: group H by fact
  interpret Prod: group "G \<times>\<times> H"
    by (auto intro: DirProd_group group.intro group.axioms assms)
  show ?thesis by (simp add: Prod.inv_equality g h)
qed

lemma DirProd_subgroups :
  assumes "group G"
and "subgroup H G"
and "group K"
and "subgroup I K"
shows "subgroup (H \<times> I) (G \<times>\<times> K)"
proof (intro group.group_incl_imp_subgroup[OF DirProd_group[OF assms(1)assms(3)]])
  have "H \<subseteq> carrier G" "I \<subseteq> carrier K" using subgroup_imp_subset assms apply blast+.
  thus "(H \<times> I) \<subseteq> carrier (G \<times>\<times> K)" unfolding DirProd_def by auto
  have "Group.group ((G\<lparr>carrier := H\<rparr>) \<times>\<times> (K\<lparr>carrier := I\<rparr>))"
    using DirProd_group[OF subgroup.subgroup_is_group[OF assms(2)assms(1)]
                           subgroup.subgroup_is_group[OF assms(4)assms(3)]].
  moreover have "((G\<lparr>carrier := H\<rparr>) \<times>\<times> (K\<lparr>carrier := I\<rparr>)) = ((G \<times>\<times> K)\<lparr>carrier := H \<times> I\<rparr>)"
    unfolding DirProd_def using assms apply simp.
  ultimately show "Group.group ((G \<times>\<times> K)\<lparr>carrier := H \<times> I\<rparr>)" by simp
qed

subsection \<open>Homomorphisms and Isomorphisms\<close>

definition
  hom :: "_ => _ => ('a => 'b) set" where
  "hom G H =
    {h. h \<in> carrier G \<rightarrow> carrier H &
      (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y)}"

lemma (in group) hom_compose:
  "[|h \<in> hom G H; i \<in> hom H I|] ==> compose (carrier G) i h \<in> hom G I"
by (fastforce simp add: hom_def compose_def)

definition
  iso :: "_ => _ => ('a => 'b) set"
  where "iso G  H = {h. h \<in> hom G H & bij_betw h (carrier G) (carrier H)}"

definition
is_iso :: "_ \<Rightarrow> _ \<Rightarrow> bool" (infixr "\<cong>" 60)
where "G \<cong> H = (iso G H  \<noteq> {})" 

lemma iso_set_refl: "(%x. x) \<in> iso G G"
  by (simp add: iso_def hom_def inj_on_def bij_betw_def Pi_def)

corollary iso_refl : "G \<cong> G"
  using iso_set_refl unfolding is_iso_def by auto

lemma (in group) iso_set_sym:
     "h \<in> iso G H \<Longrightarrow> inv_into (carrier G) h \<in> (iso H G)"
apply (simp add: iso_def bij_betw_inv_into) 
apply (subgoal_tac "inv_into (carrier G) h \<in> carrier H \<rightarrow> carrier G") 
 prefer 2 apply (simp add: bij_betw_imp_funcset [OF bij_betw_inv_into]) 
apply (simp add: hom_def bij_betw_def inv_into_f_eq f_inv_into_f Pi_def)
  done

corollary (in group) iso_sym :
"G \<cong> H \<Longrightarrow> H \<cong> G"
  using iso_set_sym unfolding is_iso_def by auto

lemma (in group) iso_set_trans: 
     "[|h \<in> iso G H; i \<in> iso H I|] ==> (compose (carrier G) i h) \<in> iso G I"
  by (auto simp add: iso_def hom_compose bij_betw_compose)

corollary (in group) iso_trans :
"\<lbrakk>G \<cong> H ; H \<cong> I\<rbrakk> \<Longrightarrow> G \<cong> I"
  using iso_set_trans unfolding is_iso_def by blast

lemma DirProd_commute_iso_set:
  shows "(\<lambda>(x,y). (y,x)) \<in> iso (G \<times>\<times> H) (H \<times>\<times> G)"
  by (auto simp add: iso_def hom_def inj_on_def bij_betw_def)

corollary DirProd_commute_iso :
"(G \<times>\<times> H) \<cong> (H \<times>\<times> G)"
  using DirProd_commute_iso_set unfolding is_iso_def by blast

lemma DirProd_assoc_iso_set:
  shows "(\<lambda>(x,y,z). (x,(y,z))) \<in> iso (G \<times>\<times> H \<times>\<times> I) (G \<times>\<times> (H \<times>\<times> I))"
by (auto simp add: iso_def hom_def inj_on_def bij_betw_def)

lemma (in group) DirProd_iso_set_trans: 
  assumes "g \<in> iso G G2"
    and "h \<in> iso H I"
  shows "(\<lambda>(x,y). (g x, h y)) \<in> iso (G \<times>\<times> H) (G2 \<times>\<times> I)"
proof-
  have "(\<lambda>(x,y). (g x, h y)) \<in> hom (G \<times>\<times> H) (G2 \<times>\<times> I)"
    using assms unfolding iso_def hom_def by auto
  moreover have " inj_on (\<lambda>(x,y). (g x, h y)) (carrier (G \<times>\<times> H))"
    using assms unfolding iso_def DirProd_def bij_betw_def inj_on_def by auto
  moreover have "(\<lambda>(x, y). (g x, h y)) ` carrier (G \<times>\<times> H) = carrier (G2 \<times>\<times> I)"
    using assms unfolding iso_def bij_betw_def image_def DirProd_def by fastforce
  ultimately show "(\<lambda>(x,y). (g x, h y)) \<in> iso (G \<times>\<times> H) (G2 \<times>\<times> I)"
    unfolding iso_def bij_betw_def by auto
qed

corollary (in group) DirProd_iso_trans :
  assumes "G \<cong> G2"
    and "H \<cong> I"
  shows "G \<times>\<times> H \<cong> G2 \<times>\<times> I"
  using DirProd_iso_set_trans assms unfolding is_iso_def by blast


text\<open>Basis for homomorphism proofs: we assume two groups @{term G} and
  @{term H}, with a homomorphism @{term h} between them\<close>
locale group_hom = G?: group G + H?: group H for G (structure) and H (structure) +
  fixes h
  assumes homh: "h \<in> hom G H"

lemma (in group_hom) hom_mult [simp]:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y"
proof -
  assume "x \<in> carrier G" "y \<in> carrier G"
  with homh [unfolded hom_def] show ?thesis by simp
qed

lemma (in group_hom) hom_closed [simp]:
  "x \<in> carrier G ==> h x \<in> carrier H"
proof -
  assume "x \<in> carrier G"
  with homh [unfolded hom_def] show ?thesis by auto
qed

lemma (in group_hom) one_closed [simp]:
  "h \<one> \<in> carrier H"
  by simp

lemma (in group_hom) hom_one [simp]:
  "h \<one> = \<one>\<^bsub>H\<^esub>"
proof -
  have "h \<one> \<otimes>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub> = h \<one> \<otimes>\<^bsub>H\<^esub> h \<one>"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  then show ?thesis by (simp del: r_one)
qed

lemma (in group_hom) inv_closed [simp]:
  "x \<in> carrier G ==> h (inv x) \<in> carrier H"
  by simp

lemma (in group_hom) hom_inv [simp]:
  "x \<in> carrier G ==> h (inv x) = inv\<^bsub>H\<^esub> (h x)"
proof -
  assume x: "x \<in> carrier G"
  then have "h x \<otimes>\<^bsub>H\<^esub> h (inv x) = \<one>\<^bsub>H\<^esub>"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  also from x have "... = h x \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h x)"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  finally have "h x \<otimes>\<^bsub>H\<^esub> h (inv x) = h x \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h x)" .
  with x show ?thesis by (simp del: H.r_inv H.Units_r_inv)
qed

(* Contributed by Paulo Emílio de Vilhena *)
lemma (in group) canonical_inj_is_hom:
  assumes "subgroup H G"
  shows "group_hom (G \<lparr> carrier := H \<rparr>) G id"
  unfolding group_hom_def group_hom_axioms_def hom_def
  using subgroup.subgroup_is_group[OF assms is_group]
        is_group subgroup_imp_subset[OF assms] by auto

(* Contributed by Joachim Breitner *)
lemma (in group) int_pow_is_hom:
  "x \<in> carrier G \<Longrightarrow> (op(^) x) \<in> hom \<lparr> carrier = UNIV, mult = op +, one = 0::int \<rparr> G "
  unfolding hom_def by (simp add: int_pow_mult)


subsection \<open>Commutative Structures\<close>

text \<open>
  Naming convention: multiplicative structures that are commutative
  are called \emph{commutative}, additive structures are called
  \emph{Abelian}.
\<close>

locale comm_monoid = monoid +
  assumes m_comm: "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"

lemma (in comm_monoid) m_lcomm:
  "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk> \<Longrightarrow>
   x \<otimes> (y \<otimes> z) = y \<otimes> (x \<otimes> z)"
proof -
  assume xyz: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  from xyz have "x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z" by (simp add: m_assoc)
  also from xyz have "... = (y \<otimes> x) \<otimes> z" by (simp add: m_comm)
  also from xyz have "... = y \<otimes> (x \<otimes> z)" by (simp add: m_assoc)
  finally show ?thesis .
qed

lemmas (in comm_monoid) m_ac = m_assoc m_comm m_lcomm

lemma comm_monoidI:
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
  shows "comm_monoid G"
  using l_one
    by (auto intro!: comm_monoid.intro comm_monoid_axioms.intro monoid.intro 
             intro: assms simp: m_closed one_closed m_comm)

lemma (in monoid) monoid_comm_monoidI:
  assumes m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_monoid G"
  by (rule comm_monoidI) (auto intro: m_assoc m_comm)

(*lemma (in comm_monoid) r_one [simp]:
  "x \<in> carrier G ==> x \<otimes> \<one> = x"
proof -
  assume G: "x \<in> carrier G"
  then have "x \<otimes> \<one> = \<one> \<otimes> x" by (simp add: m_comm)
  also from G have "... = x" by simp
  finally show ?thesis .
qed*)

lemma (in comm_monoid) nat_pow_distr:
  "[| x \<in> carrier G; y \<in> carrier G |] ==>
  (x \<otimes> y) (^) (n::nat) = x (^) n \<otimes> y (^) n"
  by (induct n) (simp, simp add: m_ac)

locale comm_group = comm_monoid + group

lemma (in group) group_comm_groupI:
  assumes m_comm: "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==>
      x \<otimes> y = y \<otimes> x"
  shows "comm_group G"
  by standard (simp_all add: m_comm)

lemma comm_groupI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "comm_group G"
  by (fast intro: group.group_comm_groupI groupI assms)

lemma comm_groupE:
  fixes G (structure)
  assumes "comm_group G"
  shows "\<And>x y. \<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
    and "\<one> \<in> carrier G"
    and "\<And>x y z. \<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and "\<And>x y. \<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  apply (simp_all add: group.axioms assms comm_group.axioms comm_monoid.m_comm comm_monoid.m_ac(1))
  by (simp_all add: Group.group.axioms(1) assms comm_group.axioms(2) monoid.m_closed group.r_inv_ex)

lemma (in comm_group) inv_mult:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv x \<otimes> inv y"
  by (simp add: m_ac inv_mult_group)


subsection \<open>The Lattice of Subgroups of a Group\<close>

text_raw \<open>\label{sec:subgroup-lattice}\<close>

theorem (in group) subgroups_partial_order:
  "partial_order \<lparr>carrier = {H. subgroup H G}, eq = op =, le = op \<subseteq>\<rparr>"
  by standard simp_all

lemma (in group) subgroup_self:
  "subgroup (carrier G) G"
  by (rule subgroupI) auto

lemma (in group) subgroup_imp_group:
  "subgroup H G ==> group (G\<lparr>carrier := H\<rparr>)"
  by (erule subgroup.subgroup_is_group) (rule group_axioms)

lemma (in group) is_monoid [intro, simp]:
  "monoid G"
  by (auto intro: monoid.intro m_assoc) 

lemma (in group) subgroup_inv_equality:
  "[| subgroup H G; x \<in> H |] ==> m_inv (G \<lparr>carrier := H\<rparr>) x = inv x"
apply (rule_tac inv_equality [THEN sym])
  apply (rule group.l_inv [OF subgroup_imp_group, simplified], assumption+)
 apply (rule subsetD [OF subgroup.subset], assumption+)
apply (rule subsetD [OF subgroup.subset], assumption)
apply (rule_tac group.inv_closed [OF subgroup_imp_group, simplified], assumption+)
  done

lemma (in group) subgroup_mult_equality:
  "\<lbrakk> subgroup H G; h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow>  h1 \<otimes>\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> h2 = h1 \<otimes> h2"
  unfolding subgroup_def by simp

theorem (in group) subgroups_Inter:
  assumes subgr: "(!!H. H \<in> A ==> subgroup H G)"
    and not_empty: "A ~= {}"
  shows "subgroup (\<Inter>A) G"
proof (rule subgroupI)
  from subgr [THEN subgroup.subset] and not_empty
  show "\<Inter>A \<subseteq> carrier G" by blast
next
  from subgr [THEN subgroup.one_closed]
  show "\<Inter>A ~= {}" by blast
next
  fix x assume "x \<in> \<Inter>A"
  with subgr [THEN subgroup.m_inv_closed]
  show "inv x \<in> \<Inter>A" by blast
next
  fix x y assume "x \<in> \<Inter>A" "y \<in> \<Inter>A"
  with subgr [THEN subgroup.m_closed]
  show "x \<otimes> y \<in> \<Inter>A" by blast
qed

lemma (in group) subgroups_Inter_pair :
  assumes  "subgroup I G" 
    and  "subgroup J G"
  shows "subgroup (I\<inter>J) G" using subgroups_Inter[ where ?A = "{I,J}"] assms by auto

theorem (in group) subgroups_complete_lattice:
  "complete_lattice \<lparr>carrier = {H. subgroup H G}, eq = op =, le = op \<subseteq>\<rparr>"
    (is "complete_lattice ?L")
proof (rule partial_order.complete_lattice_criterion1)
  show "partial_order ?L" by (rule subgroups_partial_order)
next
  have "greatest ?L (carrier G) (carrier ?L)"
    by (unfold greatest_def) (simp add: subgroup.subset subgroup_self)
  then show "\<exists>G. greatest ?L G (carrier ?L)" ..
next
  fix A
  assume L: "A \<subseteq> carrier ?L" and non_empty: "A ~= {}"
  then have Int_subgroup: "subgroup (\<Inter>A) G"
    by (fastforce intro: subgroups_Inter)
  have "greatest ?L (\<Inter>A) (Lower ?L A)" (is "greatest _ ?Int _")
  proof (rule greatest_LowerI)
    fix H
    assume H: "H \<in> A"
    with L have subgroupH: "subgroup H G" by auto
    from subgroupH have groupH: "group (G \<lparr>carrier := H\<rparr>)" (is "group ?H")
      by (rule subgroup_imp_group)
    from groupH have monoidH: "monoid ?H"
      by (rule group.is_monoid)
    from H have Int_subset: "?Int \<subseteq> H" by fastforce
    then show "le ?L ?Int H" by simp
  next
    fix H
    assume H: "H \<in> Lower ?L A"
    with L Int_subgroup show "le ?L H ?Int"
      by (fastforce simp: Lower_def intro: Inter_greatest)
  next
    show "A \<subseteq> carrier ?L" by (rule L)
  next
    show "?Int \<in> carrier ?L" by simp (rule Int_subgroup)
  qed
  then show "\<exists>I. greatest ?L I (Lower ?L A)" ..
qed

end
