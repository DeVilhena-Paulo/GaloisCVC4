(*  Title:      HOL/Algebra/Congruence.thy
    Author:     Clemens Ballarin, started 3 January 2008
    with thanks to Paulo Emílio de Vilhena
*)

theory Congruence
imports 
  Main
  "HOL-Library.FuncSet"
begin

section \<open>Objects\<close>

subsection \<open>Structure with Carrier Set.\<close>

record 'a partial_object =
  carrier :: "'a set"

lemma funcset_carrier:
  "\<lbrakk> f \<in> carrier X \<rightarrow> carrier Y; x \<in> carrier X \<rbrakk> \<Longrightarrow> f x \<in> carrier Y"
  by (fact funcset_mem)

lemma funcset_carrier':
  "\<lbrakk> f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A \<rbrakk> \<Longrightarrow> f x \<in> carrier A"
  by (fact funcset_mem)


subsection \<open>Structure with Carrier and Equivalence Relation \<open>eq\<close>\<close>

record 'a eq_object = "'a partial_object" +
  eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl ".=\<index>" 50)

definition
  elem :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl ".\<in>\<index>" 50)
  where "x .\<in>\<^bsub>S\<^esub> A \<longleftrightarrow> (\<exists>y \<in> A. x .=\<^bsub>S\<^esub> y)"

definition
  set_eq :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "{.=}\<index>" 50)
  where "A {.=}\<^bsub>S\<^esub> B \<longleftrightarrow> ((\<forall>x \<in> A. x .\<in>\<^bsub>S\<^esub> B) \<and> (\<forall>x \<in> B. x .\<in>\<^bsub>S\<^esub> A))"

definition
  eq_class_of :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set" ("class'_of\<index>")
  where "class_of\<^bsub>S\<^esub> x = {y \<in> carrier S. x .=\<^bsub>S\<^esub> y}"

definition
  eq_classes :: "_ \<Rightarrow> ('a set) set" ("classes\<index>")
  where "classes\<^bsub>S\<^esub> = {class_of\<^bsub>S\<^esub> x | x. x \<in> carrier S}"

definition
  eq_closure_of :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set" ("closure'_of\<index>")
  where "closure_of\<^bsub>S\<^esub> A = {y \<in> carrier S. y .\<in>\<^bsub>S\<^esub> A}"

definition
  eq_is_closed :: "_ \<Rightarrow> 'a set \<Rightarrow> bool" ("is'_closed\<index>")
  where "is_closed\<^bsub>S\<^esub> A \<longleftrightarrow> A \<subseteq> carrier S \<and> closure_of\<^bsub>S\<^esub> A = A"

abbreviation
  not_eq :: "_ \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl ".\<noteq>\<index>" 50)
  where "x .\<noteq>\<^bsub>S\<^esub> y \<equiv> \<not>(x .=\<^bsub>S\<^esub> y)"

abbreviation
  not_elem :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl ".\<notin>\<index>" 50)
  where "x .\<notin>\<^bsub>S\<^esub> A \<equiv> \<not>(x .\<in>\<^bsub>S\<^esub> A)"

abbreviation
  set_not_eq :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "{.\<noteq>}\<index>" 50)
  where "A {.\<noteq>}\<^bsub>S\<^esub> B \<equiv> \<not>(A {.=}\<^bsub>S\<^esub> B)"

locale equivalence =
  fixes S (structure)
  assumes refl [simp, intro]: "\<lbrakk> x \<in> carrier S \<rbrakk> \<Longrightarrow> x .= x"
    and sym [sym]:            "\<lbrakk> x \<in> carrier S; y \<in> carrier S \<rbrakk> \<Longrightarrow> x .= y \<Longrightarrow> y .= x"
    and trans [trans]:        "\<lbrakk> x \<in> carrier S; y \<in> carrier S; z \<in> carrier S \<rbrakk> \<Longrightarrow> 
                                 x .= y \<Longrightarrow> y .= z \<Longrightarrow> x .= z"

lemma equivalence_subset:
  assumes "equivalence L" "A \<subseteq> carrier L"
  shows "equivalence (L\<lparr> carrier := A \<rparr>)"
proof -
  interpret L: equivalence L
    by (simp add: assms)
  show ?thesis
    by (unfold_locales, simp_all add: L.sym assms rev_subsetD, meson L.trans assms(2) contra_subsetD)
qed


(* Lemmas by Stephan Hohe *)

lemma elemI:
  fixes R (structure)
  assumes "a' \<in> A" "a .= a'"
  shows "a .\<in> A"
  unfolding elem_def using assms by auto

lemma (in equivalence) elem_exact:
  assumes "a \<in> carrier S" "a \<in> A"
  shows "a .\<in> A"
  unfolding elem_def using assms by auto

lemma elemE:
  fixes S (structure)
  assumes "a .\<in> A"
    and "\<And>a'. \<lbrakk>a' \<in> A; a .= a'\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding elem_def by auto

lemma (in equivalence) elem_cong_l [trans]:
  assumes "a \<in> carrier S"  "a' \<in> carrier S" "A \<subseteq> carrier S"
    and "a' .= a" "a .\<in> A"
  shows "a' .\<in> A"
  using assms by (meson elem_def trans subsetCE)

lemma (in equivalence) elem_subsetD:
  assumes "A \<subseteq> B" "a .\<in> A"
  shows "a .\<in> B"
  using assms by (fast intro: elemI elim: elemE dest: subsetD)

lemma (in equivalence) mem_imp_elem [simp, intro]:
  assumes "x \<in> carrier S"
  shows "x \<in> A \<Longrightarrow> x .\<in> A"
  using assms unfolding elem_def by blast

lemma set_eqI:
  fixes R (structure)
  assumes "\<And>a. a \<in> A \<Longrightarrow> a .\<in> B"
    and   "\<And>b. b \<in> B \<Longrightarrow> b .\<in> A"
  shows "A {.=} B"
  using assms unfolding set_eq_def by auto

lemma set_eqI2:
  fixes R (structure)
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b \<in> B. a .= b"
    and   "\<And>b. b \<in> B \<Longrightarrow> \<exists>a \<in> A. b .= a"
  shows "A {.=} B"
  using assms by (simp add: set_eqI elem_def)  

lemma set_eqD1:
  fixes R (structure)
  assumes "A {.=} A'" and "a \<in> A"
  shows "\<exists>a' \<in> A'. a .= a'"
  using assms by (simp add: set_eq_def elem_def)

lemma set_eqD2:
  fixes R (structure)
  assumes "A {.=} A'" and "a' \<in> A'"
  shows "\<exists>a \<in> A. a' .= a"
  using assms by (simp add: set_eq_def elem_def)

lemma set_eqE:
  fixes R (structure)
  assumes "A {.=} B"
    and "\<lbrakk> \<forall>a \<in> A. a .\<in> B; \<forall>b \<in> B. b .\<in> A \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding set_eq_def by blast

lemma set_eqE2:
  fixes R (structure)
  assumes "A {.=} B"
    and "\<lbrakk> \<forall>a \<in> A. \<exists>b \<in> B. a .= b; \<forall>b \<in> B. \<exists>a \<in> A. b .= a \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding set_eq_def by (simp add: elem_def) 

lemma set_eqE':
  fixes R (structure)
  assumes "A {.=} B" "a \<in> A" "b \<in> B"
    and "\<And>a' b'. \<lbrakk> a' \<in> A; b' \<in> B \<rbrakk> \<Longrightarrow> b .= a' \<Longrightarrow>  a .= b' \<Longrightarrow> P"
  shows "P"
  using assms by (meson set_eqE2)

lemma (in equivalence) eq_elem_cong_r [trans]:
  assumes "A \<subseteq> carrier S" "A' \<subseteq> carrier S" "A {.=} A'"
  shows "\<lbrakk> a \<in> carrier S \<rbrakk> \<Longrightarrow> a .\<in> A \<Longrightarrow> a .\<in> A'"
  using assms by (meson elemE elem_cong_l set_eqE subset_eq)

lemma (in equivalence) set_eq_sym [sym]:
  assumes "A \<subseteq> carrier S" "B \<subseteq> carrier S"
  shows "A {.=} B \<Longrightarrow> B {.=} A"
  using assms unfolding set_eq_def elem_def by auto

lemma (in equivalence) equal_set_eq_trans [trans]:
  "\<lbrakk> A = B; B {.=} C \<rbrakk> \<Longrightarrow> A {.=} C"
  by simp

lemma (in equivalence) set_eq_equal_trans [trans]:
  "\<lbrakk> A {.=} B; B = C \<rbrakk> \<Longrightarrow> A {.=} C"
  by simp

lemma (in equivalence) set_eq_trans_aux:
  assumes "A \<subseteq> carrier S" "B \<subseteq> carrier S" "C \<subseteq> carrier S"
    and "A {.=} B" "B {.=} C"
  shows "\<And>a. a \<in> A \<Longrightarrow> a .\<in> C"
  using assms by (simp add: eq_elem_cong_r subset_iff) 

corollary (in equivalence) set_eq_trans [trans]:
  assumes "A \<subseteq> carrier S" "B \<subseteq> carrier S" "C \<subseteq> carrier S"
    and "A {.=} B" " B {.=} C"
    shows "A {.=} C"
proof (intro set_eqI)
  show "\<And>a. a \<in> A \<Longrightarrow> a .\<in> C" using set_eq_trans_aux assms by blast 
next
  show "\<And>b. b \<in> C \<Longrightarrow> b .\<in> A" using set_eq_trans_aux set_eq_sym assms by blast
qed

lemma (in equivalence) is_closedI:
  assumes "\<And>x y. \<lbrakk> y \<in> carrier S; x .= y \<rbrakk> \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A"
    and "A \<subseteq> carrier S"
  shows "is_closed A"
  unfolding eq_is_closed_def eq_closure_of_def
  using Collect_cong Collect_mem_eq assms(1) assms(2) elem_def elem_exact sym subsetCE by smt

lemma (in equivalence) closure_of_eq:
  assumes "A \<subseteq> carrier S" "x \<in> closure_of A"
  shows "\<lbrakk> x' \<in> carrier S; x .= x' \<rbrakk> \<Longrightarrow> x' \<in> closure_of A"
  using assms elem_cong_l sym unfolding eq_closure_of_def by blast 

lemma (in equivalence) is_closed_eq [dest]:
  assumes "is_closed A" "x \<in> A"
  shows "\<lbrakk> x .= x'; x' \<in> carrier S \<rbrakk> \<Longrightarrow> x' \<in> A"
  using assms closure_of_eq [where A = A] unfolding eq_is_closed_def by simp

corollary (in equivalence) is_closed_eq_rev [dest]:
  assumes "is_closed A" "x' \<in> A"
  shows "\<lbrakk> x .= x'; x \<in> carrier S \<rbrakk> \<Longrightarrow> x \<in> A"
  using sym is_closed_eq assms by (meson contra_subsetD eq_is_closed_def)

lemma closure_of_closed [simp, intro]:
  fixes S (structure)
  shows "closure_of A \<subseteq> carrier S"
  unfolding eq_closure_of_def by auto

lemma closure_of_memI:
  fixes S (structure)
  assumes "a .\<in> A" "a \<in> carrier S"
  shows "a \<in> closure_of A"
  unfolding eq_closure_of_def using assms by auto

lemma closure_ofI2:
  fixes S (structure)
  assumes "a .= a'" "a' \<in> A" "a \<in> carrier S"
  shows "a \<in> closure_of A"
  unfolding eq_closure_of_def elem_def using assms by auto

lemma closure_of_memE:
  fixes S (structure)
  assumes "a \<in> closure_of A"
    and "\<lbrakk> a \<in> carrier S; a .\<in> A \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding eq_closure_of_def by auto

lemma closure_ofE2:
  fixes S (structure)
  assumes "a \<in> closure_of A"
    and "\<And>a'. \<lbrakk>a \<in> carrier S; a' \<in> A; a .= a'\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (meson closure_of_memE elemE)


(* Lemmas by Paulo Emílio de Vilhena *)

lemma (in equivalence) set_eq_insert_aux:
  assumes "A \<subseteq> carrier S"
    and "x \<in> carrier S" "x' \<in> carrier S" "x .= x'"
    and "y \<in> insert x A"
  shows "y .\<in> insert x' A"
  by (metis assms(1) assms(4) assms(5) contra_subsetD elemI elem_exact insert_iff)

corollary (in equivalence) set_eq_insert:
  assumes "A \<subseteq> carrier S"
    and "x \<in> carrier S" "x' \<in> carrier S" "x .= x'"
  shows "insert x A {.=} insert x' A"
  by (meson set_eqI assms set_eq_insert_aux sym equivalence_axioms)

lemma (in equivalence) set_eq_pairI:
  assumes "x \<in> carrier S" "x' \<in> carrier S" "x .= x'"
    and "y \<in> carrier S"
  shows "{x, y} {.=} {x', y}"
  by (simp add: assms set_eq_insert)

lemma (in equivalence) closure_inclusion:
  assumes "A \<subseteq> B"
  shows "closure_of A \<subseteq> closure_of B"
  unfolding eq_closure_of_def using assms elem_subsetD by auto

lemma (in equivalence) classes_small:
  assumes "is_closed B"
    and "A \<subseteq> B"
  shows "closure_of A \<subseteq> B"
  by (metis assms closure_inclusion eq_is_closed_def)

lemma (in equivalence) classes_eq:
  assumes "A \<subseteq> carrier S"
  shows "A {.=} closure_of A"
  using assms by (blast intro: set_eqI elem_exact closure_of_memI elim: closure_of_memE)

lemma (in equivalence) complete_classes:
  assumes "is_closed A"
  shows "A = closure_of A"
  using assms by (simp add: eq_is_closed_def)

lemma (in equivalence) closure_idem_weak:
  "closure_of (closure_of A) {.=} closure_of A"
  by (simp add: classes_eq set_eq_sym)

lemma (in equivalence) closure_idem_strong:
  assumes "A \<subseteq> carrier S"
  shows "closure_of (closure_of A) = closure_of A"
  using assms closure_of_eq complete_classes is_closedI by auto

lemma (in equivalence) classes_consistent:
  assumes "A \<subseteq> carrier S"
  shows "is_closed (closure_of A)"
  using closure_idem_strong by (simp add: assms eq_is_closed_def)

lemma (in equivalence) classes_coverture:
  "\<Union>classes = carrier S"
proof
  show "\<Union>classes \<subseteq> carrier S"
    unfolding eq_classes_def eq_class_of_def by blast
next
  show "carrier S \<subseteq> \<Union>classes" unfolding eq_classes_def eq_class_of_def
  proof
    fix x assume "x \<in> carrier S"
    hence "x \<in> {y \<in> carrier S. x .= y}" using refl by simp
    thus "x \<in> \<Union>{{y \<in> carrier S. x .= y} |x. x \<in> carrier S}" by blast
  qed
qed

lemma (in equivalence) disjoint_union:
  assumes "class1 \<in> classes" "class2 \<in> classes"
    and "class1 \<inter> class2 \<noteq> {}"
    shows "class1 = class2"
proof -
  obtain x y where x: "x \<in> carrier S" "class1 = class_of x"
               and y: "y \<in> carrier S" "class2 = class_of y"
    using assms(1-2) unfolding eq_classes_def by blast
  obtain z   where z: "z \<in> carrier S" "z \<in> class1 \<inter> class2"
    using assms classes_coverture by fastforce
  hence "x .= z \<and> y .= z" using x y unfolding eq_class_of_def by blast
  hence "x .= y" using x y z trans sym by meson
  hence "class_of x = class_of y"
    unfolding eq_class_of_def using local.sym trans x y by blast
  thus ?thesis using x y by simp
qed
  
end
