(*  Title:      HOL/Algebra/FiniteProduct.thy
    Author:     Clemens Ballarin, started 19 November 2002

This file is largely based on HOL/Finite_Set.thy.
*)

theory FiniteProduct
imports Group
begin

subsection \<open>Product Operator for Commutative Monoids\<close>

subsubsection \<open>Inductive Definition of a Relation for Products over Sets\<close>

text \<open>Instantiation of locale \<open>LC\<close> of theory \<open>Finite_Set\<close> is not
  possible, because here we have explicit typing rules like 
  \<open>x \<in> carrier G\<close>.  We introduce an explicit argument for the domain
  \<open>D\<close>.\<close>

inductive_set
  foldSetD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a] \<Rightarrow> ('b set * 'a) set" for D and f and e where
    emptyI [intro]:  "e \<in> D \<Longrightarrow> ({}, e) \<in> foldSetD D f e"
  | insertI [intro]: "\<lbrakk> x \<notin> A; f x y \<in> D; (A, y) \<in> foldSetD D f e \<rbrakk> \<Longrightarrow>
                       (insert x A, f x y) \<in> foldSetD D f e"

inductive_cases empty_foldSetDE [elim!]: "({}, x) \<in> foldSetD D f e"

definition
  foldD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a, 'b set] \<Rightarrow> 'a"
  where "foldD D f e A = (THE x. (A, x) \<in> foldSetD D f e)"

lemma foldSetD_closed [dest]:
  "(A, z) \<in> foldSetD D f e \<Longrightarrow> z \<in> D"
  by (induction rule: foldSetD.induct)

lemma foldSetD_imp_finite [simp]:
  "(A, x) \<in> foldSetD D f e \<Longrightarrow> finite A"
  by (induct set: foldSetD) auto

lemma Diff1_foldSetD:
  "\<lbrakk> (A - {x}, y) \<in> foldSetD D f e; x \<in> A; f x y \<in> D \<rbrakk> \<Longrightarrow> (A, f x y) \<in> foldSetD D f e"
  by (metis Diff_insert_absorb foldSetD.insertI mk_disjoint_insert)

lemma finite_imp_foldSetD:
  "\<lbrakk> finite A; e \<in> D; \<And>x y. \<lbrakk> x \<in> A; y \<in> D \<rbrakk> \<Longrightarrow> f x y \<in> D \<rbrakk> \<Longrightarrow>
    \<exists> x. (A, x) \<in> foldSetD D f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSetD D f e" by auto
  with insert have "y \<in> D" by (auto dest: foldSetD_closed)
  with y and insert have "(insert x F, f x y) \<in> foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed

lemma foldSetD_backwards:
  assumes "A \<noteq> {}" "(A, z) \<in> foldSetD D f e"
  shows "\<exists>x y. x \<in> A \<and> (A - {x}, y) \<in> foldSetD D f e \<and> z = f x y" using assms(2)
proof (cases)
  case emptyI thus ?thesis using assms(1) by simp
next
  case (insertI x A y) thus ?thesis
    by (metis Diff_insert_absorb insertI1) 
qed


text \<open>Left-Commutative Operations\<close>

locale LCD =
  fixes B :: "'b set"
    and D :: "'a set"
    and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
  assumes left_commute: "\<lbrakk> x \<in> B; y \<in> B; z \<in> D \<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
  and f_closed [simp, intro!]: "\<And>x y. \<lbrakk> x \<in> B; y \<in> D \<rbrakk> \<Longrightarrow> f x y \<in> D"

lemma (in LCD) Diff1_foldSetD:
  "\<lbrakk> (A - { x }, y) \<in> foldSetD D f e; x \<in> A; A \<subseteq> B \<rbrakk> \<Longrightarrow> (A, f x y) \<in> foldSetD D f e"
  by (meson Diff1_foldSetD f_closed foldSetD_closed subsetCE)

lemma (in LCD) finite_imp_foldSetD:
  "\<lbrakk> finite A; A \<subseteq> B; e \<in> D \<rbrakk> \<Longrightarrow> \<exists>x. (A, x) \<in> foldSetD D f e"
  by (meson f_closed finite_imp_foldSetD subsetCE)

lemma (in LCD) foldSetD_determ_aux:
  assumes "e \<in> D" "A \<subseteq> B" "card A = n"
    and "(A, x) \<in> foldSetD D f e" "(A, y) \<in> foldSetD D f e"
  shows "x = y" using assms
proof (induction n arbitrary: A x y)
  case 0 thus ?case by auto
next
  case (Suc n)
  hence "A \<noteq> {}" by auto
  then obtain xa ya z1 z2
    where x: "xa \<in> A" "(A - { xa }, z1) \<in> foldSetD D f e" "x = xa \<cdot> z1"
      and y: "ya \<in> A" "(A - { ya }, z2) \<in> foldSetD D f e" "y = ya \<cdot> z2"
      by (meson foldSetD_backwards Suc)
  thus ?case
  proof (cases)
    assume Eq: "xa = ya" hence "z1 = z2"
      using Suc.IH[OF Suc(2) _ _ x(2), of z2] Suc(3-4,6) x(1) y(2) by auto
    thus ?thesis
      using x(3) y(3) Eq by simp
  next
    assume Ineq: "xa \<noteq> ya"
    hence "finite (A - { xa, ya })"
      using Suc.prems(4) by auto
    then obtain w where w: "w \<in> D" "(A - { xa, ya }, w) \<in> foldSetD D f e"
      using finite_imp_foldSetD Suc.prems by (meson Diff_subset foldSetD_closed order_trans)

    hence "((A - { xa }) - { ya }, w) \<in> foldSetD D f e"
      by (metis Diff_insert2)
    hence "(A - { xa }, ya \<cdot> w) \<in> foldSetD D f e"
      using Diff1_foldSetD[of "A - { xa }" ya w e] Ineq y(1) x(1) Suc(3) by auto
    hence "ya \<cdot> w = z1"
      using Suc.IH[OF Suc(2) _ _ x(2), of "ya \<cdot> w"] Suc(3-4,6) x(1) by auto

    moreover
    have "((A - { ya }) - { xa }, w) \<in> foldSetD D f e"
      using w by (metis Diff_insert)
    hence "(A - { ya }, xa \<cdot> w) \<in> foldSetD D f e"
      using Diff1_foldSetD[of "A - { ya }" xa w e] Ineq y(1) x(1) Suc(3) by auto
    hence "xa \<cdot> w = z2"
      using Suc.IH[OF Suc(2) _ _ y(2), of "xa \<cdot> w"] Suc(3-4,6) y(1) by auto

    ultimately show ?thesis
      using Suc.prems(2) w(1) x y left_commute by blast
  qed
qed

lemma (in LCD) foldSetD_determ:
  "\<lbrakk> (A, x) \<in> foldSetD D f e; (A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B \<rbrakk> \<Longrightarrow> y = x"
  by (blast intro: foldSetD_determ_aux [rule_format])

lemma (in LCD) foldD_equality:
  "\<lbrakk> (A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B \<rbrakk> \<Longrightarrow> foldD D f e A = y"
  by (unfold foldD_def) (blast intro: foldSetD_determ)

lemma foldD_empty [simp]:
  "e \<in> D \<Longrightarrow> foldD D f e {} = e"
  by (unfold foldD_def) blast

lemma (in LCD) foldD_insert_aux:
  "\<lbrakk> x \<notin> A; x \<in> B; e \<in> D; A \<subseteq> B \<rbrakk> \<Longrightarrow>
    ((insert x A, v) \<in> foldSetD D f e) = (\<exists> y. (A, y) \<in> foldSetD D f e \<and> v = f x y)"
  by (metis Diff_insert_absorb finite_insert foldD_equality foldSetD_imp_finite insertI1
      insert_subset local.Diff1_foldSetD local.finite_imp_foldSetD)

lemma (in LCD) foldD_insert:
  "\<lbrakk> finite A; x \<notin> A; x \<in> B; e \<in> D; A \<subseteq> B \<rbrakk> \<Longrightarrow> foldD D f e (insert x A) = f x (foldD D f e A)"
  by (metis Diff_insert_absorb LCD.foldD_equality LCD_axioms insertI1 insert_subsetI
      local.Diff1_foldSetD local.finite_imp_foldSetD)

lemma (in LCD) foldD_closed [simp]:
  "\<lbrakk> finite A; e \<in> D; A \<subseteq> B \<rbrakk> \<Longrightarrow> foldD D f e A \<in> D"
proof (induct set: finite)
  case empty thus ?case by simp
next
  case insert thus ?case by (simp add: foldD_insert)
qed

lemma (in LCD) foldD_commute:
  "\<lbrakk> finite A; x \<in> B; e \<in> D; A \<subseteq> B \<rbrakk> \<Longrightarrow> f x (foldD D f e A) = foldD D f (f x e) A"
  apply (induct set: finite)
   apply simp
  apply (auto simp add: left_commute foldD_insert)
  done

lemma Int_mono2: "\<lbrakk> A \<subseteq> C; B \<subseteq> C \<rbrakk> \<Longrightarrow> A \<inter> B \<subseteq> C"
  by blast

lemma (in LCD) foldD_nest_Un_Int:
  "\<lbrakk> finite A; finite C; e \<in> D; A \<subseteq> B; C \<subseteq> B \<rbrakk> \<Longrightarrow>
    foldD D f (foldD D f e C) A = foldD D f (foldD D f e (A \<inter> C)) (A \<union> C)"
  apply (induct set: finite)
   apply simp
  apply (simp add: foldD_insert foldD_commute Int_insert_left insert_absorb Int_mono2)
  done

lemma (in LCD) foldD_nest_Un_disjoint:
  "\<lbrakk> finite A; finite B; A \<inter> B = {}; e \<in> D; A \<subseteq> B; C \<subseteq> B \<rbrakk> \<Longrightarrow>
    foldD D f e (A \<union> B) = foldD D f (foldD D f e B) A"
  by (simp add: foldD_nest_Un_Int)

\<comment> \<open>Delete rules to do with \<open>foldSetD\<close> relation.\<close>

declare foldSetD_imp_finite [simp del]
  empty_foldSetDE [rule del]
  foldSetD.intros [rule del]
declare (in LCD)
  foldSetD_closed [rule del]


text \<open>Commutative Monoids\<close>

text \<open>
  We enter a more restrictive context, with \<open>f :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> instead of \<open>'b \<Rightarrow> 'a \<Rightarrow> 'a\<close>.
\<close>

locale ACeD =
  fixes D :: "'a set"
    and e :: 'a
    and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 70)
  assumes ident [simp]: "x \<in> D \<Longrightarrow> x \<cdot> e = x"
    and commute: "\<lbrakk> x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
    and assoc: "\<lbrakk> x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and e_closed [simp]: "e \<in> D"
    and f_closed [simp]: "\<lbrakk> x \<in> D; y \<in> D \<rbrakk> \<Longrightarrow> x \<cdot> y \<in> D"

lemma (in ACeD) left_commute:
  "\<lbrakk> x \<in> D; y \<in> D; z \<in> D \<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
  using assoc commute by auto

lemma (in ACeD) LCD_of_ACeD: "LCD D D f"
  by (simp add: LCD_def left_commute)

lemmas (in ACeD) AC = assoc commute left_commute

lemma (in ACeD) left_ident [simp]: "x \<in> D \<Longrightarrow> e \<cdot> x = x"
  using commute ident by fastforce

lemma (in ACeD) foldD_Un_Int:
  "\<lbrakk> finite A; finite B; A \<subseteq> D; B \<subseteq> D \<rbrakk> \<Longrightarrow>
     foldD D f e A \<cdot> foldD D f e B = foldD D f e (A \<union> B) \<cdot> foldD D f e (A \<inter> B)"
  apply (induct set: finite)
   apply (simp add: left_commute LCD.foldD_closed [OF LCD.intro [of D]])
  apply (simp add: AC insert_absorb Int_insert_left
    LCD.foldD_insert [OF LCD.intro [of D]]
    LCD.foldD_closed [OF LCD.intro [of D]]
    Int_mono2)
  done

lemma (in ACeD) foldD_Un_disjoint:
  "\<lbrakk> finite A; finite B; A \<inter> B = {}; A \<subseteq> D; B \<subseteq> D \<rbrakk> \<Longrightarrow>
    foldD D f e (A \<union> B) = foldD D f e A \<cdot> foldD D f e B"
  by (simp add: foldD_Un_Int left_commute LCD.foldD_closed [OF LCD.intro [of D]])


subsubsection \<open>Products over Finite Sets\<close>

definition
  finprod :: "[('b, 'm) monoid_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b"
  where "finprod G f A =
   (if finite A
    then foldD (carrier G) (mult G o f) \<one>\<^bsub>G\<^esub> A
    else \<one>\<^bsub>G\<^esub>)"

syntax
  "_finprod" :: "index => idt => 'a set => 'b => 'b"
      ("(3\<Otimes>__\<in>_. _)" [1000, 0, 51, 10] 10)
translations
  "\<Otimes>\<^bsub>G\<^esub>i\<in>A. b" \<rightleftharpoons> "CONST finprod G (\<lambda>i. b) A"
  \<comment> \<open>Beware of argument permutation!\<close>

lemma (in comm_monoid) finprod_empty [simp]: 
  "finprod G f {} = \<one>"
  by (simp add: finprod_def)

lemma (in comm_monoid) finprod_infinite[simp]:
  "\<not> finite A \<Longrightarrow> finprod G f A = \<one>" 
  by (simp add: finprod_def)

declare funcsetI [intro]
  funcset_mem [dest]

context comm_monoid begin

lemma finprod_insert [simp]:
  "[| finite F; a \<notin> F; f \<in> F \<rightarrow> carrier G; f a \<in> carrier G |] ==>
   finprod G f (insert a F) = f a \<otimes> finprod G f F"
  apply (rule trans)
   apply (simp add: finprod_def)
  apply (rule trans)
   apply (rule LCD.foldD_insert [OF LCD.intro [of "insert a F"]])
         apply simp
         apply (rule m_lcomm)
           apply fast
          apply fast
         apply assumption
        apply fastforce
       apply simp+
   apply fast
  apply (auto simp add: finprod_def)
  done

lemma finprod_one [simp]: "(\<Otimes>i\<in>A. \<one>) = \<one>"
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A)
  have "(%i. \<one>) \<in> A \<rightarrow> carrier G" by auto
  with insert show ?case by simp
qed simp

lemma finprod_closed [simp]:
  fixes A
  assumes f: "f \<in> A \<rightarrow> carrier G" 
  shows "finprod G f A \<in> carrier G"
using f
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A)
  then have a: "f a \<in> carrier G" by fast
  from insert have A: "f \<in> A \<rightarrow> carrier G" by fast
  from insert A a show ?case by simp
qed simp

lemma funcset_Int_left [simp, intro]:
  "[| f \<in> A \<rightarrow> C; f \<in> B \<rightarrow> C |] ==> f \<in> A Int B \<rightarrow> C"
  by fast

lemma funcset_Un_left [iff]:
  "(f \<in> A Un B \<rightarrow> C) = (f \<in> A \<rightarrow> C & f \<in> B \<rightarrow> C)"
  by fast

lemma finprod_Un_Int:
  "[| finite A; finite B; g \<in> A \<rightarrow> carrier G; g \<in> B \<rightarrow> carrier G |] ==>
     finprod G g (A Un B) \<otimes> finprod G g (A Int B) =
     finprod G g A \<otimes> finprod G g B"
\<comment> \<open>The reversed orientation looks more natural, but LOOPS as a simprule!\<close>
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert a A)
  then have a: "g a \<in> carrier G" by fast
  from insert have A: "g \<in> A \<rightarrow> carrier G" by fast
  from insert A a show ?case
    by (simp add: m_ac Int_insert_left insert_absorb Int_mono2) 
qed

lemma finprod_Un_disjoint:
  "[| finite A; finite B; A Int B = {};
      g \<in> A \<rightarrow> carrier G; g \<in> B \<rightarrow> carrier G |]
   ==> finprod G g (A Un B) = finprod G g A \<otimes> finprod G g B"
  apply (subst finprod_Un_Int [symmetric])
      apply auto
  done

lemma finprod_multf:
  "[| f \<in> A \<rightarrow> carrier G; g \<in> A \<rightarrow> carrier G |] ==>
   finprod G (%x. f x \<otimes> g x) A = (finprod G f A \<otimes> finprod G g A)"
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A) then
  have fA: "f \<in> A \<rightarrow> carrier G" by fast
  from insert have fa: "f a \<in> carrier G" by fast
  from insert have gA: "g \<in> A \<rightarrow> carrier G" by fast
  from insert have ga: "g a \<in> carrier G" by fast
  from insert have fgA: "(%x. f x \<otimes> g x) \<in> A \<rightarrow> carrier G"
    by (simp add: Pi_def)
  show ?case
    by (simp add: insert fA fa gA ga fgA m_ac)
qed simp

lemma finprod_cong':
  "[| A = B; g \<in> B \<rightarrow> carrier G;
      !!i. i \<in> B ==> f i = g i |] ==> finprod G f A = finprod G g B"
proof -
  assume prems: "A = B" "g \<in> B \<rightarrow> carrier G"
    "!!i. i \<in> B ==> f i = g i"
  show ?thesis
  proof (cases "finite B")
    case True
    then have "!!A. [| A = B; g \<in> B \<rightarrow> carrier G;
      !!i. i \<in> B ==> f i = g i |] ==> finprod G f A = finprod G g B"
    proof induct
      case empty thus ?case by simp
    next
      case (insert x B)
      then have "finprod G f A = finprod G f (insert x B)" by simp
      also from insert have "... = f x \<otimes> finprod G f B"
      proof (intro finprod_insert)
        show "finite B" by fact
      next
        show "x ~: B" by fact
      next
        assume "x ~: B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
          "g \<in> insert x B \<rightarrow> carrier G"
        thus "f \<in> B \<rightarrow> carrier G" by fastforce
      next
        assume "x ~: B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
          "g \<in> insert x B \<rightarrow> carrier G"
        thus "f x \<in> carrier G" by fastforce
      qed
      also from insert have "... = g x \<otimes> finprod G g B" by fastforce
      also from insert have "... = finprod G g (insert x B)"
      by (intro finprod_insert [THEN sym]) auto
      finally show ?case .
    qed
    with prems show ?thesis by simp
  next
    case False with prems show ?thesis by simp
  qed
qed

lemma finprod_cong:
  "[| A = B; f \<in> B \<rightarrow> carrier G = True;
      !!i. i \<in> B =simp=> f i = g i |] ==> finprod G f A = finprod G g B"
  (* This order of prems is slightly faster (3%) than the last two swapped. *)
  by (rule finprod_cong') (auto simp add: simp_implies_def)

text \<open>Usually, if this rule causes a failed congruence proof error,
  the reason is that the premise \<open>g \<in> B \<rightarrow> carrier G\<close> cannot be shown.
  Adding @{thm [source] Pi_def} to the simpset is often useful.
  For this reason, @{thm [source] finprod_cong}
  is not added to the simpset by default.
\<close>

end

declare funcsetI [rule del]
  funcset_mem [rule del]

context comm_monoid begin

lemma finprod_0 [simp]:
  "f \<in> {0::nat} \<rightarrow> carrier G ==> finprod G f {..0} = f 0"
by (simp add: Pi_def)

lemma finprod_0':
  "f \<in> {.. n :: nat} \<rightarrow> carrier G \<Longrightarrow> (f 0) \<otimes> finprod G f {Suc 0..n} = finprod G f {..n}"
proof -
  assume A: "f \<in> {.. n :: nat} \<rightarrow> carrier G"
  hence "(f 0) \<otimes> finprod G f {Suc 0..n} = finprod G f {..0} \<otimes> finprod G f {Suc 0..n}"
    using finprod_0[of f] by (simp add: funcset_mem)
  also have " ... = finprod G f ({..0} \<union> {Suc 0..n})"
    using finprod_Un_disjoint[of "{..0}" "{Suc 0..n}" f] A by (simp add: funcset_mem)
  also have " ... = finprod G f {..n}"
    by (simp add: atLeastAtMost_insertL atMost_atLeast0)
  finally show ?thesis .
qed
    

lemma finprod_Suc [simp]:
  "f \<in> {..Suc n} \<rightarrow> carrier G ==>
   finprod G f {..Suc n} = (f (Suc n) \<otimes> finprod G f {..n})"
by (simp add: Pi_def atMost_Suc)

lemma finprod_Suc2:
  "f \<in> {..Suc n} \<rightarrow> carrier G ==>
   finprod G f {..Suc n} = (finprod G (%i. f (Suc i)) {..n} \<otimes> f 0)"
proof (induct n)
  case 0 thus ?case by (simp add: Pi_def)
next
  case Suc thus ?case by (simp add: m_assoc Pi_def)
qed

lemma finprod_Suc3:
  assumes "f \<in> {.. n :: nat} \<rightarrow> carrier G"
  shows "finprod G f {.. n} = (f n) \<otimes> finprod G f {..< n}"
proof (cases "n = 0")
  case True thus ?thesis
   using assms atMost_Suc by simp
next
  case False
  then obtain k where "n = Suc k"
    using not0_implies_Suc by blast
  thus ?thesis
    using finprod_Suc[of f k] assms atMost_Suc lessThan_Suc_atMost by simp
qed

lemma finprod_mult [simp]:
  "[| f \<in> {..n} \<rightarrow> carrier G; g \<in> {..n} \<rightarrow> carrier G |] ==>
     finprod G (%i. f i \<otimes> g i) {..n::nat} =
     finprod G f {..n} \<otimes> finprod G g {..n}"
  by (induct n) (simp_all add: m_ac Pi_def)

(* The following two were contributed by Jeremy Avigad. *)

lemma finprod_reindex:
  "f : (h ` A) \<rightarrow> carrier G \<Longrightarrow> 
        inj_on h A ==> finprod G f (h ` A) = finprod G (%x. f (h x)) A"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  hence "\<not> finite (h ` A)"
    using finite_imageD by blast
  with \<open>\<not> finite A\<close> show ?case by simp
qed (auto simp add: Pi_def)

lemma finprod_const:
  assumes a [simp]: "a : carrier G"
    shows "finprod G (\<lambda>x. a) A = a [^] card A"
proof (induct A rule: infinite_finite_induct)
  case (insert b A)
  show ?case 
  proof (subst finprod_insert[OF insert(1-2)])
    show "a \<otimes> (\<Otimes>x\<in>A. a) = a [^] card (insert b A)"
      by (insert insert, auto, subst m_comm, auto)
  qed auto
qed auto

(* The following lemma was contributed by Jesus Aransay. *)

lemma finprod_singleton:
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and f_Pi: "f \<in> A \<rightarrow> carrier G"
  shows "(\<Otimes>j\<in>A. if i = j then f j else \<one>) = f i"
  using i_in_A finprod_insert [of "A - {i}" i "(\<lambda>j. if i = j then f j else \<one>)"]
    fin_A f_Pi finprod_one [of "A - {i}"]
    finprod_cong [of "A - {i}" "A - {i}" "(\<lambda>j. if i = j then f j else \<one>)" "(\<lambda>i. \<one>)"] 
  unfolding Pi_def simp_implies_def by (force simp add: insert_absorb)

end

end
