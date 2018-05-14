(*  Title:      HOL/Algebra/QuotRing.thy
    Author:     Stephan Hohe
*)

theory QuotRing
imports RingHom
begin

section \<open>Quotient Rings\<close>

subsection \<open>Multiplication on Cosets\<close>

definition rcoset_mult :: "[('a, _) ring_scheme, 'a set, 'a set, 'a set] \<Rightarrow> 'a set"
    ("[mod _:] _ \<Otimes>\<index> _" [81,81,81] 80)
  where "rcoset_mult R I A B = (\<Union>a\<in>A. \<Union>b\<in>B. I +>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> b))"


text \<open>@{const "rcoset_mult"} fulfils the properties required by
  congruences\<close>
lemma (in ideal) rcoset_mult_add:
    "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> [mod I:] (I +> x) \<Otimes> (I +> y) = I +> (x \<otimes> y)"
  apply rule
  apply (rule, simp add: rcoset_mult_def, clarsimp)
  defer 1
  apply (rule, simp add: rcoset_mult_def)
  defer 1
proof -
  fix z x' y'
  assume carr: "x \<in> carrier R" "y \<in> carrier R"
    and x'rcos: "x' \<in> I +> x"
    and y'rcos: "y' \<in> I +> y"
    and zrcos: "z \<in> I +> x' \<otimes> y'"

  from x'rcos have "\<exists>h\<in>I. x' = h \<oplus> x"
    by (simp add: a_r_coset_def r_coset_def)
  then obtain hx where hxI: "hx \<in> I" and x': "x' = hx \<oplus> x"
    by fast+

  from y'rcos have "\<exists>h\<in>I. y' = h \<oplus> y"
    by (simp add: a_r_coset_def r_coset_def)
  then obtain hy where hyI: "hy \<in> I" and y': "y' = hy \<oplus> y"
    by fast+

  from zrcos have "\<exists>h\<in>I. z = h \<oplus> (x' \<otimes> y')"
    by (simp add: a_r_coset_def r_coset_def)
  then obtain hz where hzI: "hz \<in> I" and z: "z = hz \<oplus> (x' \<otimes> y')"
    by fast+

  note carr = carr hxI[THEN a_Hcarr] hyI[THEN a_Hcarr] hzI[THEN a_Hcarr]

  from z have "z = hz \<oplus> (x' \<otimes> y')" .
  also from x' y' have "\<dots> = hz \<oplus> ((hx \<oplus> x) \<otimes> (hy \<oplus> y))" by simp
  also from carr have "\<dots> = (hz \<oplus> (hx \<otimes> (hy \<oplus> y)) \<oplus> x \<otimes> hy) \<oplus> x \<otimes> y" by algebra
  finally have z2: "z = (hz \<oplus> (hx \<otimes> (hy \<oplus> y)) \<oplus> x \<otimes> hy) \<oplus> x \<otimes> y" .

  from hxI hyI hzI carr have "hz \<oplus> (hx \<otimes> (hy \<oplus> y)) \<oplus> x \<otimes> hy \<in> I"
    by (simp add: I_l_closed I_r_closed)

  with z2 have "\<exists>h\<in>I. z = h \<oplus> x \<otimes> y" by fast
  then show "z \<in> I +> x \<otimes> y" by (simp add: a_r_coset_def r_coset_def)
next
  fix z
  assume xcarr: "x \<in> carrier R"
    and ycarr: "y \<in> carrier R"
    and zrcos: "z \<in> I +> x \<otimes> y"
  from xcarr have xself: "x \<in> I +> x" by (intro a_rcos_self)
  from ycarr have yself: "y \<in> I +> y" by (intro a_rcos_self)
  show "\<exists>a\<in>I +> x. \<exists>b\<in>I +> y. z \<in> I +> a \<otimes> b"
    using xself and yself and zrcos by fast
qed


subsection \<open>Quotient Ring Definition\<close>

definition FactRing :: "[('a,'b) ring_scheme, 'a set] \<Rightarrow> ('a set) ring"
    (infixl "Quot" 65)
  where "FactRing R I =
    \<lparr>carrier = a_rcosets\<^bsub>R\<^esub> I, mult = rcoset_mult R I,
      one = (I +>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>), zero = I, add = set_add R\<rparr>"


subsection \<open>Factorization over General Ideals\<close>

text \<open>The quotient is a ring\<close>
lemma (in ideal) quotient_is_ring: "ring (R Quot I)"
apply (rule ringI)
   \<comment>\<open>abelian group\<close>
   apply (rule comm_group_abelian_groupI)
   apply (simp add: FactRing_def)
   apply (rule a_factorgroup_is_comm_group[unfolded A_FactGroup_def'])
  \<comment>\<open>mult monoid\<close>
  apply (rule monoidI)
      apply (simp_all add: FactRing_def A_RCOSETS_def RCOSETS_def
             a_r_coset_def[symmetric])
      \<comment>\<open>mult closed\<close>
      apply (clarify)
      apply (simp add: rcoset_mult_add, fast)
     \<comment>\<open>mult \<open>one_closed\<close>\<close>
     apply force
    \<comment>\<open>mult assoc\<close>
    apply clarify
    apply (simp add: rcoset_mult_add m_assoc)
   \<comment>\<open>mult one\<close>
   apply clarify
   apply (simp add: rcoset_mult_add)
  apply clarify
  apply (simp add: rcoset_mult_add)
 \<comment>\<open>distr\<close>
 apply clarify
 apply (simp add: rcoset_mult_add a_rcos_sum l_distr)
apply clarify
apply (simp add: rcoset_mult_add a_rcos_sum r_distr)
done


text \<open>This is a ring homomorphism\<close>

lemma (in ideal) rcos_ring_hom: "(op +> I) \<in> ring_hom R (R Quot I)"
apply (rule ring_hom_memI)
   apply (simp add: FactRing_def a_rcosetsI[OF a_subset])
  apply (simp add: FactRing_def rcoset_mult_add)
 apply (simp add: FactRing_def a_rcos_sum)
apply (simp add: FactRing_def)
done

lemma (in ideal) rcos_ring_hom_ring: "ring_hom_ring R (R Quot I) (op +> I)"
apply (rule ring_hom_ringI)
     apply (rule is_ring, rule quotient_is_ring)
   apply (simp add: FactRing_def a_rcosetsI[OF a_subset])
  apply (simp add: FactRing_def rcoset_mult_add)
 apply (simp add: FactRing_def a_rcos_sum)
apply (simp add: FactRing_def)
done

text \<open>The quotient of a cring is also commutative\<close>
lemma (in ideal) quotient_is_cring:
  assumes "cring R"
  shows "cring (R Quot I)"
proof -
  interpret cring R by fact
  show ?thesis
    apply (intro cring.intro comm_monoid.intro comm_monoid_axioms.intro)
      apply (rule quotient_is_ring)
     apply (rule ring.axioms[OF quotient_is_ring])
    apply (simp add: FactRing_def A_RCOSETS_defs a_r_coset_def[symmetric])
    apply clarify
    apply (simp add: rcoset_mult_add m_comm)
    done
qed

text \<open>Cosets as a ring homomorphism on crings\<close>
lemma (in ideal) rcos_ring_hom_cring:
  assumes "cring R"
  shows "ring_hom_cring R (R Quot I) (op +> I)"
proof -
  interpret cring R by fact
  show ?thesis
    apply (rule ring_hom_cringI)
      apply (rule rcos_ring_hom_ring)
     apply (rule is_cring)
    apply (rule quotient_is_cring)
   apply (rule is_cring)
   done
qed


subsection \<open>Factorization over Prime Ideals\<close>

text \<open>The quotient ring generated by a prime ideal is a domain\<close>
lemma (in primeideal) quotient_is_domain: "domain (R Quot I)"
  apply (rule domain.intro)
   apply (rule quotient_is_cring, rule is_cring)
  apply (rule domain_axioms.intro)
   apply (simp add: FactRing_def) defer 1
    apply (simp add: FactRing_def A_RCOSETS_defs a_r_coset_def[symmetric], clarify)
    apply (simp add: rcoset_mult_add) defer 1
proof (rule ccontr, clarsimp)
  assume "I +> \<one> = I"
  then have "\<one> \<in> I" by (simp only: a_coset_join1 one_closed a_subgroup)
  then have "carrier R \<subseteq> I" by (subst one_imp_carrier, simp, fast)
  with a_subset have "I = carrier R" by fast
  with I_notcarr show False by fast
next
  fix x y
  assume carr: "x \<in> carrier R" "y \<in> carrier R"
    and a: "I +> x \<otimes> y = I"
    and b: "I +> y \<noteq> I"

  have ynI: "y \<notin> I"
  proof (rule ccontr, simp)
    assume "y \<in> I"
    then have "I +> y = I" by (rule a_rcos_const)
    with b show False by simp
  qed

  from carr have "x \<otimes> y \<in> I +> x \<otimes> y" by (simp add: a_rcos_self)
  then have xyI: "x \<otimes> y \<in> I" by (simp add: a)

  from xyI and carr have xI: "x \<in> I \<or> y \<in> I" by (simp add: I_prime)
  with ynI have "x \<in> I" by fast
  then show "I +> x = I" by (rule a_rcos_const)
qed

text \<open>Generating right cosets of a prime ideal is a homomorphism
        on commutative rings\<close>
lemma (in primeideal) rcos_ring_hom_cring: "ring_hom_cring R (R Quot I) (op +> I)"
  by (rule rcos_ring_hom_cring) (rule is_cring)


subsection \<open>Factorization over Maximal Ideals\<close>

text \<open>In a commutative ring, the quotient ring over a maximal ideal
        is a field.
        The proof follows ``W. Adkins, S. Weintraub: Algebra --
        An Approach via Module Theory''\<close>
lemma (in maximalideal) quotient_is_field:
  assumes "cring R"
  shows "field (R Quot I)"
proof -
  interpret cring R by fact
  show ?thesis
    apply (intro cring.cring_fieldI2)
      apply (rule quotient_is_cring, rule is_cring)
     defer 1
     apply (simp add: FactRing_def A_RCOSETS_defs a_r_coset_def[symmetric], clarsimp)
     apply (simp add: rcoset_mult_add) defer 1
  proof (rule ccontr, simp)
    \<comment>\<open>Quotient is not empty\<close>
    assume "\<zero>\<^bsub>R Quot I\<^esub> = \<one>\<^bsub>R Quot I\<^esub>"
    then have II1: "I = I +> \<one>" by (simp add: FactRing_def)
    from a_rcos_self[OF one_closed] have "\<one> \<in> I"
      by (simp add: II1[symmetric])
    then have "I = carrier R" by (rule one_imp_carrier)
    with I_notcarr show False by simp
  next
    \<comment>\<open>Existence of Inverse\<close>
    fix a
    assume IanI: "I +> a \<noteq> I" and acarr: "a \<in> carrier R"

    \<comment>\<open>Helper ideal \<open>J\<close>\<close>
    define J :: "'a set" where "J = (carrier R #> a) <+> I"
    have idealJ: "ideal J R"
      apply (unfold J_def, rule add_ideals)
       apply (simp only: cgenideal_eq_rcos[symmetric], rule cgenideal_ideal, rule acarr)
      apply (rule is_ideal)
      done

    \<comment>\<open>Showing @{term "J"} not smaller than @{term "I"}\<close>
    have IinJ: "I \<subseteq> J"
    proof (rule, simp add: J_def r_coset_def set_add_defs)
      fix x
      assume xI: "x \<in> I"
      have Zcarr: "\<zero> \<in> carrier R" by fast
      from xI[THEN a_Hcarr] acarr
      have "x = \<zero> \<otimes> a \<oplus> x" by algebra
      with Zcarr and xI show "\<exists>xa\<in>carrier R. \<exists>k\<in>I. x = xa \<otimes> a \<oplus> k" by fast
    qed

    \<comment>\<open>Showing @{term "J \<noteq> I"}\<close>
    have anI: "a \<notin> I"
    proof (rule ccontr, simp)
      assume "a \<in> I"
      then have "I +> a = I" by (rule a_rcos_const)
      with IanI show False by simp
    qed

    have aJ: "a \<in> J"
    proof (simp add: J_def r_coset_def set_add_defs)
      from acarr
      have "a = \<one> \<otimes> a \<oplus> \<zero>" by algebra
      with one_closed and additive_subgroup.zero_closed[OF is_additive_subgroup]
      show "\<exists>x\<in>carrier R. \<exists>k\<in>I. a = x \<otimes> a \<oplus> k" by fast
    qed

    from aJ and anI have JnI: "J \<noteq> I" by fast

    \<comment>\<open>Deducing @{term "J = carrier R"} because @{term "I"} is maximal\<close>
    from idealJ and IinJ have "J = I \<or> J = carrier R"
    proof (rule I_maximal, unfold J_def)
      have "carrier R #> a \<subseteq> carrier R"
        using subset_refl acarr by (rule r_coset_subset_G)
      then show "carrier R #> a <+> I \<subseteq> carrier R"
        using a_subset by (rule set_add_closed)
    qed

    with JnI have Jcarr: "J = carrier R" by simp

    \<comment>\<open>Calculating an inverse for @{term "a"}\<close>
    from one_closed[folded Jcarr]
    have "\<exists>r\<in>carrier R. \<exists>i\<in>I. \<one> = r \<otimes> a \<oplus> i"
      by (simp add: J_def r_coset_def set_add_defs)
    then obtain r i where rcarr: "r \<in> carrier R"
      and iI: "i \<in> I" and one: "\<one> = r \<otimes> a \<oplus> i" by fast
    from one and rcarr and acarr and iI[THEN a_Hcarr]
    have rai1: "a \<otimes> r = \<ominus>i \<oplus> \<one>" by algebra

    \<comment>\<open>Lifting to cosets\<close>
    from iI have "\<ominus>i \<oplus> \<one> \<in> I +> \<one>"
      by (intro a_rcosI, simp, intro a_subset, simp)
    with rai1 have "a \<otimes> r \<in> I +> \<one>" by simp
    then have "I +> \<one> = I +> a \<otimes> r"
      by (rule a_repr_independence, simp) (rule a_subgroup)

    from rcarr and this[symmetric]
    show "\<exists>r\<in>carrier R. I +> a \<otimes> r = I +> \<one>" by fast
  qed
qed


subsection \<open>Isomorphism\<close>

definition
  ring_iso :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "ring_iso R S = { h. h \<in> ring_hom R S \<and> bij_betw h (carrier R) (carrier S) }"

definition
  is_ring_iso :: "_ \<Rightarrow> _ \<Rightarrow> bool" (infixr "\<simeq>" 60)
  where "R \<simeq> S = (ring_iso R S \<noteq> {})"


lemma ring_iso_memI:
  fixes R (structure) and S (structure)
  assumes "\<And>x. x \<in> carrier R \<Longrightarrow> h x \<in> carrier S"
      and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
      and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<oplus> y) = h x \<oplus>\<^bsub>S\<^esub> h y"
      and "h \<one> = \<one>\<^bsub>S\<^esub>"
      and "bij_betw h (carrier R) (carrier S)"
  shows "h \<in> ring_iso R S"
  by (auto simp add: ring_hom_memI assms ring_iso_def)

lemma ring_iso_refl: "R \<simeq> R"
proof -
  have "id \<in> ring_iso R R" by (rule ring_iso_memI) (auto)
  thus ?thesis using is_ring_iso_def by auto 
qed

lemma ring_iso_trans: "\<lbrakk> R \<simeq> S; S \<simeq> Q \<rbrakk> \<Longrightarrow> R \<simeq> Q"
proof -
  assume "R \<simeq> S" "S \<simeq> Q"
  then obtain f g where f: "f \<in> ring_hom R S" "bij_betw f (carrier R) (carrier S)"
                    and g: "g \<in> ring_hom S Q" "bij_betw g (carrier S) (carrier Q)"
    unfolding is_ring_iso_def ring_iso_def by blast
  hence gof_bij: "bij_betw (g \<circ> f) (carrier R) (carrier Q)"
    using bij_betw_comp_iff by blast

  have "g \<circ> f \<in> ring_iso R Q"
    apply (rule ring_iso_memI)
    using gof_bij bij_betwE apply blast
    apply (smt bij_betwE comp_apply f g(1) ring_hom_mult)
    apply (smt bij_betwE comp_apply f g(1) ring_hom_add)
    apply (metis comp_def f(1) g(1) ring_hom_one)
    by (simp add: gof_bij)

  thus ?thesis unfolding is_ring_iso_def by auto
qed

lemma ring_iso_sym:
  assumes "ring R"
  shows "R \<simeq> S \<Longrightarrow> S \<simeq> R"
proof -
  assume "R \<simeq> S" then obtain h where h: "h \<in> ring_iso R S"
    unfolding is_ring_iso_def by blast
  hence h_hom:  "h \<in> ring_hom R S"
    and h_surj: "h ` (carrier R) = (carrier S)"
    and h_inj:  "\<And> x1 x2. \<lbrakk> x1 \<in> carrier R; x2 \<in> carrier R \<rbrakk> \<Longrightarrow>  h x1 = h x2 \<Longrightarrow> x1 = x2"
    unfolding ring_iso_def bij_betw_def inj_on_def by auto

  have h_inv_bij: "bij_betw (inv_into (carrier R) h) (carrier S) (carrier R)"
      using bij_betw_inv_into h ring_iso_def by fastforce

  have "inv_into (carrier R) h \<in> ring_iso S R"
    apply (rule ring_iso_memI)
    apply (simp add: h_surj inv_into_into)
    apply (auto simp add: h_inv_bij)
    apply (smt assms f_inv_into_f h_hom h_inj h_surj inv_into_into
           ring.ring_simprules(5) ring_hom_closed ring_hom_mult)
    apply (smt assms f_inv_into_f h_hom h_inj h_surj inv_into_into
           ring.ring_simprules(1) ring_hom_add ring_hom_closed)
    by (metis (no_types, hide_lams) assms f_inv_into_f h_hom h_inj
        imageI inv_into_into ring.ring_simprules(6) ring_hom_one)

  thus ?thesis using is_ring_iso_def by auto 
qed

theorem (in ring_hom_ring) FactRing_iso_set:
  assumes "h ` carrier R = carrier S"
  shows "(\<lambda>X. the_elem (h ` X)) \<in> ring_iso (R Quot (a_kernel R S h)) S"
proof (rule ring_iso_memI)
  have quot_mem:
    "\<And>X. X \<in> carrier (R Quot (a_kernel R S h)) \<Longrightarrow> \<exists>x \<in> carrier R. X = (a_kernel R S h) +> x"
  proof -
    fix X assume "X \<in> carrier (R Quot (a_kernel R S h))"
    thus "\<exists>x \<in> carrier R. X = (a_kernel R S h) +> x"
      unfolding FactRing_def RCOSETS_def A_RCOSETS_def by (simp add: a_r_coset_def)
  qed

  have well_founded:
    "\<And>X. X \<in> carrier (R Quot (a_kernel R S h)) \<Longrightarrow> \<exists>y \<in> carrier S. (h ` X) = { y }"
  proof -
    fix X assume "X \<in> carrier (R Quot (a_kernel R S h))"
    then obtain x where x: "x \<in> carrier R" and X: "X = (a_kernel R S h) +> x"
      using quot_mem by blast
    hence "\<And>x'. x' \<in> X \<Longrightarrow> h x' = h x"
    proof -
      fix x' assume "x' \<in> X" hence "x' \<in> (a_kernel R S h) +> x" using X by simp
      then obtain k where k: "k \<in> a_kernel R S h" "x' = k \<oplus> x"
        by (metis R.add.inv_closed R.add.m_assoc R.l_neg R.r_zero
            abelian_subgroup.a_elemrcos_carrier
            abelian_subgroup.a_rcos_module_imp abelian_subgroup_a_kernel x)
      hence "h x' = h k \<oplus>\<^bsub>S\<^esub> h x"
        by (meson additive_subgroup.a_Hcarr additive_subgroup_a_kernel hom_add x)
      also have " ... =  h x"
        using k by (auto simp add: x)
      finally show "h x' = h x" .
    qed
    moreover have "h x \<in> h ` X"
      by (simp add: X homeq_imp_rcos x)
    ultimately have "(h ` X) = { h x }"
      by blast
    thus "\<exists>y \<in> carrier S. (h ` X) = { y }"
      by (simp add: assms x) 
  qed

  have the_elem_simp [simp]:
    "\<And>x. x \<in> carrier R \<Longrightarrow> the_elem (h ` ((a_kernel R S h) +> x)) = h x"
  proof -
    fix x assume x: "x \<in> carrier R"
    hence "h x \<in> h ` ((a_kernel R S h) +> x)"
      using homeq_imp_rcos by blast
    thus "the_elem (h ` ((a_kernel R S h) +> x)) = h x"
      by (metis (no_types, lifting) x empty_iff homeq_imp_rcos rcos_imp_homeq the_elem_image_unique)
  qed

  have the_elem_inj:
    "\<And>X Y. \<lbrakk> X \<in> carrier (R Quot (a_kernel R S h)); Y \<in> carrier (R Quot (a_kernel R S h)) \<rbrakk> \<Longrightarrow>
             the_elem (h ` X) = the_elem (h ` Y) \<Longrightarrow> X = Y"
  proof -
    fix X Y
    assume "X \<in> carrier (R Quot (a_kernel R S h))"
       and "Y \<in> carrier (R Quot (a_kernel R S h))"
       and Eq: "the_elem (h ` X) = the_elem (h ` Y)"
    then obtain x y where x: "x \<in> carrier R" "X = (a_kernel R S h) +> x"
                      and y: "y \<in> carrier R" "Y = (a_kernel R S h) +> y" using quot_mem by blast
    hence "h x = h y" using Eq by simp
    hence "x \<ominus> y \<in> (a_kernel R S h)"
      by (simp add: a_minus_def abelian_subgroup.a_rcos_module_imp
                    abelian_subgroup_a_kernel homeq_imp_rcos x(1) y(1))
    thus "X = Y"
      by (metis R.a_coset_add_inv1 R.minus_eq abelian_subgroup.a_rcos_const
          abelian_subgroup_a_kernel additive_subgroup.a_subset additive_subgroup_a_kernel x y)
  qed

  have the_elem_surj:
    "(\<lambda>X. (the_elem (h ` X))) ` carrier (R Quot (a_kernel R S h)) = carrier S"
  proof -
    have "carrier S \<subseteq> (\<lambda>X. (the_elem (h ` X))) ` carrier (R Quot (a_kernel R S h))"
    proof
      fix y assume "y \<in> carrier S"
      then obtain x where x: "x \<in> carrier R" "h x = y"
        using assms by (metis image_iff)
      hence "the_elem (h ` ((a_kernel R S h) +> x)) = y" by simp
      moreover have "(a_kernel R S h) +> x \<in> carrier (R Quot (a_kernel R S h))"
      unfolding FactRing_def RCOSETS_def A_RCOSETS_def by (auto simp add: x a_r_coset_def)
      ultimately show "y \<in> (\<lambda>X. (the_elem (h ` X))) ` carrier (R Quot (a_kernel R S h))" by blast
    qed
    thus ?thesis using well_founded by fastforce
  qed

  show "bij_betw (\<lambda>X. the_elem (h ` X)) (carrier (R Quot a_kernel R S h)) (carrier S)"
    unfolding bij_betw_def inj_on_def using the_elem_surj the_elem_inj by simp

  show "\<And>x. x \<in> carrier (R Quot a_kernel R S h) \<Longrightarrow> the_elem (h ` x) \<in> carrier S"
    using well_founded by fastforce
  
  show "the_elem (h ` \<one>\<^bsub>R Quot a_kernel R S h\<^esub>) = \<one>\<^bsub>S\<^esub>"
    unfolding FactRing_def  using the_elem_simp[of "\<one>\<^bsub>R\<^esub>"] by simp

  fix X Y
  assume "X \<in> carrier (R Quot a_kernel R S h)"
     and "Y \<in> carrier (R Quot a_kernel R S h)"
  then obtain x y where x: "x \<in> carrier R" "X = (a_kernel R S h) +> x"
                    and y: "y \<in> carrier R" "Y = (a_kernel R S h) +> y"
    using quot_mem by blast

  have "X \<otimes>\<^bsub>R Quot a_kernel R S h\<^esub> Y = (a_kernel R S h) +> (x \<otimes> y)"
    by (simp add: FactRing_def ideal.rcoset_mult_add kernel_is_ideal x y)
  thus "the_elem (h ` (X \<otimes>\<^bsub>R Quot a_kernel R S h\<^esub> Y)) = the_elem (h ` X) \<otimes>\<^bsub>S\<^esub> the_elem (h ` Y)"
    by (simp add: x y)

  have "X \<oplus>\<^bsub>R Quot a_kernel R S h\<^esub> Y = (a_kernel R S h) +> (x \<oplus> y)"
    using ideal.rcos_ring_hom kernel_is_ideal ring_hom_add x y by fastforce
  thus "the_elem (h ` (X \<oplus>\<^bsub>R Quot a_kernel R S h\<^esub> Y)) = the_elem (h ` X) \<oplus>\<^bsub>S\<^esub> the_elem (h ` Y)"
    by (simp add: x y)
qed

corollary (in ring_hom_ring) FactRing_iso:
  assumes "h ` carrier R = carrier S"
  shows "R Quot (a_kernel R S h) \<simeq> S"
  using FactRing_iso_set assms is_ring_iso_def by auto

end
