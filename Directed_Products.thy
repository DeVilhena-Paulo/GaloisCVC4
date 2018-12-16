theory Directed_Products
imports "HOL-Algebra.QuotRing"

begin

section \<open>Directed Products\<close>


subsection \<open>Definitions\<close>

definition product_group :: "'a set \<Rightarrow> ('a \<Rightarrow> ('b, 'c) monoid_scheme) \<Rightarrow> ('a \<Rightarrow> 'b) monoid"
  where "product_group I G \<equiv>
           \<lparr> carrier = (\<Pi>\<^sub>E i\<in>I. carrier (G i)),
                mult = (\<lambda>x y. (\<lambda>i\<in>I. mult (G i) (x i) (y i))),
                 one = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>) \<rparr>"

definition product_ring :: "'a set \<Rightarrow> ('a \<Rightarrow> ('b, 'c) ring_scheme) \<Rightarrow> ('a \<Rightarrow> 'b) ring"
  where "product_ring I R \<equiv> monoid.extend (product_group I R)
           \<lparr> zero = one (product_group I (add_monoid \<circ> R)),
              add = mult (product_group I (add_monoid \<circ> R)) \<rparr>"

definition RDirProd :: "('a, 'n) ring_scheme \<Rightarrow> ('b, 'm) ring_scheme \<Rightarrow> ('a \<times> 'b) ring"
  where "RDirProd R S = monoid.extend (R \<times>\<times> S)
           \<lparr> zero = one ((add_monoid R) \<times>\<times> (add_monoid S)),
              add = mult ((add_monoid R) \<times>\<times> (add_monoid S)) \<rparr>"


subsection \<open>Basic Properties\<close>

text \<open>Usual unfolding lemmas : useful for unfolding one field at a time.\<close>

lemma product_group_fields:
  "carrier (product_group I G) = (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
  "mult    (product_group I G) = (\<lambda>x y. (\<lambda>i\<in>I. mult (G i) (x i) (y i)))"
  "one     (product_group I G) = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)"
  unfolding product_group_def by simp+

lemma product_ring_fields:
  "carrier (product_ring I R) = (\<Pi>\<^sub>E i\<in>I. carrier (R i))"
  "mult    (product_ring I R) = (\<lambda>x y. (\<lambda>i\<in>I. mult (R i) (x i) (y i)))"
  "one     (product_ring I R) = (\<lambda>i\<in>I. \<one>\<^bsub>R i\<^esub>)"
  "add     (product_ring I R) = (\<lambda>x y. (\<lambda>i\<in>I. add (R i) (x i) (y i)))"
  "zero    (product_ring I R) = (\<lambda>i\<in>I. \<zero>\<^bsub>R i\<^esub>)"
  unfolding product_ring_def product_group_def by (simp add: monoid.defs)+

lemma RDirProd_fields:
  "carrier (RDirProd R S) = carrier R \<times> carrier S"
  "mult    (RDirProd R S) = (\<lambda>(r, s) (r', s'). (r \<otimes>\<^bsub>R\<^esub> r', s \<otimes>\<^bsub>S\<^esub> s'))"
  "one     (RDirProd R S) = (\<one>\<^bsub>R\<^esub>, \<one>\<^bsub>S\<^esub>)"
  "add     (RDirProd R S) = (\<lambda>(r, s) (r', s'). (r \<oplus>\<^bsub>R\<^esub> r', s \<oplus>\<^bsub>S\<^esub> s'))"
  "zero    (RDirProd R S) = (\<zero>\<^bsub>R\<^esub>, \<zero>\<^bsub>S\<^esub>)"
  unfolding RDirProd_def DirProd_def by (simp add: monoid.defs)+

lemma product_ring_truncate:
  shows "monoid.truncate (product_ring I R) = product_group I R"
  unfolding product_ring_def by (simp add: monoid.defs)

lemma product_ring_add_monoid:
  shows "add_monoid (product_ring I R) = product_group I (add_monoid \<circ> R)"
  unfolding product_group_def product_ring_def by (simp add: monoid.defs)

lemma RDirProd_truncate:
  shows "monoid.truncate (RDirProd R S) = R \<times>\<times> S"
  unfolding RDirProd_def by (simp add: monoid.defs)

lemma RDirProd_add_monoid [simp]:
  shows "add_monoid (RDirProd R S) = (add_monoid R) \<times>\<times> (add_monoid S)"
  by (simp add: RDirProd_def monoid.defs)


subsection \<open>Morphisms\<close>

lemma RDirProd_iso1:
  "(\<lambda>(x, y). (y, x)) \<in> ring_iso (RDirProd R S) (RDirProd S R)"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_iso2:
  "(\<lambda>(x, (y, z)). ((x, y), z)) \<in> ring_iso (RDirProd R (RDirProd S T)) (RDirProd (RDirProd R S) T)"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: image_iff RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_iso3:
  "(\<lambda>((x, y), z). (x, (y, z))) \<in> ring_iso (RDirProd (RDirProd R S) T) (RDirProd R (RDirProd S T))"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: image_iff RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_iso4:
  assumes "f \<in> ring_iso R S" shows "(\<lambda>(r, t). (f r, t)) \<in> ring_iso (RDirProd R T) (RDirProd S T)"
  using assms unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: image_iff RDirProd_def DirProd_def monoid.defs)+

lemma RDirProd_iso5:
  assumes "f \<in> ring_iso S T" shows "(\<lambda>(r, s). (r, f s)) \<in> ring_iso (RDirProd R S) (RDirProd R T)"
  using ring_iso_set_trans[OF ring_iso_set_trans[OF RDirProd_iso1 RDirProd_iso4[OF assms]] RDirProd_iso1]
  by (simp add: case_prod_unfold comp_def)

lemma RDirProd_iso6:
  assumes "f \<in> ring_iso R R'" and "g \<in> ring_iso S S'"
  shows "(\<lambda>(r, s). (f r, g s)) \<in> ring_iso (RDirProd R S) (RDirProd R' S')"
  using ring_iso_set_trans[OF RDirProd_iso4[OF assms(1)] RDirProd_iso5[OF assms(2)]]
  by (simp add: case_prod_beta' comp_def)

lemma RDirProd_hom1:
  shows "(\<lambda>a. (a, a)) \<in> ring_hom R (RDirProd R R)"
  by (auto simp add: ring_hom_def RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_hom2:
  assumes "f \<in> ring_hom S T"
  shows "(\<lambda>(x, y). (x, f y)) \<in> ring_hom (RDirProd R S) (RDirProd R T)"
    and "(\<lambda>(x, y). (f x, y)) \<in> ring_hom (RDirProd S R) (RDirProd T R)"
  using assms by (auto simp add: ring_hom_def RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_hom3:
  assumes "f \<in> ring_hom R R'" and "g \<in> ring_hom S S'"
  shows "(\<lambda>(r, s). (f r, g s)) \<in> ring_hom (RDirProd R S) (RDirProd R' S')"
  using ring_hom_trans[OF RDirProd_hom2(2)[OF assms(1)] RDirProd_hom2(1)[OF assms(2)]]
  by (simp add: case_prod_beta' comp_def)

lemma RDirProd_proj1:
  shows "fst \<in> ring_hom (RDirProd R S) R"
  by (auto simp add: ring_hom_def RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_proj2:
  shows "snd \<in> ring_hom (RDirProd R S) S"
  by (auto simp add: ring_hom_def RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_cartesian:
  assumes "f \<in> ring_hom X R" and "g \<in> ring_hom X S"
  shows "(\<lambda>x. (f x, g x)) \<in> ring_hom X (RDirProd R S)"
  using assms by (auto simp add: ring_hom_def RDirProd_def DirProd_def monoid.defs)

(* Move --------------------------------------------------------------------- *)
lemma DirProd_proj1:
  shows "fst \<in> hom (G \<times>\<times> H) G"
  by (auto simp add: hom_def DirProd_def)

lemma DirProd_proj2:
  shows "snd \<in> hom (G \<times>\<times> H) H"
  by (auto simp add: hom_def DirProd_def)

lemma DirProd_cartesian:
  assumes "f \<in> hom X G" and "g \<in> hom X H"
  shows "(\<lambda>x. (f x, g x)) \<in> hom X (G \<times>\<times> H)"
  using assms by (auto simp add: hom_def DirProd_def)
(* -------------------------------------------------------------------------- *)

(* Rename / Move ------------------------------------------------------------ *)
lemma Times_singleton:
  "bij_betw (\<lambda>a. (a, b)) A (A \<times> { b })"
  by (intro bij_betwI', auto)

lemma bij_betw_Times_Pi:
  shows "bij_betw (\<lambda>(a, b). \<lambda>i. if i then a else b) (A \<times> B) (\<Pi> i\<in>UNIV. if i then A else B)"
  by (intro bij_betwI', auto simp add: Pi_iff) (metis)+

lemma bij_betw_Times_PiE:
  shows "bij_betw (\<lambda>(a, b). \<lambda>i. if i then a else b) (A \<times> B) (\<Pi>\<^sub>E i\<in>UNIV. if i then A else B)"
  by (simp add: bij_betw_Times_Pi PiE_UNIV_domain)

lemma bij_betw_Pi_Times:
  shows "bij_betw (\<lambda>f. (f True, f False)) (\<Pi> i\<in>UNIV. if i then A else B) (A \<times> B)"
proof (intro iffD1[OF bij_betw_cong[OF inv_into_f_eq[OF bij_betw_imp_inj_on[OF bij_betw_Times_Pi]]]
                      bij_betw_inv_into[OF bij_betw_Times_Pi]], auto)
  show "f True \<in> A" and "f False \<in> B" if "f \<in> (\<Pi> i\<in>UNIV. if i then A else B)" for f
    using Pi_mem[OF that, of True] Pi_mem[OF that, of False] by simp+
qed

lemma bij_betw_PiE_Times:
  shows "bij_betw (\<lambda>f. (f True, f False)) (\<Pi>\<^sub>E i\<in>UNIV. if i then A else B) (A \<times> B)"
  by (simp add: bij_betw_Pi_Times PiE_UNIV_domain)

lemma bij_combinator: (* named in accordance with the lemma 'inj_combinator' *)
  assumes "i \<notin> I"
  shows "bij_betw (\<lambda>(a, f). f(i := a)) (A i \<times> (\<Pi>\<^sub>E j\<in>I. A j)) (\<Pi>\<^sub>E j\<in>(insert i I). A j)"
  by (intro bij_betw_imageI[OF inj_combinator[OF assms] sym[OF PiE_insert_eq]])

lemma bij_combinator':
  assumes "i \<notin> I"
  shows "bij_betw (\<lambda>f. (f i, f(i := undefined))) (\<Pi>\<^sub>E j\<in>(insert i I). A j) (A i \<times> (\<Pi>\<^sub>E j\<in>I. A j))"
  using bij_betw_imp_inj_on[OF bij_combinator[OF assms]]
  by (intro iffD1[OF bij_betw_cong[OF inv_into_f_eq]
                        bij_betw_inv_into[OF bij_combinator[OF assms]]])
     (auto simp add: assms)
(* -------------------------------------------------------------------------- *)

lemma product_group_iso1:
  shows "(\<lambda>(g, h). \<lambda>b. if b then g else h) \<in>
          iso (G \<times>\<times> H) (product_group UNIV (\<lambda>b. if b then G else H))"
  unfolding iso_def hom_def product_group_def
  using bij_betw_Times_PiE[of "carrier G" "carrier H"]
  by (auto, smt PiE_cong)

lemma product_group_iso2:
  shows "(\<lambda>f. (f True, f False)) \<in>
          iso (product_group UNIV (\<lambda>b. if b then G else H)) (G \<times>\<times> H)"
  unfolding iso_def hom_def product_group_def
  using bij_betw_PiE_Times[of "carrier G" "carrier H"]
  by (auto, smt PiE PiE_UNIV_domain UNIV_I PiE_cong)+

lemma product_group_iso3:
  assumes "i \<notin> I"
  shows "(\<lambda>(g, f). f(i := g)) \<in>
          iso ((G i) \<times>\<times> (product_group I G)) (product_group (insert i I) G)"
  unfolding iso_def hom_def product_group_def
  using bij_combinator[OF assms, of "\<lambda>i. carrier (G i)"]
  by (auto, meson PiE_E)

lemma product_group_iso4:
  assumes "i \<notin> I"
  shows "(\<lambda>f. (f i, f(i := undefined))) \<in>
          iso (product_group (insert i I) G) ((G i) \<times>\<times> (product_group I G))"
  unfolding iso_def hom_def product_group_def
  using bij_combinator'[OF assms, of "\<lambda>i. carrier (G i)"] assms
  by auto

lemma product_group_proj:
  assumes "i \<in> I" shows "(\<lambda>f. f i) \<in> hom (product_group I G) (G i)"
proof -
  have "fst \<circ> (\<lambda>f. (f i, f(i := undefined))) \<in> hom (product_group I G) (G i)"
    using product_group_iso4[of i "I - {i}" G] assms
    by (intro hom_trans[OF _ DirProd_proj1, where ?H1 = "product_group (I - {i}) G"])
       (auto simp add: iso_def insert_absorb[OF assms])
  thus ?thesis
    by (simp add: comp_def)
qed

lemma product_group_cartesian:
  assumes "h \<in> (\<Pi> i\<in>I. hom X (G i))" shows "(\<lambda>x. \<lambda>i\<in>I. (h i) x) \<in> hom X (product_group I G)"
  using Pi_mem[OF assms] unfolding product_group_fields(1,2) hom_def
  by fastforce

lemma product_ring_iso1:
  shows "(\<lambda>(r, s). \<lambda>b. if b then r else s) \<in>
          ring_iso (RDirProd R S) (product_ring UNIV (\<lambda>b. if b then R else S))"
  unfolding ring_iso_def ring_hom_def RDirProd_def product_ring_def product_group_def
  using bij_betw_Times_PiE[of "carrier R" "carrier S"]
  by (auto simp add: monoid.defs, smt PiE_cong)

lemma product_ring_iso2:
  shows "(\<lambda>f. (f True, f False)) \<in>
          ring_iso (product_ring UNIV (\<lambda>b. if b then R else S)) (RDirProd R S)"
  unfolding ring_iso_def ring_hom_def RDirProd_def product_ring_def product_group_def
  using bij_betw_PiE_Times[of "carrier R" "carrier S"]
  by (auto simp add: monoid.defs, smt PiE PiE_UNIV_domain UNIV_I PiE_cong)+

lemma product_ring_iso3:
  assumes "i \<notin> I"
  shows "(\<lambda>(r, f). f(i := r)) \<in>
          ring_iso (RDirProd (R i) (product_ring I R)) (product_ring (insert i I) R)"
  using bij_combinator[OF assms, of "\<lambda>i. carrier (R i)"]
  unfolding ring_iso_def ring_hom_def RDirProd_def
  by (auto simp add: product_ring_fields monoid.defs, meson PiE_E)

lemma product_ring_iso4:
  assumes "i \<notin> I"
  shows "(\<lambda>f. (f i, f(i := undefined))) \<in>
          ring_iso (product_ring (insert i I) R) (RDirProd (R i) (product_ring I R))"
  using bij_combinator'[OF assms, of "\<lambda>i. carrier (R i)"] assms
  unfolding ring_iso_def ring_hom_def RDirProd_def
  by (auto simp add: product_ring_fields monoid.defs)

lemma product_ring_proj:
  assumes "i \<in> I" shows "(\<lambda>f. f i) \<in> ring_hom (product_ring I R) (R i)"
proof -
  have "fst \<circ> (\<lambda>f. (f i, f(i := undefined))) \<in> ring_hom (product_ring I R) (R i)"
    using product_ring_iso4[of i "I - {i}" R] assms
    by (intro ring_hom_trans[OF _ RDirProd_proj1, where ?S1 = "product_ring (I - {i}) R"])
       (auto simp add: ring_iso_def insert_absorb[OF assms])
  thus ?thesis
    by (simp add: comp_def)
qed

lemma product_ring_cartesian:
  assumes "h \<in> (\<Pi> i\<in>I. ring_hom X (R i))" shows "(\<lambda>x. \<lambda>i\<in>I. (h i) x) \<in> ring_hom X (product_ring I R)"
  using Pi_mem[OF assms] unfolding product_ring_fields ring_hom_def
  by fastforce


subsection \<open>Algebraic Structure\<close>

lemma product_group_is_monoid:
  assumes "\<And>i. i \<in> I \<Longrightarrow> monoid (G i)" shows "monoid (product_group I G)"
proof (intro monoid.intro, simp_all add: product_group_def)
  show "(\<lambda>i. \<one>\<^bsub>G i\<^esub>) \<in> (\<Pi> i\<in>I. carrier (G i))"
    using monoid.one_closed[OF assms] by simp
next
  fix x y z
  assume x: "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
     and y: "y \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
     and z: "z \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))"

  show "(\<lambda>i. x i \<otimes>\<^bsub>G i\<^esub> y i) \<in> (\<Pi> i\<in>I. carrier (G i))"
    using monoid.m_closed[OF assms[OF _] PiE_mem[OF x] PiE_mem[OF y]] by simp

  show "(\<lambda>i\<in>I. (if i \<in> I then x i \<otimes>\<^bsub>G i\<^esub> y i else undefined) \<otimes>\<^bsub>G i\<^esub> z i) =
        (\<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> (if i \<in> I then y i \<otimes>\<^bsub>G i\<^esub> z i else undefined))"
    using monoid.m_assoc[OF assms PiE_mem[OF x] PiE_mem[OF y] PiE_mem[OF z]]
    by (intro restrict_ext, simp)

  show "(\<lambda>i\<in>I. (if i \<in> I then \<one>\<^bsub>G i\<^esub> else undefined) \<otimes>\<^bsub>G i\<^esub> x i) = x"
   and "(\<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> (if i \<in> I then \<one>\<^bsub>G i\<^esub> else undefined)) = x"
    using restrict_ext[of I _ x] monoid.l_one[OF assms] monoid.r_one[OF assms] PiE_mem[OF x]
    unfolding PiE_restrict[OF x] by simp+
qed

lemma product_group_is_comm_monoid:
  assumes "\<And>i. i \<in> I \<Longrightarrow> comm_monoid (G i)" shows "comm_monoid (product_group I G)"
proof (intro comm_monoid.intro)
  show "monoid (product_group I G)"
    using product_group_is_monoid[of I G, OF comm_monoid.axioms(1)[OF assms]] .
next
  show "comm_monoid_axioms (product_group I G)"
    unfolding comm_monoid_axioms_def product_group_fields
    using restrict_ext comm_monoid.m_comm[OF assms] PiE_mem[of _ _ "\<lambda>i. carrier (G i)"] by auto
qed

lemma product_group_is_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" shows "group (product_group I G)"
proof (intro group.intro)
  show "monoid (product_group I G)"
    using product_group_is_monoid[of I G, OF group.axioms(1)[OF assms]] .
next
  show "group_axioms (product_group I G)"
  proof (auto simp add: group_axioms_def product_group_fields(1))
    fix x assume x: "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
    define x_inv where "x_inv = (\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> (x i))"
    hence "x_inv \<in> carrier (product_group I G)"
      using group.inv_closed[OF assms PiE_mem[OF x]]
      unfolding product_group_fields(1) by simp
    moreover have "x \<otimes>\<^bsub>product_group I G\<^esub> x_inv = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)"
              and "x_inv \<otimes>\<^bsub>product_group I G\<^esub> x = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)"
      using group.r_inv[OF assms] group.l_inv[OF assms] PiE_mem[OF x]
      unfolding product_group_fields(2) x_inv_def
      by (intro restrict_ext, auto)
    ultimately show "x \<in> Units (product_group I G)"
      using x unfolding Units_def product_group_fields by auto
  qed
qed

lemma product_group_is_comm_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> comm_group (G i)" shows "comm_group (product_group I G)"
  using comm_group.intro[OF product_group_is_comm_monoid product_group_is_group[of I G]]
        comm_group.axioms[OF assms]
  by simp

lemma product_ring_is_ring:
  assumes "\<And>i. i \<in> I \<Longrightarrow> ring (R i)" shows "ring (product_ring I R)"
proof (intro ring.intro)
  show "abelian_group (product_ring I R)"
    using product_group_is_comm_monoid[of I "add_monoid \<circ> R"]
          product_group_is_comm_group[of I "add_monoid \<circ> R"]
          abelian_group.axioms[OF ring.axioms(1)[OF assms]]
    unfolding abelian_group_def abelian_monoid_def
              abelian_group_axioms_def product_ring_add_monoid
    by simp
next
  have "monoid (monoid.truncate (product_ring I R))"
    using product_group_is_monoid[of I R, OF ring.axioms(2)[OF assms]]
    unfolding product_ring_truncate by simp
  thus "monoid (product_ring I R)"
    unfolding monoid_def by (auto simp add: monoid.defs)
next
  show "ring_axioms (product_ring I R)"
  proof (auto simp add: ring_axioms_def product_ring_fields(1))
    let ?S = "product_ring I R"

    fix x y z
    assume in_carrier:
      "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (R i))"
      "y \<in> (\<Pi>\<^sub>E i\<in>I. carrier (R i))"
      "z \<in> (\<Pi>\<^sub>E i\<in>I. carrier (R i))"

    show "(x \<oplus>\<^bsub>?S\<^esub> y) \<otimes>\<^bsub>?S\<^esub> z = x \<otimes>\<^bsub>?S\<^esub> z \<oplus>\<^bsub>?S\<^esub> y \<otimes>\<^bsub>?S\<^esub> z"
     and "z \<otimes>\<^bsub>?S\<^esub> (x \<oplus>\<^bsub>?S\<^esub> y) = z \<otimes>\<^bsub>?S\<^esub> x \<oplus>\<^bsub>?S\<^esub> z \<otimes>\<^bsub>?S\<^esub> y"
      using ring.ring_simprules(13, 23)[OF assms in_carrier[THEN PiE_mem]]
      unfolding product_ring_fields
      by (intro restrict_ext, auto)
  qed
qed

lemma product_ring_is_cring:
  assumes "\<And>i. i \<in> I \<Longrightarrow> cring (R i)" shows "cring (product_ring I R)"
proof (intro cring.intro)
  show "ring (product_ring I R)"
    using product_ring_is_ring[of I R, OF cring.axioms(1)[OF assms]] .
next
  have "comm_monoid (monoid.truncate (product_ring I R))"
    using product_group_is_comm_monoid[of I R, OF cring.axioms(2)[OF assms]]
    unfolding product_ring_truncate .
  thus "comm_monoid (product_ring I R)"
    unfolding comm_monoid_def comm_monoid_axioms_def monoid_def
    by (auto simp add: monoid.defs)
qed

text \<open>Remark : The following lemma can't be proven using the lemmas product_ring_iso2 and
      product_ring_is_ring, because the types of R and S are different.\<close>

lemma RDirProd_ring:
  assumes "ring R" and "ring S" shows "ring (RDirProd R S)"
proof -
  have "monoid (RDirProd R S)"
    using DirProd_monoid[OF assms[THEN ring.axioms(2)]] unfolding monoid_def
    by (auto simp add: DirProd_def RDirProd_def monoid.defs)
  then interpret Prod: group "add_monoid (RDirProd R S)" + monoid "RDirProd R S"
    using DirProd_group[OF assms[THEN abelian_group.a_group[OF ring.is_abelian_group]]]
    unfolding RDirProd_add_monoid by auto
  show ?thesis
    by (unfold_locales, auto simp add: RDirProd_def DirProd_def monoid.defs assms ring.ring_simprules)
qed

(*
  TODO :
   - Add suitable definition for the 'cartesian product' of fields (and domains), which I think
     to be the field of fractions (or the localization for domains) of the directed product.
*)

end