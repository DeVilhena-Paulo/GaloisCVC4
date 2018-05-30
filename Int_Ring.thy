theory Int_Ring
  imports "HOL-Computational_Algebra.Primes" Ring_Divisibility QuotRing

begin

section \<open>The Ring of Integers\<close>

section \<open>In this section we present another approach to the study of integers: instead of
         interpreting the set of integers (together with its common operations) as a ring,
         we study all the rings isomorphic to the integers. By doing so, we avoid problems
         with interpretation of locales and duplicate facts.\<close>

subsection \<open>Definitions\<close>

abbreviation integers :: "int ring" ("\<Z>")
  where "integers \<equiv> \<lparr> carrier = UNIV, mult = op *, one = 1, zero = 0, add = op + \<rparr>"

abbreviation prime' :: "int \<Rightarrow> bool"
  where "prime' \<equiv> Factorial_Ring.prime"

abbreviation
  elt_of_int :: "[_, int] \<Rightarrow> 'a" ("\<lbrakk> _ \<rbrakk>\<index>")
  where "elt_of_int R k \<equiv> add_pow R k \<one>\<^bsub>R\<^esub>"

definition
  some_int :: "[_, 'a] \<Rightarrow> int" ("int'_repr\<index> _" [81] 80)
  where "int_repr\<^bsub>R\<^esub> a = (SOME n. a = \<lbrakk> n \<rbrakk>\<^bsub>R\<^esub>)"

definition \<comment>\<open>The characteristic of a ring.\<close>
  char :: "_ \<Rightarrow> nat"
  where "char R = card ((\<lambda>n. \<lbrakk> n \<rbrakk>\<^bsub>R\<^esub>) ` UNIV)"

locale int_mod = ring +
  assumes exists_int_repr: "a \<in> carrier R \<Longrightarrow> \<exists>n. a = \<lbrakk> n \<rbrakk>"

locale int_ring = int_mod +
  assumes unique_int_repr: "\<lbrakk> n \<rbrakk> = \<lbrakk> m \<rbrakk> \<Longrightarrow> n = m"


subsection \<open>Basic Properties\<close>

text \<open>Some of these properties would be also true for structures simpler than rings, but
      we chose to work only with rings for convenience. \<close>

lemma (in ring) elt_of_int_in_carrier [intro]: "\<lbrakk> n \<rbrakk> \<in> carrier R"
  by simp

lemma (in ring) elt_of_one_or_zero [simp]: "\<lbrakk> 1 \<rbrakk> = \<one>" "\<lbrakk> 0 \<rbrakk> = \<zero>"
  by auto

lemma (in ring) elt_of_int_add: "\<lbrakk> n \<rbrakk> \<oplus> \<lbrakk> m \<rbrakk> = \<lbrakk> n + m \<rbrakk>"
  using add.int_pow_mult by simp

lemma (in ring) elt_of_int_inv: "\<ominus> \<lbrakk> n \<rbrakk> = \<lbrakk> - n \<rbrakk>"
  using add.int_pow_def2 by simp

lemma (in ring) elt_of_int_def':
  assumes "a \<in> carrier R"
  shows "[ n ] \<cdot> a = \<lbrakk> n \<rbrakk> \<otimes> a"
proof -
  have aux_lemma: "\<And>k :: nat. [ k ] \<cdot> a = \<lbrakk> int k \<rbrakk> \<otimes> a"
  proof -
    fix k show "[ k ] \<cdot> a = \<lbrakk> int k \<rbrakk> \<otimes> a"
    proof (induction k)
      case 0 thus ?case by (simp add: assms) 
    next
      case (Suc k) thus ?case
        using add.int_pow_def2 add_pow_ldistr assms l_one nat_int one_closed by presburger 
    qed
  qed

  show ?thesis
  proof (cases "n \<ge> 0")
    case True thus ?thesis
      using aux_lemma[of "nat n"] add_pow_int_ge[OF True, of R a] by simp
  next
    case False thus ?thesis
      using aux_lemma[of "nat (- n)"] add_pow_int_lt[of n R a]
      by (simp add: add_pow_ldistr_int assms)
  qed
qed

lemma (in ring) elt_of_int_mult: "\<lbrakk> n \<rbrakk> \<otimes> \<lbrakk> m \<rbrakk> = \<lbrakk> n * m \<rbrakk>"
proof -
  have "\<lbrakk> n \<rbrakk> \<otimes> \<lbrakk> m \<rbrakk> = [ n ] \<cdot> ([ m ] \<cdot> \<one>)"
    using elt_of_int_def'[of "\<lbrakk> m \<rbrakk>" n] by simp
  also have " ... = \<lbrakk> n * m \<rbrakk>"
    using add.int_pow_pow[OF one_closed, of n m] by (simp add: mult.commute)
  finally show ?thesis.
qed

lemma (in ring) elt_of_int_pow:
  "\<lbrakk> n \<rbrakk> (^) (k :: nat) = \<lbrakk> n ^ k \<rbrakk>"
  "\<lbrakk> n \<rbrakk> (^) (k :: int) = (if k < 0 then \<lbrakk> - (n ^ (nat k)) \<rbrakk> else \<lbrakk> n ^ (nat k) \<rbrakk>)"
proof -
  have aux_lemma: "\<And>k. \<lbrakk> n \<rbrakk> (^) k = \<lbrakk> n ^ k \<rbrakk>"
  proof -
    fix k show "\<lbrakk> n \<rbrakk> (^) k = \<lbrakk> n ^ k \<rbrakk>"
      by (induction k) (auto simp add: elt_of_int_mult mult.commute)
  qed

  show "\<lbrakk> n \<rbrakk> (^) k = \<lbrakk> n ^ k \<rbrakk>"
    using aux_lemma by simp
  show "\<lbrakk> n \<rbrakk> (^) (k :: int) = (if k < 0 then \<lbrakk> - (n ^ (nat k)) \<rbrakk> else \<lbrakk> n ^ (nat k) \<rbrakk>)"
    using aux_lemma elt_of_int_inv add.int_pow_def2 by (simp add: int_pow_int)
qed

lemma (in ring) elt_of_int_consistent:
  assumes "S \<subseteq> carrier R" "ring (R \<lparr> carrier := S \<rparr>)"
  shows "\<lbrakk> n \<rbrakk> = \<lbrakk> n \<rbrakk>\<^bsub>(R \<lparr> carrier := S \<rparr>)\<^esub>"
proof -
  have "subgroup S (add_monoid R)"
    using add.group_incl_imp_subgroup[OF assms(1)] assms(2)
    unfolding ring_def abelian_group_def abelian_group_axioms_def comm_group_def by auto
  moreover have "\<one> \<in> carrier (R \<lparr> carrier := S \<rparr>)"
    using assms(2) monoid.one_closed[of "R \<lparr> carrier := S \<rparr>"] unfolding ring_def by simp
  ultimately show ?thesis
    using add.int_pow_consistent[of S \<one> n] unfolding add_pow_def by simp
qed

lemma ring_of_integers: "ring \<Z>"
  apply unfold_locales
  apply (auto simp add: Units_def distrib_left mult.commute)
  apply presburger
  done

lemma elt_of_integer: "\<lbrakk> n \<rbrakk>\<^bsub>\<Z>\<^esub> = n"
proof -
  interpret ring "\<Z>"
    using ring_of_integers by simp

  have aux_lemma1: "\<And>k :: nat. \<lbrakk> int k \<rbrakk>\<^bsub>\<Z>\<^esub> = int k"
  proof -
    fix k show "\<lbrakk> int k \<rbrakk>\<^bsub>\<Z>\<^esub> = int k"
    proof (induction k)
      case 0 thus ?case by simp
    next
     case (Suc k) thus ?case
        using elt_of_int_add[of 1 "int k"] by auto
    qed
  qed

  have "\<And>k :: nat. \<lbrakk> - int k \<rbrakk>\<^bsub>\<Z>\<^esub> = \<ominus>\<^bsub>\<Z>\<^esub> \<lbrakk> int k \<rbrakk>\<^bsub>\<Z>\<^esub>"
    using add.int_pow_def2 add.int_pow_neg by blast

  moreover have "\<And>n. n \<oplus>\<^bsub>\<Z>\<^esub> (- n) = \<zero>\<^bsub>\<Z>\<^esub>" by simp
  hence "\<And>n. \<ominus>\<^bsub>\<Z>\<^esub> n = - n"
    by (simp add: minus_equality)

  ultimately
  have aux_lemma2: "\<And>k :: nat. \<lbrakk> - int k \<rbrakk>\<^bsub>\<Z>\<^esub> = - int k"
    using aux_lemma1 by simp

  have "n = nat n \<or> n = - int (nat (-n))" by simp
  thus ?thesis
    using aux_lemma1[of "nat n"] aux_lemma2[of "nat (-n)"] by auto
qed

corollary integer_repr: "int_repr\<^bsub>\<Z>\<^esub> n = n"
  using elt_of_integer unfolding some_int_def by simp

corollary int_ring_of_integers: "int_ring \<Z>"
proof -
  have "\<And>i. i \<in> carrier \<Z> \<Longrightarrow> \<exists>n. i = \<lbrakk> n \<rbrakk>\<^bsub>\<Z>\<^esub>"
       "\<And>n m. \<lbrakk> n \<rbrakk>\<^bsub>\<Z>\<^esub> = \<lbrakk> m \<rbrakk>\<^bsub>\<Z>\<^esub> \<Longrightarrow> n = m"
    using elt_of_integer by auto
  thus ?thesis
    using ring_of_integers int_mod_axioms_def int_mod_def
          int_ring_axioms_def int_ring_def by metis
qed


subsection \<open>Int_Mod\<close>

sublocale int_mod \<subseteq> ring ..

lemma (in int_mod) elt_of_int_surj: "carrier R = (\<lambda>n. \<lbrakk> n \<rbrakk>) ` UNIV"
  using exists_int_repr by blast

lemma (in int_mod) char_eq_card: "char R = card (carrier R)"
  using elt_of_int_surj unfolding char_def by simp

lemma (in int_mod) int_repr_wf: "a \<in> carrier R \<Longrightarrow> a = \<lbrakk> int_repr a \<rbrakk>"
  using exists_int_repr[of a] unfolding some_int_def by (smt someI)

lemma (in int_mod) int_repr_inj:
  "\<lbrakk> r1 \<in> carrier R; r2 \<in> carrier R \<rbrakk> \<Longrightarrow> int_repr r1 = int_repr r2 \<Longrightarrow> r1 = r2"
  using int_repr_wf by metis

lemma (in int_mod) m_comm:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<otimes> b = b \<otimes> a"
  using int_repr_wf[OF assms(1)] int_repr_wf[OF assms(2)]
  by (metis add_pow_rdistr_int assms(1) elt_of_int_def' one_closed)

sublocale int_mod \<subseteq> cring
  unfolding cring_def comm_monoid_def comm_monoid_axioms_def
  using is_ring m_comm monoid_axioms by auto


subsection \<open>Int_Ring\<close>

sublocale int_ring \<subseteq> int_mod ..

lemma (in int_ring) elt_of_int_bij: "bij_betw (\<lambda>n. \<lbrakk> n \<rbrakk>) (UNIV :: int set) (carrier R)"
  using unique_int_repr elt_of_int_surj unfolding bij_betw_def inj_def by simp

lemma (in int_ring) elt_of_int_inj: "int_repr \<lbrakk> n \<rbrakk> = n"
  using int_repr_wf unique_int_repr by auto

lemma (in int_ring) char_eq_zero: "char R = 0"
  using bij_betw_same_card[OF elt_of_int_bij] char_eq_card infinite_UNIV_int by auto

lemma (in int_ring) int_repr_bij: "bij_betw (\<lambda>r. int_repr r) (carrier R) (UNIV :: int set)"
  using int_repr_inj elt_of_int_inj UNIV_eq_I elt_of_int_surj imageI rangeI
  unfolding bij_betw_def inj_on_def by metis

sublocale int_ring \<subseteq> domain
proof
  have "\<lbrakk> (1 :: int) \<rbrakk> = \<lbrakk> (0 :: int) \<rbrakk> \<Longrightarrow> 1 = 0"
    using unique_int_repr[of 1 0] by simp 
  thus "\<one> \<noteq> \<zero>" by (smt elt_of_one_or_zero)
next
  fix a b assume a: "a \<in> carrier R" and b: "b \<in> carrier R" and ab: "a \<otimes> b = \<zero>"
  hence "\<lbrakk> int_repr a * int_repr b \<rbrakk> = \<lbrakk> (0 :: int) \<rbrakk>"
    by (metis elt_of_int_mult elt_of_one_or_zero(2) int_repr_wf)
  hence "int_repr a * int_repr b = 0"
    using unique_int_repr[of "int_repr a * int_repr b" 0] by simp
  hence "int_repr a = 0 \<or> int_repr b = 0"
    by simp
  thus "a = \<zero> \<or> b = \<zero>"
    using a b int_repr_wf by force
qed

sublocale int_ring \<subseteq> euclidean_domain R "\<lambda>a. nat \<bar> int_repr a \<bar>"
proof (rule domain.euclidean_domainI[OF is_domain])
  let ?norm = "\<lambda>a. nat \<bar> int_repr a \<bar>"
  fix a b assume a: "a \<in> carrier R - { \<zero> }" and b: "b \<in> carrier R - { \<zero> }"
  define q_int and r_int
    where "q_int = (int_repr a) div (int_repr b)"
      and "r_int = (int_repr a) mod (int_repr b)"
  hence "(int_repr a) = (int_repr b) * q_int + r_int"
    by simp
  hence "\<lbrakk> int_repr a \<rbrakk> = \<lbrakk> int_repr b \<rbrakk> \<otimes> \<lbrakk> q_int \<rbrakk> \<oplus> \<lbrakk> r_int \<rbrakk>"
    by (simp add: elt_of_int_add elt_of_int_mult)
  hence "a = b \<otimes> \<lbrakk> q_int \<rbrakk> \<oplus> \<lbrakk> r_int \<rbrakk>"
    using int_repr_wf[of a] int_repr_wf[of b] a b by auto
  moreover have "?norm b \<noteq> 0"
    using b int_repr_wf[of b] by auto
  hence "nat \<bar>r_int\<bar> < ?norm b"
    using abs_mod_less r_int_def by auto
  ultimately
  show "\<exists>q r. q \<in> carrier R \<and> r \<in> carrier R \<and> a = b \<otimes> q \<oplus> r \<and> (r = \<zero> \<or> ?norm r < ?norm b)"
    by (metis elt_of_int_in_carrier elt_of_int_inj)
qed

sublocale int_ring \<subseteq> principal_domain ..

lemma (in int_ring) is_principal_domain: "principal_domain R" ..


subsection \<open>Ideals of Int_Rings\<close>

lemma (in int_ring) int_ring_Units: "Units R = { \<lbrakk> -1 \<rbrakk>, \<lbrakk> 1 \<rbrakk> }"
proof
  have "\<lbrakk> -1 \<rbrakk> \<otimes> \<lbrakk> -1 \<rbrakk> = \<one>" "\<lbrakk> 1 \<rbrakk> \<otimes> \<lbrakk> 1 \<rbrakk> = \<one>"
    using elt_of_one_or_zero(1) elt_of_int_mult by auto
  thus "{ \<lbrakk> -1 \<rbrakk>, \<lbrakk> 1 \<rbrakk> } \<subseteq> Units R"
    unfolding Units_def by auto
next
  show "Units R \<subseteq> { \<lbrakk> -1 \<rbrakk>, \<lbrakk> 1 \<rbrakk> }"
  proof
    fix u assume u: "u \<in> Units R"
    then obtain u' where u': "u' \<in> carrier R" "u \<otimes> u' = \<one>"
      unfolding Units_def by blast
    hence "(int_repr u) * (int_repr u') = 1"
      using elt_of_one_or_zero(1) elt_of_int_mult[of "int_repr u" "int_repr u'"]
            u int_repr_wf int_mod_axioms unique_int_repr by fastforce
    hence "int_repr u = -1 \<or> int_repr u = 1"
      using zmult_eq_1_iff by blast
    hence "u = \<lbrakk> -1 \<rbrakk> \<or> u = \<lbrakk> 1 \<rbrakk>"
      using int_repr_wf[of u] u unfolding Units_def by auto
    thus "u \<in> { \<lbrakk> -1 \<rbrakk>, \<lbrakk> 1 \<rbrakk> }"
      by simp
  qed
qed

lemma (in int_ring) divides_iff_dvd:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "(a divides b) = ((int_repr a) dvd (int_repr b))"
  unfolding factor_def dvd_def
  using assms int_repr_wf add.int_pow_closed one_closed
        elt_of_int_mult elt_of_int_inj elt_of_int_mult
  by metis

lemma (in int_ring) prime_iff_prime':
  assumes "p \<in> carrier R - { \<zero> }"
  shows "prime (mult_of R) p = prime' \<bar> int_repr p \<bar>"
proof
  assume A: "prime (mult_of R) p" show "prime' \<bar> int_repr p \<bar>"
    unfolding Factorial_Ring.prime_def prime_elem_def normalize_def
  proof (auto)
    show "int_repr p = 0 \<Longrightarrow> False"
      using assms int_repr_wf by fastforce
  next
    assume "\<bar> int_repr p \<bar> = 1"
    hence "int_repr p = 1 \<or> int_repr p = -1"
      by linarith
    hence "p \<in> Units R"
      using int_ring_Units int_repr_wf[of p] assms by force
    thus False
      using A Units_mult_eq_Units unfolding prime_def by simp
  next
    fix a b
    assume "(int_repr p) dvd (a * b)" "\<not> (int_repr p) dvd b"
    hence div_ab: "p divides \<lbrakk> a * b \<rbrakk>" and not_div_b: "\<not> p divides \<lbrakk> b \<rbrakk>"
      using elt_of_int_inj[of "a * b"] divides_iff_dvd[of p "\<lbrakk> a * b \<rbrakk>"] assms
            elt_of_int_inj[of "b"] divides_iff_dvd[of p "\<lbrakk> b \<rbrakk>"] by auto
    show "int_repr p dvd a"
    proof (cases)
      assume "a = 0" thus ?thesis by simp
    next
      assume a_not_zero: "a \<noteq> 0" hence "a * b \<noteq> 0"
        using \<open>\<not> (int_repr p) dvd b\<close> by auto
      hence "\<lbrakk> a * b \<rbrakk> \<noteq> \<zero>"
        using elt_of_one_or_zero(2) unique_int_repr by metis
      hence "\<lbrakk> a * b \<rbrakk> \<in> carrier R - { \<zero> }"
        by simp
      hence "p divides\<^bsub>(mult_of R)\<^esub> \<lbrakk> a * b \<rbrakk>"
        using divides_imp_divides_mult[of p "\<lbrakk> a * b \<rbrakk>"] div_ab assms by blast
      hence "p divides\<^bsub>(mult_of R)\<^esub> \<lbrakk> a \<rbrakk> \<otimes> \<lbrakk> b \<rbrakk>"
        using elt_of_int_mult[of a b] by simp
      moreover have "\<not> p divides\<^bsub>(mult_of R)\<^esub> \<lbrakk> b \<rbrakk>"
        using not_div_b divides_mult_imp_divides[of R p "\<lbrakk> b \<rbrakk>"] by auto
      moreover have "\<lbrakk> a \<rbrakk> \<noteq> \<zero>"
        using a_not_zero elt_of_one_or_zero(2) unique_int_repr by metis
      hence "\<lbrakk> a \<rbrakk> \<in> carrier (mult_of R)"
        by auto
      moreover have "b \<noteq> 0"
        using \<open>\<not> (int_repr p) dvd b\<close> by auto
      hence "\<lbrakk> b \<rbrakk> \<noteq> \<zero>"
        using elt_of_one_or_zero(2) unique_int_repr by auto
      hence "\<lbrakk> b \<rbrakk> \<in> carrier (mult_of R)"
        by auto
      ultimately have "p divides\<^bsub>(mult_of R)\<^esub> \<lbrakk> a \<rbrakk>"
        using A mult_of.prime_divides by metis
      thus ?thesis
        using divides_mult_imp_divides divides_iff_dvd[of p "\<lbrakk> a \<rbrakk>"] elt_of_int_inj[of a] assms by simp
    qed
  qed
next
  assume A: "prime' \<bar> int_repr p \<bar>" show "prime (mult_of R) p"
  proof (rule primeI)
    from A have "int_repr p \<noteq> 1 \<and> int_repr p \<noteq> -1"
      by auto
    hence "p \<notin> Units R"
      using int_ring_Units int_repr_wf[of p] unique_int_repr by auto
    thus "p \<notin> Units (mult_of R)"
      using Units_mult_eq_Units by simp
  next
    { fix c assume c: "c \<in> carrier (mult_of R)" "\<bar> int_repr p \<bar> dvd (int_repr c)"
      hence "(int_repr p) dvd (int_repr c)"
        by simp
      hence "p divides c"
        using divides_iff_dvd[of p c] c(1) assms by (metis DiffD1 carrier_mult_of)
      hence "p divides\<^bsub>mult_of R\<^esub> c"
        using divides_imp_divides_mult[of p c] c(1) assms by (metis DiffD1 carrier_mult_of) }
    note aux_lemma = this

    fix a b
    assume a: "a \<in> carrier (mult_of R)"
       and b: "b \<in> carrier (mult_of R)"
       and "p divides\<^bsub>mult_of R\<^esub> a \<otimes>\<^bsub>mult_of R\<^esub> b"
    hence "(int_repr p) dvd (int_repr (a \<otimes> b))" 
      using divides_iff_dvd[of p "a \<otimes> b"] divides_mult_imp_divides[of R p "a \<otimes> b"] assms by auto
    hence "\<bar> int_repr p \<bar> dvd ((int_repr a) * (int_repr b))"
      using elt_of_int_mult[of "int_repr a" "int_repr b"] elt_of_int_inj int_repr_wf a b by auto
    hence "\<bar> int_repr p \<bar> dvd (int_repr a) \<or>  \<bar> int_repr p \<bar> dvd (int_repr b)"
      using prime_dvd_multD[OF A] by simp
    thus "p divides\<^bsub>mult_of R\<^esub> a \<or> p divides\<^bsub>mult_of R\<^esub> b"
      using aux_lemma a b by auto
  qed
qed

lemma (in int_ring) associated_iff_same_abs:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<sim> b = (\<bar> int_repr a \<bar> = \<bar> int_repr b \<bar>)"
proof
  assume "a \<sim> b"
  then obtain u v
    where u: "u \<in> carrier R" "a = b \<otimes> u"
      and v: "v \<in> carrier R" "b = a \<otimes> v"
    unfolding associated_def factor_def by blast
  hence "b = (b \<otimes> u) \<otimes> v"
    by simp
  hence "(int_repr b) = (int_repr b) * (int_repr u) * (int_repr v)"
    using assms u(1) v(1) elt_of_int_inj elt_of_int_mult int_repr_wf by metis
  hence "(int_repr b) = 0 \<or> (int_repr u) * (int_repr v) = 1"
    by auto
  thus "\<bar> int_repr a \<bar> = \<bar> int_repr b \<bar>"
  proof
    have eq: "(int_repr a) = (int_repr b) * (int_repr u)"
      using assms u elt_of_int_inj elt_of_int_mult int_repr_wf by metis
    assume "int_repr b = 0" thus ?thesis
      using eq by simp
  next
    have eq: "\<bar> int_repr a \<bar> = \<bar> (int_repr b) * (int_repr u) \<bar>"
      using assms u elt_of_int_inj elt_of_int_mult int_repr_wf by metis
    assume "int_repr u * int_repr v = 1"
    hence "\<bar> int_repr u \<bar> = 1"
      using zmult_eq_1_iff by auto
    thus ?thesis
      using eq by (simp add: abs_mult)
  qed
next
  assume "\<bar>int_repr a\<bar> = \<bar>int_repr b\<bar>"
  hence "(int_repr a) = (int_repr b) \<or> (int_repr a) = (int_repr b) * (-1)"
    by linarith
  thus "a \<sim> b"
  proof
    assume "(int_repr a) = (int_repr b)"
    hence "a = b"
      using int_repr_wf[OF assms(1)] int_repr_wf[OF assms(2)] by simp
    thus ?thesis
      using assms(1) by blast
  next
    assume "(int_repr a) = (int_repr b) * (-1)"
    hence "a = b \<otimes> \<lbrakk> -1 \<rbrakk> \<and> b = a \<otimes> \<lbrakk> -1 \<rbrakk>"
      using int_repr_wf[OF assms(1)] int_repr_wf[OF assms(2)]
      by (metis add.inverse_inverse elt_of_int_mult mult_minus1_right)
    thus ?thesis
      unfolding associated_def factor_def by blast
  qed
qed

lemma (in int_ring) ideal_int_repr: "ideal I R \<Longrightarrow> \<exists>n. I = PIdl \<lbrakk> n \<rbrakk>"
  using principal_I[of I] int_repr_wf cgenideal_eq_genideal principalideal.generate[of I R] by metis

lemma (in int_ring) ideal_pos_int_repr:
  assumes "ideal I R"
  shows "\<exists>!n. n \<ge> 0 \<and> I = PIdl \<lbrakk> n \<rbrakk>"
proof -
  have "\<And>i j. \<lbrakk> PIdl \<lbrakk> i \<rbrakk> = PIdl \<lbrakk> j \<rbrakk>; i \<ge> 0; j \<ge> 0 \<rbrakk> \<Longrightarrow> i = j"
  proof -
    fix i j assume A: "PIdl \<lbrakk> i \<rbrakk> = PIdl \<lbrakk> j \<rbrakk>" "i \<ge> 0" "j \<ge> 0"
    hence "\<lbrakk> i \<rbrakk> \<sim> \<lbrakk> j \<rbrakk>"
      using associated_iff_same_ideal by simp
    thus "i = j"
      using associated_iff_same_abs[of "\<lbrakk> i \<rbrakk>" "\<lbrakk> j \<rbrakk>"] A(2-3) by (simp add: elt_of_int_inj)
  qed

  moreover have "\<exists>n. n \<ge> 0 \<and> I = PIdl \<lbrakk> n \<rbrakk>"
  proof -
    obtain n where "I = PIdl \<lbrakk> n \<rbrakk>"
      using ideal_int_repr[OF assms] by blast
    hence "I = PIdl \<lbrakk> \<bar> n \<bar> \<rbrakk>"
      using associated_iff_same_ideal associated_iff_same_abs[of "\<lbrakk> n \<rbrakk>" "\<lbrakk> \<bar> n \<bar> \<rbrakk>"]
      by (simp add: elt_of_int_inj)
    thus ?thesis
      using abs_ge_zero by blast
  qed

  ultimately show ?thesis
    by blast
qed

lemma (in int_ring) in_ideal_iff:
  assumes "a \<in> carrier R"
  shows "(a \<in> PIdl \<lbrakk> n \<rbrakk>) = (n dvd (int_repr a))"
proof -
  have "(a \<in> PIdl \<lbrakk> n \<rbrakk>) = (\<lbrakk> n \<rbrakk> divides a)"
    using assms to_contain_is_to_divide[of "\<lbrakk> n \<rbrakk>" a] cgenideal_self[OF assms]
          cgenideal_ideal cgenideal_minimal by blast
  thus ?thesis
    using divides_iff_dvd[of "\<lbrakk> n \<rbrakk>" a] assms elt_of_int_inj by simp
qed

corollary (in int_ring) int_ideal:
  "PIdl \<lbrakk> n \<rbrakk> = { \<lbrakk> (n * k) \<rbrakk> | k. k \<in> UNIV }"
proof
  show "PIdl \<lbrakk> n \<rbrakk> \<subseteq> { \<lbrakk> n * k \<rbrakk> | k. k \<in> UNIV }"
  proof 
    fix a assume a: "a \<in> PIdl \<lbrakk> n \<rbrakk>"
    hence "n dvd (int_repr a)"
      using in_ideal_iff[of a n] cgenideal_minimal oneideal by blast
    hence "\<exists>k. int_repr a = n * k"
      unfolding dvd_def by blast
    thus "a \<in> { \<lbrakk> (n * k) \<rbrakk> | k. k \<in> UNIV }"
      using int_repr_wf[of a] a cgenideal_ideal[of "\<lbrakk> n \<rbrakk>"]  ideal.Icarr[of "PIdl \<lbrakk> n \<rbrakk>" R a] by auto
  qed
next
  show "{ \<lbrakk> n * k \<rbrakk> | k. k \<in> UNIV } \<subseteq> PIdl \<lbrakk> n \<rbrakk>"
  proof
    fix a assume "a \<in> { \<lbrakk> n * k \<rbrakk> | k. k \<in> UNIV }"
    then obtain k where "a = \<lbrakk> n * k \<rbrakk>" by auto
    thus "a \<in>  PIdl \<lbrakk> n \<rbrakk>"
      using in_ideal_iff[of a n] elt_of_int_inj[of "n * k"] by auto
  qed
qed

corollary (in int_ring) int_ideal':
  assumes "a \<in> carrier R"
  shows "PIdl a = { \<lbrakk> ((int_repr a) * k) \<rbrakk> | k. k \<in> UNIV }"
  using int_repr_wf[OF assms] int_ideal[of "int_repr a"] by auto

corollary (in int_ring) int_rcoset:
  "PIdl \<lbrakk> n \<rbrakk> +> \<lbrakk> i \<rbrakk> = { \<lbrakk> (n * k) + i \<rbrakk> | k. k \<in> UNIV }"
proof
  show "PIdl \<lbrakk> n \<rbrakk> +> \<lbrakk> i \<rbrakk> \<subseteq> { \<lbrakk> n * k + i \<rbrakk> | k. k \<in> UNIV }"
  proof
    fix a assume "a \<in> PIdl \<lbrakk> n \<rbrakk> +> \<lbrakk> i \<rbrakk>"
    then obtain k where "a = \<lbrakk> n * k \<rbrakk> \<oplus> \<lbrakk> i \<rbrakk>"
      using a_r_coset_def'[of R "PIdl \<lbrakk> n \<rbrakk>" "\<lbrakk> i \<rbrakk>"] int_ideal[of n] by auto
    thus "a \<in> { \<lbrakk> n * k + i \<rbrakk> | k. k \<in> UNIV }"
      using elt_of_int_add[of "n * k" i] by auto
  qed
next
  show "{ \<lbrakk> n * k + i \<rbrakk> | k. k \<in> UNIV } \<subseteq> PIdl \<lbrakk> n \<rbrakk> +> \<lbrakk> i \<rbrakk>"
  proof
    fix a assume "a \<in> { \<lbrakk> n * k + i \<rbrakk> | k. k \<in> UNIV }"
    then obtain k where "a = \<lbrakk> n * k \<rbrakk> \<oplus> \<lbrakk> i \<rbrakk>"
      using elt_of_int_add by auto
    thus "a \<in> PIdl \<lbrakk> n \<rbrakk> +> \<lbrakk> i \<rbrakk>"
      using a_r_coset_def'[of R "PIdl \<lbrakk> n \<rbrakk>" "\<lbrakk> i \<rbrakk>"] int_ideal[of n] by auto
  qed
qed

corollary (in int_ring) int_rcoset':
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "PIdl a +> b = { \<lbrakk> ((int_repr a) * k) + (int_repr b) \<rbrakk> | k. k \<in> UNIV }"
  using int_repr_wf[OF assms(1)] int_repr_wf[OF assms(2)]
        int_rcoset[of "int_repr a" "int_repr b"] by auto

corollary (in int_ring) rcoset_eq:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "(PIdl a +> b = PIdl a +> c) = ((int_repr a) dvd ((int_repr b) - (int_repr c)))"
proof 
  assume "PIdl a +> b = PIdl a +> c"
  hence "a \<oplus> b \<in> PIdl a +> c"
    using cgenideal_self[OF assms(1)]  unfolding a_r_coset_def' by auto
  then obtain k where "a \<oplus> b = \<lbrakk> ((int_repr a) * k) + (int_repr c) \<rbrakk>"
    using int_rcoset'[OF assms(1) assms(3)] by auto
  hence "(int_repr a) + (int_repr b) = ((int_repr a) * k) + (int_repr c)"
    by (metis assms(1) assms(2) elt_of_int_add elt_of_int_inj int_repr_wf)
  hence "(int_repr b) - (int_repr c) = (int_repr a) * (k - 1)"
    by (simp add: algebra_simps)
  thus "(int_repr a) dvd ((int_repr b) - (int_repr c))"
    by simp
next
  assume "int_repr a dvd int_repr b - int_repr c"
  then obtain k' where "int_repr b - int_repr c = int_repr a * k'"
    using dvd_def by blast
  hence "int_repr b = int_repr a * k' + int_repr c"
    by (simp add: algebra_simps)
  hence "PIdl a +> b = { \<lbrakk> (int_repr a * k) + (int_repr a * k' + int_repr c) \<rbrakk> | k. k \<in> UNIV }"
    using int_rcoset'[OF assms(1-2)] by simp
  also have " ... = { \<lbrakk> int_repr a * (k +  k') + int_repr c \<rbrakk> | k. k \<in> UNIV }"
    by (simp add: algebra_simps)
  also have " ... = { \<lbrakk> int_repr a * k + int_repr c \<rbrakk> | k. k \<in> UNIV }"
    by (metis (no_types, hide_lams) UNIV_I diff_add_cancel)
  finally show "PIdl a +> b = PIdl a +> c"
    using int_rcoset'[OF assms(1) assms(3)] by simp
qed



subsection \<open>Homomorphisms\<close>

lemma (in int_ring) exists_hom:
  assumes "ring S"
  shows "(\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>) \<in> ring_hom R S"
proof (rule ring_hom_memI)
  show "\<And>x. x \<in> carrier R \<Longrightarrow> \<lbrakk> int_repr x \<rbrakk>\<^bsub>S\<^esub> \<in> carrier S"
    using ring.elt_of_int_in_carrier[OF assms] by simp
  show "\<lbrakk> int_repr \<one> \<rbrakk>\<^bsub>S\<^esub> = \<one>\<^bsub>S\<^esub>"
    using ring.elt_of_one_or_zero(1)[OF assms] elt_of_int_inj elt_of_one_or_zero(1) by metis
next
  fix x y assume x: "x \<in> carrier R" and y: "y \<in> carrier R"
  show "\<lbrakk> int_repr (x \<otimes> y) \<rbrakk>\<^bsub>S\<^esub> = \<lbrakk> int_repr x \<rbrakk>\<^bsub>S\<^esub> \<otimes>\<^bsub>S\<^esub> \<lbrakk> int_repr y \<rbrakk>\<^bsub>S\<^esub>"
    using elt_of_int_mult ring.elt_of_int_mult[OF assms] int_repr_wf elt_of_int_inj x y by metis

  show "\<lbrakk> int_repr (x \<oplus> y) \<rbrakk>\<^bsub>S\<^esub> = \<lbrakk> int_repr x \<rbrakk>\<^bsub>S\<^esub> \<oplus>\<^bsub>S\<^esub> \<lbrakk> int_repr y \<rbrakk>\<^bsub>S\<^esub>"
    using elt_of_int_add ring.elt_of_int_add[OF assms] int_repr_wf elt_of_int_inj x y by metis
qed

lemma (in int_ring) unique_hom:
  assumes "h \<in> ring_hom R S" "ring S"
  shows "restrict h (carrier R) = restrict (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>) (carrier R)"
proof -
  have "\<And>i. i \<in> carrier R \<Longrightarrow> h i = \<lbrakk> int_repr i \<rbrakk>\<^bsub>S\<^esub>"
  proof -
    interpret rhom: ring_hom_ring R S h
      using assms(1) ring_hom_ringI[OF is_ring assms(2), of h] unfolding ring_hom_def by auto

    fix i assume "i \<in> carrier R"
    hence "h i = h \<lbrakk> int_repr i \<rbrakk>"
      using int_repr_wf by auto
    also have " ... =  [(int_repr i)] \<cdot>\<^bsub>S\<^esub> (h \<one>)"
      unfolding add_pow_def
      using group_hom.int_pow_hom[OF rhom.a_group_hom, of \<one> "int_repr i"] one_closed by simp
    also have " ... = \<lbrakk> int_repr i \<rbrakk>\<^bsub>S\<^esub>"
      using ring_hom_one[OF assms(1)] by simp
    finally show "h i = \<lbrakk> int_repr i \<rbrakk>\<^bsub>S\<^esub>" .
  qed

  thus ?thesis
    using restrict_cong[of "carrier R" "carrier R" h "\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>"] by auto
qed

lemma (in int_ring) char_hom_surj: "(\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>) ` (carrier R) =  (\<lambda>i. \<lbrakk> i \<rbrakk>\<^bsub>S\<^esub>) ` (UNIV)"
proof -
  have "(\<lambda>i. \<lbrakk> i \<rbrakk>\<^bsub>S\<^esub>) ` (UNIV) = (\<lambda>i. \<lbrakk> i \<rbrakk>\<^bsub>S\<^esub>) ` ((\<lambda>r. int_repr r) ` (carrier R))"
    using int_repr_bij unfolding bij_betw_def by simp
  also have " ... = (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>) ` (carrier R)"
    using image_comp by auto
  finally have "(\<lambda>i. \<lbrakk> i \<rbrakk>\<^bsub>S\<^esub>) ` (UNIV) = (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>) ` (carrier R)" .
  thus ?thesis by simp
qed

lemma (in int_ring) surj_hom_imp_int_mod:
  assumes "h \<in> ring_hom R S" "ring S"
    and "h ` (carrier R) = (carrier S)"
  shows "int_mod S"
proof -
  have restrict_eq: "\<And>r. r \<in> carrier R \<Longrightarrow> h r = \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>"
    using unique_hom[OF assms(1-2)] unfolding restrict_def by metis

  have "\<And>s. s \<in> carrier S \<Longrightarrow> \<exists>n. s = \<lbrakk> n \<rbrakk>\<^bsub>S\<^esub>"
  proof -
    fix s assume "s \<in> carrier S"
    then obtain r where r: "r \<in> carrier R" "h r = s"
      using assms(3) image_iff[of s h "carrier R"] by auto
    thus "\<exists>n. s = \<lbrakk> n \<rbrakk>\<^bsub>S\<^esub>"
      using restrict_eq[OF r(1)] by blast
  qed
  thus ?thesis
    unfolding int_mod_def int_mod_axioms_def using assms(2) by auto
qed

corollary (in int_ring) hom_imp_img_int_mod:
  assumes "h \<in> ring_hom R S" "ring S"
  shows "int_mod (S \<lparr> carrier := h ` (carrier R) \<rparr>)"
proof -
  interpret Hom?: ring_hom_ring R S h
    using assms is_ring unfolding ring_hom_ring_def ring_hom_ring_axioms_def by auto
  have "h \<in> ring_hom R (S \<lparr> carrier := h ` (carrier R) \<rparr>)"
    using assms(1) unfolding ring_hom_def by auto
  thus ?thesis
    using surj_hom_imp_int_mod[of h "S \<lparr> carrier := h ` (carrier R) \<rparr>"] Hom.img_is_ring by auto
qed

corollary (in ring) int_subring: "int_mod (R \<lparr> carrier := (\<lambda>i. \<lbrakk> i \<rbrakk>) ` (UNIV) \<rparr>)"
proof -
  note ring_R = is_ring
  interpret Z?: int_ring \<Z>
    using int_ring_of_integers .
  show ?thesis
    using Z.hom_imp_img_int_mod[OF Z.exists_hom[OF ring_R] ring_R] integer_repr by simp
qed

lemma (in int_ring) iso_imp_int_ring:
  assumes "ring S"
  shows "R \<simeq> S \<Longrightarrow> int_ring S"
proof -
  assume "R \<simeq> S"
  then obtain h where bij: "bij_betw h (carrier R) (carrier S)" and hom: "h \<in> ring_hom R S"
    unfolding is_ring_iso_def ring_iso_def by blast
  hence restrict_eq: "\<And>r. r \<in> carrier R \<Longrightarrow> h r = \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>"
    using unique_hom[OF hom assms] unfolding restrict_def by metis

  have "\<And>s. s \<in> carrier S \<Longrightarrow> \<exists>n. s = \<lbrakk> n \<rbrakk>\<^bsub>S\<^esub>"
  proof -
    fix s assume "s \<in> carrier S"
    then obtain r where r: "r \<in> carrier R" "h r = s"
      using bij_betw_imp_surj_on[OF bij] image_iff[of s h "carrier R"] by auto
    thus "\<exists>n. s = \<lbrakk> n \<rbrakk>\<^bsub>S\<^esub>"
      using restrict_eq[OF r(1)] by blast
  qed

  moreover have "\<And>n m. \<lbrakk> n \<rbrakk>\<^bsub>S\<^esub> = \<lbrakk> m \<rbrakk>\<^bsub>S\<^esub> \<Longrightarrow> n = m"
  proof -
    fix n m assume "\<lbrakk> n \<rbrakk>\<^bsub>S\<^esub> = \<lbrakk> m \<rbrakk>\<^bsub>S\<^esub>"
    hence "h \<lbrakk> n \<rbrakk> = h \<lbrakk> m \<rbrakk>"
      using restrict_eq[of "\<lbrakk> n \<rbrakk>"] restrict_eq[of "\<lbrakk> m \<rbrakk>"] elt_of_int_inj by auto
    hence "\<lbrakk> n \<rbrakk> = \<lbrakk> m \<rbrakk>"
      using bij unfolding bij_betw_def inj_on_def by auto
    thus "n = m"
      using unique_int_repr by simp
  qed

  ultimately show "int_ring S"
    using assms unfolding int_ring_def int_mod_def int_mod_axioms_def int_ring_axioms_def by auto
qed

corollary (in int_ring) integers_iso: "(\<lambda>r. int_repr r) \<in> ring_iso R \<Z>"
proof (rule ring_iso_memI)
  show "int_repr \<one> = \<one>\<^bsub>\<Z>\<^esub>"
    by (metis elt_of_int_inj elt_of_one_or_zero(1) monoid.select_convs(2))
  show "bij_betw (some_int R) (carrier R) (carrier \<Z>)"
    using int_repr_bij by simp
next
  fix x y assume x: "x \<in> carrier R" and y: "y \<in> carrier R"
  show "int_repr x \<in> carrier \<Z>"
    by simp
  show "int_repr (x \<otimes> y) = int_repr x \<otimes>\<^bsub>\<Z>\<^esub> int_repr y"
    using x y elt_of_int_inj elt_of_int_mult int_repr_wf monoid.select_convs(1) by metis
  show "int_repr (x \<oplus> y) = int_repr x \<oplus>\<^bsub>\<Z>\<^esub> int_repr y"
    using x y elt_of_int_inj elt_of_int_add int_repr_wf ring.simps(2) by metis
qed

lemma (in int_ring) mod_ring:
  assumes "a \<in> carrier R - { \<zero> }"
  shows "carrier (R Quot (PIdl a)) = (\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) ` {0..< \<bar> int_repr a \<bar>}"
proof
  show "(\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) ` {0..< \<bar> int_repr a \<bar>} \<subseteq> carrier (R Quot (PIdl a))"
    unfolding FactRing_def A_RCOSETS_def' by auto
next
  show "carrier (R Quot (PIdl a)) \<subseteq> (\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) ` {0..< \<bar> int_repr a \<bar>}"
  proof
    fix I assume "I \<in> carrier (R Quot (PIdl a))"
    then obtain b where b: "b \<in> carrier R" "I = PIdl a +> b"
      unfolding FactRing_def A_RCOSETS_def' by auto
    define c_repr where "c_repr = (int_repr b) mod \<bar> int_repr a \<bar>"
    hence "(c_repr - (int_repr b)) mod \<bar> int_repr a \<bar> = 0"
      by (metis diff_self mod_0 mod_diff_right_eq)
    hence "(int_repr a) dvd (c_repr - (int_repr b))"
      by auto
    hence "I = PIdl a +> \<lbrakk> c_repr \<rbrakk>"
      using rcoset_eq[of a "\<lbrakk> c_repr \<rbrakk>" b] assms b elt_of_int_inj[of "c_repr"] by auto
    moreover have "int_repr a \<noteq> 0"
      using assms int_repr_wf by force
    hence "0 < \<bar>int_repr a\<bar>"
      by simp
    hence "c_repr \<in> {0..< \<bar> int_repr a \<bar>}"
      unfolding c_repr_def using abs_mod_less by auto
    hence "PIdl a +> \<lbrakk> c_repr \<rbrakk> \<in> (\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) ` {0..< \<bar> int_repr a \<bar>}"
      by simp
    ultimately show "I \<in> (\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) ` {0..< \<bar> int_repr a \<bar>}"
      by simp
  qed
qed

lemma (in int_ring) mod_ring_card:
  assumes "a \<in> carrier R"
  shows "card (carrier (R Quot (PIdl a))) = \<bar> int_repr a \<bar>"
proof -
  have "card (carrier (R Quot (PIdl a))) = \<bar> int_repr a \<bar>" if "a \<in> carrier R - { \<zero> }"
  proof -
    have a_gt: "0 < \<bar> int_repr a \<bar>"
        using that int_repr_wf[of a] by auto

    have "\<And>i j. \<lbrakk> i \<in> {0..< \<bar> int_repr a \<bar>}; j \<in> {0..< \<bar> int_repr a \<bar>} \<rbrakk> \<Longrightarrow>
                  PIdl a +> \<lbrakk> i \<rbrakk> = PIdl a +> \<lbrakk> j \<rbrakk> \<Longrightarrow> i = j"
    proof -
      fix i j
      assume "i \<in> {0..< \<bar> int_repr a \<bar>}" "j \<in> {0..< \<bar> int_repr a \<bar>}"
      hence "0 \<le> i" "i < \<bar> int_repr a \<bar>"
        and "0 \<le> j" "j < \<bar> int_repr a \<bar>" by auto
      hence ij: "\<bar> i - j \<bar> < \<bar> int_repr a \<bar>"
        by linarith
      assume "PIdl a +> \<lbrakk> i \<rbrakk> = PIdl a +> \<lbrakk> j \<rbrakk>"
      then obtain k where "i - j = (int_repr a) * k"
        using rcoset_eq[of a "\<lbrakk> i \<rbrakk>" "\<lbrakk> j \<rbrakk>"] assms elt_of_int_inj[of i] elt_of_int_inj[of j]
        unfolding dvd_def by auto
      hence eq: "\<bar> i - j \<bar> = \<bar> int_repr a \<bar> * \<bar> k \<bar>"
        by (simp add: abs_mult)
      hence "\<bar> i - j \<bar> \<ge> \<bar> int_repr a \<bar>" if "\<bar> k \<bar> \<ge> 1"
        using that by (simp add: mult_le_cancel_left1)
      hence "\<not> \<bar> k \<bar> \<ge> 1"
        using ij by auto
      hence "\<bar> i - j \<bar> = 0"
        using eq by auto
      thus "i = j"
        by auto
    qed
    hence "inj_on (\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) {0..< \<bar> int_repr a \<bar>}"
      unfolding inj_on_def by auto
    hence  "card ((\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) ` {0..< \<bar> int_repr a \<bar>}) = card{0..< \<bar> int_repr a \<bar>}"
      using card_image by blast
    also have "... = \<bar> int_repr a \<bar>"
      using a_gt by auto
    finally have "card ((\<lambda>i. PIdl a +> \<lbrakk> i \<rbrakk>) ` {0..< \<bar> int_repr a \<bar>}) = \<bar> int_repr a \<bar>" .
    thus ?thesis
      using mod_ring[OF that] by simp
  qed

  moreover
  have "card (carrier (R Quot (PIdl a))) = \<bar> int_repr a \<bar>" if "a \<in> { \<zero> }"
  proof -
    have "ring_hom_ring R R id"
      apply unfold_locales unfolding ring_hom_def by auto
    hence "(\<lambda>X. the_elem (id ` X)) \<in> ring_iso (R Quot (a_kernel R R id)) R"
      using ring_hom_ring.FactRing_iso_set[of R R id] by simp
    moreover have "a_kernel R R id = { \<zero> }"
      using a_kernel_def'[of R R id] by auto
    hence "a_kernel R R id = PIdl a"
      using that zero_genideal cgenideal_eq_genideal[OF zero_closed] by simp
    ultimately have "(\<lambda>X. the_elem (id ` X)) \<in> ring_iso (R Quot (PIdl a)) R"
      by simp
    hence "bij_betw (\<lambda>X. the_elem (id ` X)) (carrier (R Quot (PIdl a))) (carrier R)"
      unfolding ring_iso_def by simp
    hence "card (carrier (R Quot (PIdl a))) = card (carrier R)"
      using bij_betw_same_card by simp
    hence "card (carrier (R Quot (PIdl a))) = 0"
      using char_eq_card char_eq_zero by simp
    also have " ... = \<bar> int_repr a \<bar>"
      using that elt_of_int_inj[of 0] elt_of_one_or_zero(2) by simp
    finally show "card (carrier (R Quot (PIdl a))) = \<bar> int_repr a \<bar>" .
  qed

  ultimately show ?thesis
    using assms by auto
qed

corollary (in int_ring) mod_ring_card': "card (carrier (R Quot (PIdl \<lbrakk> n \<rbrakk>))) = \<bar> n \<bar>"
  using mod_ring_card[of "\<lbrakk> n \<rbrakk>"] elt_of_int_inj[of n] by simp


lemma (in int_ring) FactRing_is_int_mod:
  assumes "a \<in> carrier R"
  shows "int_mod (R Quot (PIdl a))"
proof -
  have "ring (R Quot (PIdl a))"
    using assms by (simp add: cgenideal_ideal ideal.quotient_is_ring)
  moreover have "op +> (PIdl a) ` carrier R = carrier (R Quot PIdl a)"
    unfolding FactRing_def A_RCOSETS_def' by auto
  ultimately show ?thesis
    using surj_hom_imp_int_mod[OF ideal.rcos_ring_hom[OF cgenideal_ideal[OF assms]]] by simp
qed

lemma (in int_ring) FactRing_iso_int_mod:
  assumes "int_mod S"
  shows "R Quot (PIdl \<lbrakk> char S \<rbrakk>) \<simeq> S"
    and "PIdl \<lbrakk> char S \<rbrakk> = a_kernel R S (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>)"
proof -
  have "(\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>) ` (carrier R) = (carrier S)"
    using int_mod.elt_of_int_surj[OF assms] char_hom_surj by simp
  moreover have "ring S"
    using assms unfolding int_mod_def by simp
  hence ring_hom: "ring_hom_ring R S (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>)"
    using exists_hom[of S] is_ring unfolding ring_hom_ring_def ring_hom_ring_axioms_def by simp
  ultimately have "R Quot (a_kernel R S (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>)) \<simeq> S"
    using ring_hom_ring.FactRing_iso[of R S "\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>"] by simp
  moreover obtain n where n: "PIdl \<lbrakk> n \<rbrakk> = a_kernel R S (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>)"
    using ideal_int_repr[OF ring_hom_ring.kernel_is_ideal[OF ring_hom]] by auto
  ultimately have iso: "R Quot (PIdl \<lbrakk> n \<rbrakk>) \<simeq> S"
    by simp
  hence "\<bar> n \<bar> = card (carrier S)"
    using ring_iso_same_card[of "R Quot (PIdl \<lbrakk> n \<rbrakk>)" S] mod_ring_card'[of n] by simp
  hence "\<bar> n \<bar> = char S"
    using int_mod.char_eq_card[OF assms] by simp
  hence "PIdl \<lbrakk> n \<rbrakk> = PIdl \<lbrakk> char S \<rbrakk>"
    using associated_iff_same_abs[of "\<lbrakk> n \<rbrakk>" "\<lbrakk> char S \<rbrakk>"]
          associated_iff_same_ideal[of "\<lbrakk> n \<rbrakk>" "\<lbrakk> char S \<rbrakk>"]
          elt_of_int_inj[of n] elt_of_int_inj[of "char S"] by simp
  thus "R Quot (PIdl \<lbrakk> char S \<rbrakk>) \<simeq> S" and "PIdl \<lbrakk> char S \<rbrakk> = a_kernel R S (\<lambda>r. \<lbrakk> int_repr r \<rbrakk>\<^bsub>S\<^esub>)"
    using iso n by auto
qed

lemma (in int_mod) Z_mod:
  "\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char R)) \<simeq> R"
  "PIdl\<^bsub>\<Z>\<^esub> (char R) = a_kernel \<Z> R (\<lambda>k. \<lbrakk> k \<rbrakk>)"
  using int_ring.FactRing_iso_int_mod[OF int_ring_of_integers, of R]
        elt_of_integer integer_repr int_mod_axioms by auto

lemma (in ring) add_pow_eq_zero_iff: "(\<lbrakk> n \<rbrakk> = \<zero>) = ((int (char R)) dvd n)"
proof -
  let ?h = "\<lambda>k. \<lbrakk> k \<rbrakk>"
  let ?h_img = "R \<lparr> carrier := ?h ` (UNIV) \<rparr>"
  have aux_lemma: "\<And>n. \<lbrakk> n \<rbrakk> = \<lbrakk> n \<rbrakk>\<^bsub>(?h_img)\<^esub>"
  proof -
    fix n
    have "?h ` (UNIV) \<subseteq> carrier R"
      by auto
    thus "\<lbrakk> n \<rbrakk> = \<lbrakk> n \<rbrakk>\<^bsub>(?h_img)\<^esub>"
      using elt_of_int_consistent[of "?h ` (UNIV)" n] int_subring unfolding int_mod_def by simp
  qed
  hence h: "?h = (\<lambda>k. \<lbrakk> k \<rbrakk>\<^bsub>(?h_img)\<^esub>)"
    by blast

  have "(\<lbrakk> n \<rbrakk> = \<zero>) = (\<lbrakk> n \<rbrakk>\<^bsub>(?h_img)\<^esub> = \<zero>)"
    using aux_lemma[of n] by simp
  also have " ... = (n \<in> a_kernel \<Z> ?h_img (\<lambda>k. \<lbrakk> k \<rbrakk>\<^bsub>(?h_img)\<^esub>))"
    unfolding a_kernel_def' by simp
  also have " ... = (n \<in> PIdl\<^bsub>\<Z>\<^esub> int (char ?h_img))"
    using int_mod.Z_mod(2)[OF int_subring] by simp
  also have " ... = (n \<in> PIdl\<^bsub>\<Z>\<^esub> int (char R))"
    using int_mod.char_eq_card[OF int_subring] unfolding char_def by simp
  also have " ... = ((char R) dvd n)"
    using int_ring.in_ideal_iff[OF int_ring_of_integers, of n "char R"]
          elt_of_integer integer_repr by auto
  finally show ?thesis .
qed

lemma (in field) char_of_field: "char R = 0 \<or> prime' (char R)"
proof -
  let ?h = "\<lambda>k. \<lbrakk> k \<rbrakk>"
  let ?h_img = "R \<lparr> carrier := ?h ` (UNIV) \<rparr>"

  have char_eq: "char R = char ?h_img"
    using int_mod.char_eq_card[OF int_subring] unfolding char_def by simp

  have "char R \<noteq> 0 \<Longrightarrow> prime' (char R)"
  proof -
    assume "char R \<noteq> 0"
    hence A: "char R \<in> carrier \<Z> - { 0 }" "char ?h_img \<in> carrier \<Z> - { 0 }"
      by (auto simp add: char_eq)
    moreover have "\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char ?h_img)) \<simeq> ?h_img"
      using int_mod.Z_mod(1)[OF int_subring] by simp
    then obtain h
      where hom: "h \<in> ring_hom (\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char ?h_img))) ?h_img"
        and inj: "inj_on h (carrier (\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char ?h_img))))"
      unfolding is_ring_iso_def ring_iso_def bij_betw_def by auto
    moreover have "ring (\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char ?h_img)))"
      using ideal.quotient_is_ring cring.cgenideal_ideal[of \<Z> "char ?h_img"]
            int_ring_of_integers
      by (simp add: int_mod.axioms(1) int_ring.FactRing_is_int_mod) 
    hence "ring_hom_ring (\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char ?h_img))) ?h_img h"
      using ring_of_integers int_subring int_mod_def[of ?h_img] hom
            ideal.quotient_is_ring cring.cgenideal_ideal[of \<Z> "char ?h_img"]
      unfolding ring_hom_ring_def ring_hom_ring_axioms_def by simp
    moreover have "ring_hom_ring \<Z> R ?h"
      using int_ring.exists_hom[OF int_ring_of_integers is_ring] ring_of_integers is_ring
      unfolding ring_hom_ring_def ring_hom_ring_axioms_def by (simp add: integer_repr)
    hence "domain ?h_img"
      using ring_hom_ring.img_is_domain[of \<Z> R ?h] is_domain by simp
    ultimately have "domain (\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char ?h_img)))"
      using ring_hom_ring.inj_on_domain[of "\<Z> Quot (PIdl\<^bsub>\<Z>\<^esub> (char ?h_img))" ?h_img h] inj by simp
    moreover have "principal_domain \<Z>"
      using int_ring.is_principal_domain[OF int_ring_of_integers] .
    ultimately have "prime (mult_of \<Z>) (char ?h_img)"
      using principal_domain.domain_iff_prime[of \<Z> "char ?h_img"] A(2) char_eq
            int_ring_of_integers  by auto
    hence "prime' \<bar> int_repr\<^bsub>\<Z>\<^esub> (char R) \<bar>"
      using int_ring.prime_iff_prime'[OF int_ring_of_integers, of "char ?h_img"] A(2) char_eq by simp
    thus "prime' (char R)"
      using integer_repr unfolding char_def by simp
  qed
  thus ?thesis
    by blast
qed

end