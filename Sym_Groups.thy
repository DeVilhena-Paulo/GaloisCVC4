theory More_Sym_Groups
  imports Cycles Group Coset Generated_Groups Solvable_Groups
    
begin

abbreviation inv' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"
  where "inv' f \<equiv> Hilbert_Choice.inv f"
  
definition sym_group :: "nat \<Rightarrow> (nat \<Rightarrow> nat) monoid"
  where "sym_group n = \<lparr> carrier = { p. p permutes {1..n} }, mult = (op \<circ>), one = id \<rparr>"

definition sign_img :: "int monoid"
  where "sign_img = \<lparr> carrier = { -1, 1 }, mult = (op *), one = 1 \<rparr>"


lemma sym_group_is_group: "group (sym_group n)"
  apply (rule groupI)
  apply (simp_all add: sym_group_def permutes_compose permutes_id comp_assoc)
  using permutes_inv permutes_inv_o(2) by blast

lemma sym_group_inv_closed:
  assumes "p \<in> carrier (sym_group n)"
  shows "inv' p \<in> carrier (sym_group n)"
  using assms permutes_inv sym_group_def by auto

lemma sym_group_inv_equality:
  assumes "p \<in> carrier (sym_group n)"
  shows "inv\<^bsub>(sym_group n)\<^esub> p = inv' p"
proof -
  have "inv' p \<circ> p = id"
    using assms permutes_inv_o(2) sym_group_def by auto
  hence "(inv' p) \<otimes>\<^bsub>(sym_group n)\<^esub> p = one (sym_group n)"
    by (simp add: sym_group_def)
  thus ?thesis  using group.inv_equality[OF sym_group_is_group]
    by (simp add: assms sym_group_inv_closed)
qed

lemma sign_is_hom:
  "group_hom (sym_group n) sign_img sign"
  unfolding group_hom_def
proof (auto)
  show "group (sym_group n)"
    by (simp add: sym_group_is_group)
next
  show "group sign_img"
    unfolding sign_img_def group_def monoid_def group_axioms_def Units_def by auto
next
  show "group_hom_axioms (sym_group n) sign_img sign"
    unfolding sign_img_def group_hom_axioms_def sym_group_def hom_def
  proof auto
    show "\<And>x. sign x \<noteq> - 1 \<Longrightarrow> x permutes {Suc 0..n} \<Longrightarrow> sign x = 1"
      by (meson sign_def)
    show "\<And>x y. \<lbrakk> x permutes {Suc 0..n}; y permutes {Suc 0..n} \<rbrakk> \<Longrightarrow>
                  sign (x \<circ> y) = sign x * sign y"
      using sign_compose permutation_permutes by blast
  qed
qed


definition alt_group :: "nat \<Rightarrow> (nat \<Rightarrow> nat) monoid"
  where "alt_group n = (sym_group n) \<lparr> carrier := { p. p permutes {1..n} \<and> evenperm p } \<rparr>"

lemma alt_group_is_kernel_from_sign:
  "carrier (alt_group n) = kernel (sym_group n) sign_img sign"
  unfolding alt_group_def sym_group_def sign_img_def kernel_def sign_def by auto

lemma alt_group_is_group:
  "group (alt_group n)"
proof -
  have "subgroup (kernel (sym_group n) sign_img sign) (sym_group n)"
    using group_hom.subgroup_kernel sign_is_hom by blast
  thus ?thesis
    using alt_group_def alt_group_is_kernel_from_sign group.subgroup_imp_group
         sym_group_is_group by fastforce
qed

lemma alt_group_inv_closed:
  assumes "p \<in> carrier (alt_group n)"
  shows "inv' p \<in> carrier (alt_group n)"
  using assms permutes_inv alt_group_def
  using evenperm_inv permutation_permutes by fastforce

lemma alt_group_inv_equality:
  assumes "p \<in> carrier (alt_group n)"
  shows "inv\<^bsub>(alt_group n)\<^esub> p = inv' p"
proof -
  have "inv' p \<circ> p = id"
    using assms permutes_inv_o(2) alt_group_def by auto
  hence "(inv' p) \<otimes>\<^bsub>(alt_group n)\<^esub> p = one (alt_group n)"
    by (simp add: alt_group_def sym_group_def)
  thus ?thesis  using group.inv_equality[OF alt_group_is_group]
    by (simp add: assms alt_group_inv_closed)
qed


subsection \<open>Transposition Sequences\<close>

text \<open>In order to prove that the Alternating Group can be generated by 3-cycles, we need
      a stronger decomposition of permutations as transposition sequences than the one 
      proposed found at Permutations.thy\<close>

inductive swapseq :: "'a set \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
empty:  "swapseq {} 0 id" |
single: "\<lbrakk> swapseq S n p; a \<notin> S \<rbrakk> \<Longrightarrow> swapseq (insert a S) n p" |
comp:   "\<lbrakk> swapseq S n p; a \<noteq> b \<rbrakk> \<Longrightarrow>
           swapseq (insert a (insert b S)) (Suc n) ((Fun.swap a b id) \<circ> p)"


lemma swapseq_finite:
  assumes "swapseq S n p"
  shows "finite S" using assms
  apply (induction) by auto

lemma swapseq_zero_imp_id:
  assumes "swapseq S 0 p"
  shows "p = id"
proof -
  { fix S n and p :: "'a \<Rightarrow> 'a" assume "swapseq S n p" "n = 0"
    hence "p = id"
      apply (induction) by auto }
  thus ?thesis using assms by auto
qed

lemma swapseq_zero:
  assumes "finite S"
  shows "swapseq S 0 id" using assms 
proof (induct set: "finite")
  case empty thus ?case using swapseq.empty .
next
  case insert show ?case using swapseq.single[OF insert(3) insert(2)] .
qed

lemma swapseq_finite_expansion:
  assumes "finite B" "swapseq A n p"
  shows "swapseq (A \<union> B) n p" using assms 
proof (induct set: "finite")
  case empty thus ?case by simp
next
  case insert show ?case
    by (metis Un_insert_right insert.hyps(3) insert.prems insert_absorb single) 
qed

lemma swapseq_backwards:
  assumes "swapseq A (Suc n) p"
  shows "\<exists>a b A' p'. a \<noteq> b \<and> A = (insert a (insert b A')) \<and>
                     swapseq A' n p' \<and> p = (Fun.swap a b id) \<circ> p'"
proof -
  { fix A n k and p :: "'a \<Rightarrow> 'a" assume "swapseq A n p" "n = Suc k"
    hence "\<exists>a b A' p'. a \<noteq> b \<and> A = (insert a (insert b A')) \<and>
                       swapseq A' k p' \<and> p = (Fun.swap a b id) \<circ> p'"
    proof (induction)
      case empty thus ?case by simp
    next
      case single thus ?case
        by (metis Un_insert_right insert_iff insert_is_Un swapseq.single)
    next
      case comp thus ?case by blast 
    qed }
  thus ?thesis using assms by simp
qed

lemma swapseq_endswap:
  assumes "swapseq S n p" "a \<noteq> b"
  shows "swapseq (insert a (insert b S)) (Suc n) (p \<circ> (Fun.swap a b id))" using assms
proof (induction n arbitrary: S p a b)
  case 0 hence "p = id"
    using swapseq_zero_imp_id by blast
  thus ?case using 0 by (metis comp_id id_comp swapseq.comp) 
next
  case (Suc n)
  then obtain c d S' and p' :: "'a \<Rightarrow> 'a"
    where cd: "c \<noteq> d"
      and S: "S = (insert c (insert d S'))" "swapseq S' n p'"
      and p: "p = (Fun.swap c d id) \<circ> p'"
    using swapseq_backwards[OF Suc(2)] by blast
  hence "swapseq (insert a (insert b S')) (Suc n) (p' \<circ> (Fun.swap a b id))"
    by (simp add: Suc.IH Suc.prems(2))
  hence "swapseq (insert c (insert d (insert a (insert b S')))) (Suc (Suc n))
                 ((Fun.swap c d id) \<circ> p' \<circ> (Fun.swap a b id))"
    by (metis cd fun.map_comp swapseq.comp)
  then show ?case by (metis S(1) p insert_commute) 
qed

lemma swapseq_imp_swapiseq:
  assumes "swapseq S n p"
  shows "swapidseq n p" using assms
proof (induction)
  case empty thus ?case by simp
  case single show ?case using single(3) .
next
  case comp thus ?case by (meson comp_Suc) 
qed

lemma swapseq_extension:
  assumes "swapseq A n p" "swapseq B m q" "A \<inter> B = {}"
  shows "swapseq (A \<union> B) (n + m) (p \<circ> q)"
proof -
  { fix m and q :: "'a \<Rightarrow> 'a" and A B :: "'a set" assume "finite A" "swapseq B m q"
    hence "swapseq (A \<union> B) m q"
    proof (induct set: "finite")
      case empty thus ?case by simp
    next
      case (insert a A') thus ?case
        using swapseq.single[of "A' \<union> B" m q a]
        by (metis Un_insert_left insert_absorb) 
    qed } note aux_lemma = this

  from assms show ?thesis
  proof (induct n arbitrary: p A)
    case 0 thus ?case
      using swapseq_zero_imp_id[OF 0(1)] aux_lemma[of A B m q] by (simp add: swapseq_finite)
  next
    case (Suc n)
    obtain a b A' and p' :: "'a \<Rightarrow> 'a"
      where A': "a \<noteq> b" "A = (insert a (insert b A'))"
        and p': "swapseq A' n p'"
        and p: "p = (Fun.swap a b id) \<circ> p'"
      using swapseq_backwards[OF Suc(2)] by blast
    hence "swapseq (A' \<union> B) (n + m) (p' \<circ> q)"
      using Suc.hyps Suc.prems(3) assms(2) by fastforce
    thus ?case using swapseq.comp[of "A' \<union> B" "n + m" "p' \<circ> q" a b]
      by (metis Un_insert_left p A' add_Suc rewriteR_comp_comp)
  qed
qed

lemma swapseq_of_cycles:
  assumes "cycle cs"
  shows "swapseq (set cs) (length cs - 1) (cycle_of_list cs)" using assms
proof (induction cs rule: cycle_of_list.induct)
  case (1 i j cs) show ?case
  proof (cases)
    assume "cs = []" thus ?case
      using swapseq.comp[OF swapseq.empty, of i j] "1.prems" by auto 
  next
    assume "cs \<noteq> []" hence "length (j # cs) \<ge> 2"
      using not_less_eq_eq by fastforce
    hence IH: "swapseq (set (j # cs)) (length (j # cs) - 1) (cycle_of_list (j # cs))"
      using "1.IH" "1.prems" by auto
    thus ?case using swapseq.comp[OF IH, of i j]
      by (metis "1.prems" cycle_of_list.simps(1) diff_Suc_1 distinct.simps(2)
          distinct_length_2_or_more insert_absorb length_Cons list.simps(15))
  qed
next
  case "2_1" thus ?case using swapseq.empty
    by (metis cycle_of_list.simps(2) diff_0_eq_0 empty_set list.size(3)) 
next
  case ("2_2" v) thus ?case using swapseq.single[OF swapseq.empty, of v]
    by (metis cycle_of_list.simps(3) diff_Suc_1 distinct.simps(2)
              empty_set length_Cons list.simps(15) list.size(3))
qed

lemma cycle_decomp_imp_swapseq:
  assumes "cycle_decomp S p"
  shows "\<exists>n. swapseq S n p" using assms
proof (induction)
  case empty
  then show ?case using swapseq.empty by blast
next
  case (comp I p cs)
  then obtain m where m: "swapseq I m p" by blast
  hence "swapseq (set cs) (length cs - 1) (cycle_of_list cs)"
    using comp.hyps(2) swapseq_of_cycles by blast
  thus ?case using swapseq_extension m
    using comp.hyps(3) by blast
qed

lemma swapseq_of_permutations:
  assumes "p permutes S" "finite S"
  shows "\<exists>n. swapseq S n p"
  using assms cycle_decomp_imp_swapseq cycle_decomposition by blast

lemma split_swapidseq:
  assumes "k \<le> n" "swapidseq n p"
  shows "\<exists>q r. swapidseq k q \<and> swapidseq (n - k) r \<and> p = q \<circ> r"
proof -
  { fix n :: "nat" and p :: "'a \<Rightarrow> 'a" assume "swapidseq (Suc n) p"
    hence "\<exists>a b q. a \<noteq> b \<and> swapidseq n q \<and> p = (Fun.swap a b id) \<circ> q"
    proof (cases)
      case comp_Suc thus ?thesis by auto
    qed } note aux_lemma = this

  from assms show ?thesis
  proof (induction k)
    case 0 thus ?case by simp
  next
    case (Suc k)
    then obtain r q where 1: "swapidseq k q" "swapidseq (n - k) r" "p = q \<circ> r"
      using Suc_leD by blast
    then obtain a b r' where 2: "a \<noteq> b" "swapidseq (n - (Suc k)) r'" "r = (Fun.swap a b id) \<circ> r'"
      using aux_lemma[of "n - (Suc k)" r] by (metis Suc.prems(1) Suc_diff_le diff_Suc_Suc)
    have "swapidseq (Suc k) (q \<circ> (Fun.swap a b id))" using 1 2 by (simp add: swapidseq_endswap)
    moreover have "p = (q \<circ> (Fun.swap a b id)) \<circ> r'"
      using 1 2 fun.map_comp by blast 
    ultimately show ?case using 2 by blast 
  qed
qed

lemma split_swapseq:
  assumes "k \<le> n" "swapseq S n p"
  obtains q r S1 S2 where "swapseq S1 k q" "swapseq S2 (n - k) r" "p = q \<circ> r" "S1 \<union> S2 = S"
proof -
  from assms have "\<exists>q r S1 S2. swapseq S1 k q \<and> swapseq S2 (n - k) r \<and> p = q \<circ> r \<and> S1 \<union> S2 = S"
  proof (induction k)
    case 0 have "finite S"
      using "0.prems"(2) swapseq_finite by auto
    have "swapseq {} 0 id \<and> swapseq S (n - 0) p \<and> p = id \<circ> p"
      using swapseq.empty by (simp add: assms(2)) 
    thus ?case by blast
  next
    case (Suc k)
    then obtain q r S1 S2 where "swapseq S1 k q" "swapseq S2 (n - k) r" "p = q \<circ> r" "S1 \<union> S2 = S"
      using Suc_leD by blast
    then obtain a b S2' and r' :: "'a \<Rightarrow> 'a"
      where S2': "a \<noteq> b" "S2 = (insert a (insert b S2'))"
        and  r': "swapseq S2' (n - (Suc k)) r'"
        and   r: "r = (Fun.swap a b id) \<circ> r'"
      by (metis Suc.prems(1) Suc_diff_le diff_Suc_Suc swapseq_backwards)

    have "swapseq (insert a (insert b S1)) (Suc k) (q \<circ> (Fun.swap a b id))"
      by (simp add: S2'(1) \<open>swapseq S1 k q\<close> swapseq_endswap)
    moreover have "p = (q \<circ> (Fun.swap a b id)) \<circ> r'"
      by (simp add: \<open>p = q \<circ> r\<close> fun.map_comp r)
    moreover have "(insert a (insert b S1)) \<union> S2' = S"
      using S2'(2) \<open>S1 \<union> S2 = S\<close> by auto
    ultimately show ?case using r r' by blast
  qed
  thus ?thesis using that by blast
qed



abbreviation three_cycles :: "nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "three_cycles n \<equiv>
           { cycle_of_list cs | cs. cycle cs \<and> length cs = 3 \<and> set cs \<subseteq> {1..n} }"


lemma stupid_lemma:
  assumes "length cs = 3"
  shows "cs = [(cs ! 0), (cs ! 1), (cs ! 2)]"
proof (intro nth_equalityI)
  show "length cs = length [(cs ! 0), (cs ! 1), (cs ! 2)]"
    using assms by simp
  show "\<forall> ia < length cs. cs ! ia = [(cs ! 0), (cs ! 1), (cs ! 2)] ! ia"
    by (metis Suc_1 Suc_eq_plus1 add.left_neutral assms less_antisym
        less_one nth_Cons' nth_Cons_Suc numeral_3_eq_3)
qed

lemma alt_group_as_three_cycles:
  "carrier (alt_group n) = generate (alt_group n) (three_cycles n)"
proof
  show "generate (alt_group n) (three_cycles n) \<subseteq> carrier (alt_group n)"
  proof
    { fix p assume "p \<in> three_cycles n"
      have "p \<in> carrier (alt_group n)"
      proof -
        from \<open>p \<in> three_cycles n\<close>
        obtain cs where p: "p = cycle_of_list cs"
                    and cs: "cycle cs" "length cs = 3" "set cs \<subseteq> {1..n}" by blast
        hence "p = (Fun.swap (cs ! 0) (cs ! 1) id) \<circ> (Fun.swap (cs ! 1) (cs ! 2) id)"
          using stupid_lemma[OF cs(2)] p
          by (metis comp_id cycle_of_list.simps(1) cycle_of_list.simps(3)) 

        hence "evenperm p"
          by (metis cs(1) distinct_length_2_or_more evenperm_comp
                    evenperm_swap permutation_swap_id stupid_lemma[OF cs(2)])

        moreover have "permutation p" using p cs(1) cycle_permutes by simp
        hence "p permutes {1..n}"
          using id_outside_supp[OF cs(1)] p cs permutation_permutes unfolding permutes_def
          by (metis permutation_permutes permutes_def subsetCE)

        ultimately show ?thesis by (simp add: alt_group_def)
      qed } note aux_lemma = this

    fix p assume "p \<in> generate (alt_group n) (three_cycles n)"
    thus "p \<in> carrier (alt_group n)"
    proof (induction)
      case one thus ?case by (simp add: alt_group_is_group group.is_monoid) 
      case incl thus ?case using aux_lemma unfolding alt_group_def by auto
      case inv thus ?case using aux_lemma by (simp add: alt_group_is_group) next
      case eng thus ?case by (simp add: alt_group_is_group group.is_monoid monoid.m_closed) 
    qed
  qed

next
  show "carrier (alt_group n) \<subseteq> generate (alt_group n) (three_cycles n)"
  proof
    fix p assume p: "p \<in> carrier (alt_group n)"
    show "p \<in> generate (alt_group n) (three_cycles n)"
    proof -
      { fix q :: "nat \<Rightarrow> nat" and a b c
        assume A: "a \<noteq> b" "b \<noteq> c" "{ a, b, c } \<subseteq> {1..n}" "q = cycle_of_list [a, b, c]" 
        have "q \<in> generate (alt_group n) (three_cycles n)"
        proof (cases)
          assume "c = a" hence "q = id" by (simp add: A(4) swap_commute)
          thus "q \<in> generate (alt_group n) (three_cycles n)"
            using generate.one[of "alt_group n"] by (simp add: alt_group_def sym_group_def)
        next
          assume "c \<noteq> a" hence "q \<in> (three_cycles n)"
            by (smt A distinct.simps(2) distinct_singleton empty_set length_Cons
                list.simps(15) list.size(3) mem_Collect_eq numeral_3_eq_3 set_ConsD)
          thus "q \<in> generate (alt_group n) (three_cycles n)"
            by (simp add: generate.incl)
        qed } note aux_lemma1 = this
      
      { fix S :: "nat set" and q :: "nat \<Rightarrow> nat" assume A: "swapseq S 2 q" "S \<subseteq> {1..n}"
        have "q \<in> generate (alt_group n) (three_cycles n)"
        proof -
          obtain a b S' q' where ab: "a \<noteq> b" "S = (insert a (insert b S'))"
                             and q': "swapseq S' 1 q'" "q = (Fun.swap a b id) \<circ> q'"
            using swapseq_backwards[of S 1 q] A(1) Suc_1 by metis
          then obtain c d S'' where cd: "c \<noteq> d" "S' = (insert c (insert d S''))"
                                and q: "q = (Fun.swap a b id) \<circ> (Fun.swap c d id)"
            using swapseq_backwards[of S' 0 q']
            by (metis One_nat_def comp_id swapseq_zero_imp_id)
          hence incl: "{ a, b, c, d } \<subseteq> {1..n}" using A(2) ab(2) by blast
          thus ?thesis
          proof (cases)
            assume Eq: "b = c" hence "q = cycle_of_list [a, b, d]" by (simp add: q)
            thus ?thesis using aux_lemma1 ab cd Eq incl by simp
          next
            assume In: "b \<noteq> c"
            have "q = (cycle_of_list [a, b, c]) \<circ> (cycle_of_list [b, c, d])"
              by (metis (no_types, lifting) comp_id cycle_of_list.simps(1)
                  cycle_of_list.simps(3) fun.map_comp q swap_id_idempotent)
            thus ?thesis
              using aux_lemma1[of a b c] aux_lemma1[of b c d]
                    generate.eng[where ?h1.0 = "cycle_of_list [a, b, c]"
                                   and ?h2.0 = "cycle_of_list [b, c, d]"]
              using In ab alt_group_def cd sym_group_def incl
              by (smt insert_subset monoid.select_convs(1) partial_object.simps(3)) 
          qed
        qed } note aux_lemma2 = this
      
      have "p permutes {1..n}"
        using p permutation_permutes unfolding alt_group_def by auto
      then obtain l where "swapseq {1..n} l p" "swapidseq l p"
        using swapseq_of_permutations swapseq_imp_swapiseq by blast

      have "evenperm p" using p by (simp add: alt_group_def)
      hence "even l" using \<open>swapidseq l p\<close> evenperm_unique by blast

      then obtain k where "swapseq {1..n} (2 * k) p"
        using dvd_def by (metis \<open>swapseq {1..n} l p\<close>)
      thus "p \<in> generate (alt_group n) (three_cycles n)"
      proof (induct k arbitrary: p)
        case 0
        hence "p = id" by (simp add: swapseq_zero_imp_id) 
        moreover have "id \<in> generate (alt_group n) (three_cycles n)"
          using generate.one[of "alt_group n"] by (simp add: alt_group_def sym_group_def) 
        ultimately show ?case by blast
      next
        case (Suc k)
        then obtain S1 S2 q r
          where split: "swapseq S1 2 q" "swapseq S2 (2 * k) r" "p = q \<circ> r" "S1 \<union> S2 = {1..n}"
          using split_swapseq[of 2 "2 * Suc k" "{1..n}" p]
          by (smt One_nat_def Suc_1 Suc_leI Suc_le_mono add_diff_cancel_left' le_Suc_eq
              mult_Suc_right nat_mult_eq_1_iff one_le_mult_iff zero_less_Suc)

        hence "r \<in> generate (alt_group n) (three_cycles n)"
          using Suc.hyps swapseq_finite_expansion[of "{1..n}" S2 "2 * k" r]
          by (metis (no_types, lifting) Suc.prems Un_commute sup.right_idem swapseq_finite)

        moreover have "q \<in> generate (alt_group n) (three_cycles n)"
          using aux_lemma2[OF split(1)] \<open>S1 \<union> S2 = {1..n}\<close> by auto
        ultimately show ?case
          using split generate.eng[of q "alt_group n" "three_cycles n" r]
          by (smt alt_group_def monoid.select_convs(1) partial_object.simps(3) sym_group_def)
      qed
    qed
  qed
qed

lemma elts_from_card:
  assumes "card S \<ge> n"
  obtains f where "inj_on f {1..n}" "f ` {1..n} \<subseteq> S"
proof -
  have "\<exists>f. inj_on f {1..n} \<and> f ` {1..n} \<subseteq> S" using assms
  proof (induction n)
    case 0 thus ?case by simp
  next
    case (Suc n)
    then obtain f where f: "inj_on f {1..n}" "f ` {1..n} \<subseteq> S"
      using Suc_leD by blast
    hence "card (f ` {1..n}) = n" by (simp add: card_image)
    then obtain y where y: "y \<in> S - (f ` {1..n})"
      by (metis Diff_eq_empty_iff Suc.prems \<open>f ` {1..n} \<subseteq> S\<close> not_less_eq_eq order_refl some_in_eq subset_antisym)
    define f' where f': "f' = (\<lambda>x. (if x \<in> {1..n} then f x else y))"
    hence "\<And>i j. \<lbrakk> i \<in> {1..Suc n}; j \<in> {1..Suc n} \<rbrakk> \<Longrightarrow> f' i = f' j \<Longrightarrow> i = j"
      by (metis (no_types, lifting) DiffD2 f(1) y atLeastAtMostSuc_conv atLeastatMost_empty_iff2
          card_0_eq card_atLeastAtMost diff_Suc_1 finite_atLeastAtMost image_eqI inj_onD insertE nat.simps(3))
    moreover have "f' ` {1..n} \<subseteq> S \<and> f' (Suc n) \<in> S"
      using f f' y by (simp add: image_subset_iff)
    hence "f' ` {1..Suc n} \<subseteq> S" using f' by auto 
    ultimately show ?case unfolding inj_on_def by blast  
  qed
  thus ?thesis using that by auto
qed

theorem derived_alt_group_is_cons:
  assumes "n \<ge> 5"
  shows "derived (alt_group n) (carrier (alt_group n)) = carrier (alt_group n)"
proof
  show "derived (alt_group n) (carrier (alt_group n)) \<subseteq> carrier (alt_group n)"
    by (simp add: alt_group_is_group group.derived_incl group.subgroup_self)
next
  show "carrier (alt_group n) \<subseteq> derived (alt_group n) (carrier (alt_group n))"
  proof -
    have derived_set_in_carrier:
      "derived_set (alt_group n) (carrier (alt_group n)) \<subseteq> carrier (alt_group n)"
    proof
      fix p assume "p \<in> derived_set (alt_group n) (carrier (alt_group n))"
      then obtain q r
        where q: "q \<in> carrier (alt_group n)"
          and r: "r \<in> carrier (alt_group n)"
          and "p = q \<otimes>\<^bsub>(alt_group n)\<^esub> r \<otimes>\<^bsub>(alt_group n)\<^esub> (inv' q) \<otimes>\<^bsub>(alt_group n)\<^esub> (inv' r)"
        using alt_group_inv_equality by auto
      hence p: "p = q \<circ> r \<circ> (inv' q) \<circ> (inv' r)"
        by (simp add: alt_group_def sym_group_def)

      have "q permutes {1..n}" using q by (simp add: alt_group_def)
      moreover have r_perm: "r permutes {1..n}" using r by (simp add: alt_group_def)
      ultimately have "p permutes {1..n} \<and> evenperm p" using p
        apply (simp add: permutes_compose permutes_inv)
        by (metis evenperm_comp evenperm_inv finite_atLeastAtMost
            permutation_compose permutation_inverse permutation_permutes) 
      thus "p \<in> carrier (alt_group n)" by (simp add: alt_group_def)
    qed

    have "three_cycles n \<subseteq> derived_set (alt_group n) (carrier (alt_group n))"
    proof
      fix p :: "nat \<Rightarrow> nat" assume "p \<in> three_cycles n"
      then obtain cs
        where cs: "cycle cs" "length cs = 3" "set cs \<subseteq> {1..n}" and p: "p = cycle_of_list cs" by blast
      then obtain i j k where i: "i = cs ! 0" and j: "j = cs ! 1" and k: "k = cs ! 2"
                          and ijk: "cs = [i, j, k]" using stupid_lemma[OF cs(2)] by blast

      have "p ^^ 2 = cycle_of_list [i, k, j]"
      proof
        fix l show "(p ^^ 2) l = cycle_of_list [i, k, j] l"
        proof (cases)
          assume "l \<notin> {i, j, k}"
          hence "l \<notin> set cs \<and> l \<notin> set [i, k, j]" using ijk by auto
          thus ?thesis
            using id_outside_supp[of cs l] id_outside_supp[of "[i, j, k]" l] p o_apply
            by (simp add: ijk numeral_2_eq_2)
        next
          assume "\<not> l \<notin> {i, j, k}" hence "l \<in> {i, j, k}" by simp
          have "map ((cycle_of_list cs) ^^ 2) cs = rotate 2 cs"
            using cyclic_rotation[of cs 2] cs by simp
          also have " ... = rotate1 (rotate1 [i, j , k])"
            by (metis One_nat_def Suc_1 funpow_0 ijk rotate_Suc rotate_def)
          also have " ... = [k, i, j]" by simp
          finally have "map ((cycle_of_list cs) ^^ 2) cs = [k, i, j]" .
          hence "map (p ^^ 2) [i, j, k] = [k, i, j]" using p ijk by simp

          moreover have "map (cycle_of_list [i, k, j]) [i, j, k] = [k, i, j]"
            using cs(1) ijk by auto 

          ultimately show ?thesis using \<open>l \<in> {i, j, k}\<close> by auto
        qed
      qed
      hence "p ^^ 2 = (Fun.swap j k id) \<circ> (cycle_of_list [i, j, k]) \<circ> (inv' (Fun.swap j k id))"
        using conjugation_of_cycle[of "[i, j, k]" "Fun.swap j k id"] cs(1) ijk by auto

      moreover have "card ({1..n} - {i, j, k}) \<ge> card {1..n} - card {i, j, k}"
        by (meson diff_card_le_card_Diff finite.emptyI finite.insertI)
      hence card_ge_two: "card ({1..n} - {i, j, k}) \<ge> 2"
        using assms cs ijk by simp
      then obtain f :: "nat \<Rightarrow> nat" where f: "inj_on f {1..2}" "f ` {1..2} \<subseteq> {1..n} - {i, j, k}"
        using elts_from_card[OF card_ge_two] by blast  
      then obtain g h where gh: "g = f 1" "h = f 2" "g \<noteq> h"
        by (metis Suc_1 atLeastAtMost_iff diff_Suc_1 diff_Suc_Suc inj_onD nat.simps(3) one_le_numeral order_refl)
      hence g: "g \<in> {1..n} - {i, j, k}" using f(2) gh(2) by force
      hence h: "h \<in> {1..n} - {i, j, k}" using f(2) gh(2) by force
      hence gh_simps: "g \<noteq> h \<and> g \<in> {1..n} \<and> h \<in> {1..n} \<and> g \<notin> {i, j, k} \<and> h \<notin> {i, j, k}"
        using g gh(3) by blast

      ultimately have final_step:
        "p ^^ 2 = ((Fun.swap j k id) \<circ> (Fun.swap g h id)) \<circ>
                  (cycle_of_list [i, j, k]) \<circ>
                  (inv' ((Fun.swap j k id) \<circ> (Fun.swap g h id)))"
        by (smt bij_id bij_swap_iff comp_id cycle_of_list.simps(1) cycle_of_list.simps(3)
            fun.map_comp insertCI inv_swap_id o_inv_distrib o_inv_o_cancel surj_id
            surj_imp_inj_inv surj_imp_surj_swap swap_id_independent)
      
      define q where "q = (Fun.swap j k id) \<circ> (Fun.swap g h id)"

      hence "(p \<circ> p) = q \<circ> p \<circ> (inv' q)"
        by (metis final_step One_nat_def Suc_1 comp_id funpow.simps(2) funpow_simps_right(1) ijk p)
      hence "(p \<circ> p) \<circ> (inv' p) = q \<circ> p \<circ> (inv' q) \<circ> (inv' p)" by simp
      hence 1: "p = q \<circ> p \<circ> (inv' q) \<circ> (inv' p)"
        using p cycle_permutes[OF cs(1)] o_assoc[of p p "inv' p"]
        by (simp add: permutation_inverse_works(2))

      have "(Fun.swap j k id) \<circ> (Fun.swap g h id) permutes {1..n}"
        by (metis cs(3) gh_simps ijk insert_subset list.simps(15) permutes_compose permutes_swap_id)
      moreover have "evenperm ((Fun.swap j k id) \<circ> (Fun.swap g h id))"
        by (metis cs(1) distinct_length_2_or_more evenperm_comp evenperm_swap gh(3) ijk permutation_swap_id)
      ultimately have 2: "q \<in> carrier (alt_group n)"
        by (simp add: alt_group_def q_def)

      have 3: "p \<in> carrier (alt_group n)"
        using alt_group_as_three_cycles generate.incl[OF \<open>p \<in> three_cycles n\<close>] by simp

      from 1 2 3 show "p \<in> derived_set (alt_group n) (carrier (alt_group n))"
        using alt_group_is_group[of n] alt_group_inv_equality[OF 2] alt_group_inv_equality[OF 3]
        unfolding alt_group_def sym_group_def by fastforce
    qed
    hence "generate (alt_group n) (three_cycles n) \<subseteq> derived (alt_group n) (carrier (alt_group n))"
      unfolding derived_def
      using group.mono_generate[OF alt_group_is_group[of n]] derived_set_in_carrier by simp
    thus ?thesis using alt_group_as_three_cycles by blast
  qed
qed

corollary alt_group_not_solvable:
  assumes "n \<ge> 5"
  shows "\<not> solvable (alt_group n)"
proof (rule ccontr)
  assume "\<not> \<not> solvable (alt_group n)" hence "solvable (alt_group n)" by simp
  then obtain k
    where trivial_seq: "(derived (alt_group n) ^^ k) (carrier (alt_group n)) = { \<one>\<^bsub>alt_group n\<^esub> }"
    using group.solvable_iff_trivial_derived_seq[OF alt_group_is_group[of n]] by blast

  have "(derived (alt_group n) ^^ k) (carrier (alt_group n)) = (carrier (alt_group n))"
    apply (induction k) using derived_alt_group_is_cons[OF assms] by auto
  hence "carrier (alt_group n) = { \<one>\<^bsub>alt_group n\<^esub> }"
    using trivial_seq by auto
  hence singleton: "carrier (alt_group n) = { id }"
    by (simp add: alt_group_def sym_group_def) 

  have "set [1 :: nat, 2, 3] \<subseteq> {1..n}" using assms by auto
  moreover have "cycle [1 :: nat, 2, 3]" by simp
  moreover have "length [1 :: nat, 2, 3] = 3" by simp
  ultimately have "cycle_of_list [1 :: nat, 2, 3] \<in> three_cycles n" by blast
  hence "cycle_of_list [1 :: nat, 2, 3] \<in> carrier (alt_group n)"
    using alt_group_as_three_cycles by (simp add: generate.incl)

  moreover have "map (cycle_of_list [1 :: nat, 2, 3]) [1 :: nat, 2, 3] = [2 :: nat, 3, 1]"
    using cyclic_rotation[OF \<open>cycle [1 :: nat, 2, 3]\<close>, of 1] by simp
  hence "cycle_of_list [1 :: nat, 2, 3] \<noteq> id"
    by (metis list.map_id list.sel(1) numeral_One numeral_eq_iff semiring_norm(85))

  ultimately show False using singleton by blast
qed

corollary sym_group_not_solvable:
  assumes "n \<ge> 5"
  shows "\<not> solvable (sym_group n)"
proof -
  have "subgroup (kernel (sym_group n) sign_img sign) (sym_group n)"
    using group_hom.subgroup_kernel sign_is_hom by blast
  hence "subgroup (carrier (alt_group n)) (sym_group n)"
    using alt_group_is_kernel_from_sign[of n] by simp
  hence "group_hom (alt_group n) (sym_group n) id"
    using group.canonical_inj_is_hom[OF sym_group_is_group[of n]] by (simp add: alt_group_def)
  thus ?thesis
    using group_hom.not_solvable[of "alt_group n" "sym_group n" id]
          alt_group_not_solvable[OF assms] inj_on_id by blast
qed

end