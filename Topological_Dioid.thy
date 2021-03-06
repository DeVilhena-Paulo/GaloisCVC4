theory Topological_Dioid
  imports Dioid 
begin

sublocale dioid \<subseteq> order_topology "dioid_canonic_order D" "dioid_canonic_strict_order D"
"generate_topology (range (ord.lessThan (dioid_canonic_strict_order D)) \<union>
   range (ord.greaterThan (dioid_canonic_strict_order D)))"
proof
  show P1 : "\<And>x y. (x <\<^bsub>D\<^esub> y) = (x \<le>\<^bsub>D\<^esub> y \<and> \<not> y \<le>\<^bsub>D\<^esub> x)"
    unfolding dioid_canonic_strict_order_def dioid_canonic_order_def factor_def apply auto
  proof (rule ccontr)
    fix x y z assume xyz : "x \<noteq> x \<oplus> y" "y \<in> carrier D" "x \<in> carrier D" "z \<in> carrier D" "x = x\<oplus>y\<oplus>z"
    from this have "\<zero> = y \<oplus> z "
      using a_comm_cancel_monoid 
      by (metis add.m_assoc add.m_closed cancel r_zero zero_closed)
    hence A : "y \<le> \<zero>"
      unfolding dioid_canonic_order_def
      using xyz by auto
    moreover have B : "\<zero> \<le> y"
      unfolding dioid_canonic_order_def
      using xyz zero_closed add.Units_one_closed add.unit_divides
      by presburger
    ultimately have "\<zero> = y"
      using partial_order.le_antisym[OF canonically_ordered] xyz(2) zero_closed
      by (metis (no_types, lifting) gorder.select_convs(1) partial_object.select_convs(1))
    hence "x = x \<oplus> y" using xyz by auto
    thus False using xyz by auto
  qed
  show "\<And>x. x \<le>\<^bsub>D\<^esub> x" unfolding dioid_canonic_order_def by auto
  show "\<And>x y z. x \<le>\<^bsub>D\<^esub> y \<Longrightarrow> y \<le>\<^bsub>D\<^esub> z \<Longrightarrow> x \<le>\<^bsub>D\<^esub> z" unfolding dioid_canonic_order_def apply auto
    using add.divides_trans by blast
  show "\<And>x y. x \<le>\<^bsub>D\<^esub> y \<Longrightarrow> y \<le>\<^bsub>D\<^esub> x \<Longrightarrow> x = y"
    using partial_order.le_antisym[OF canonically_ordered] P1 apply simp
    unfolding dioid_canonic_order_def
    by blast
  show "generate_topology (range (ord.lessThan (dioid_canonic_strict_order D)) \<union>
                           range (ord.greaterThan (dioid_canonic_strict_order D))) =
        generate_topology (range (ord.lessThan (dioid_canonic_strict_order D)) \<union>
                           range (ord.greaterThan (dioid_canonic_strict_order D)))"
    by simp
qed


lemma (in dioid) topological_dioid :
"class.order_topology (dioid_canonic_order D) (dioid_canonic_strict_order D)
(generate_topology (range (ord.lessThan (dioid_canonic_strict_order D)) \<union>
   range (ord.greaterThan (dioid_canonic_strict_order D))))"
  using order_topology_axioms.




typedef 'a kr = "{R :: 'a ring. dioid R}"
proof
  fix x :: 'a
  show "(\<lparr>carrier =  {x}, monoid.mult = \<lambda>x y. y, one = x, zero = x, add = \<lambda>x y. y\<rparr>) \<in> {R. dioid R}"
  proof
    show "dioid \<lparr>carrier = {x}, monoid.mult = \<lambda>x y. y, one = x, zero = x, add = \<lambda>x y. y\<rparr>"
      apply unfold_locales apply auto unfolding dioid_canonic_order_def factor_def apply simp.
  qed
qed
  

datatype 'a extension = Infinity | Elt 'a

type_synonym N_ext = "nat extension"

instantiation  extension :: (plus) plus
begin
fun plus_extension where
"Infinity +  b  = Infinity "|
"a + Infinity = Infinity"|
"(Elt a) + (Elt b) = Elt (a + b)"
instance ..
end


record 'a top_dioid = "('a extension) ring" +
infinity :: " 'a extension" ("\<infinity>")






end