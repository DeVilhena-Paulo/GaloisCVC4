theory Topological_Dioid
  imports Dioid 
begin

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

context dioid begin


interpretation a :
order_topology "dioid_canonic_order D" "\<lambda> a b. a \<le>\<^bsub>D\<^esub> b \<and> a \<noteq> b"
 "generate_topology (range (\<lambda>a. {x. x \<le>\<^bsub>D\<^esub> a}) \<union> range (\<lambda>a. {x. a \<le>\<^bsub>D\<^esub> x}))"
proof
  show "\<And>x y. (x \<le>\<^bsub>D\<^esub> y \<and> x \<noteq> y) = (x \<le>\<^bsub>D\<^esub> y \<and> \<not> y \<le>\<^bsub>D\<^esub> x)"
    unfolding factor_def
proof

interpretation monoid_monoid : monoid "\<lparr>carrier = {1::nat}, mult = op *, one = 1::nat\<rparr>" 
proof (intro monoid.intro)
  show "\<And>x y. x \<in> carrier \<lparr>carrier = {1}, mult = op *, one = 1\<rparr> \<Longrightarrow>
        y \<in> carrier \<lparr>carrier = {1}, mult = op *, one = 1\<rparr> \<Longrightarrow>
        x \<otimes>\<^bsub>\<lparr>carrier = {1}, mult = op *, one = 1\<rparr>\<^esub> y \<in> carrier \<lparr>carrier = {1}, mult = op *,one = 1\<rparr>"
    apply simp apply auto 



record 'a top_dioid = "('a extension) ring" +
infinity :: " 'a extension" ("\<infinity>")



end