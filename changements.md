# Changements

This file contains a brief description of important modifications of the library HOL-Algebra. These changements comprise new results [NEW], renaming of lemmas [REN], suppression of redundent assumptions [SUP] or redefinitions [DEF].

## Modified Theories

### Congruence.thy

 * [NEW] locale partition.
 * [NEW] lemma (in partition) equivalence_from_partition.
 * [NEW] lemma (in partition) partition_coverture.
 * [NEW] lemma (in partition) disjoint_union.
 * [NEW] lemma partitionI.
 * [NEW] lemma (in partition) remove_elem.
 * [NEW] lemma disjoint_sum.
 * [NEW] lemma (in partition) disjoint_sum.
 * [NEW] lemma (in equivalence) classes_coverture.
 * [NEW] lemma (in equivalence) disjoint_union.
 * [NEW] lemma (in equivalence) partition_from_equivalence.
 * [NEW] lemma (in equivalence) disjoint_sum.


### Group.thy
 * [DEF] suppression of the symbol "≅" in the definition of iso.
 * [REN] from `lemma iso_refl` to `lemma iso_set_refl`, and suppression of the symbol "≅".
 * [REN] from `lemma iso_sym` to `lemma iso_set_sym`, and suppression of the symbol "≅".
 * [REN] from `lemma iso_trans` to `lemma iso_set_trans`, and suppression of the symbol "≅".
 * [REN] from `lemma DirProd_commute_iso` to `lemma DirProd_commute_iso_set`, and suppression of the symbol "≅".
 * [NEW] definition is_iso.
 * [NEW] utilisation of "≅" to caracterize is_iso.
 * [NEW] corollary iso_refl.
 * [NEW] corollary (in group) iso_sym.
 * [NEW] corollary (in group) iso_trans.
 * [NEW] corollary  DirProd_commute_iso.

### FiniteProduct.thy

 * [SUP] lemma foldSetD_closed.
 * [NEW] lemma foldSetD_backwards.
 * [NEW] proof of lemma foldSetD_determ_aux written in Isar and shorter than the first.
 

### Coset.thy

 * [REN] from `lemma lagrange` to `lemma lagrange_aux`.
 * [REN] from `lemma FactGroup_iso` to `lemma FactGroup_iso_set`, and suppression of the symbol "≅".
 * [NEW] lemma lagrange (Lagrange's theorem for both finite and infinite groups).
 * [NEW] corollry (in group_hom) FactGroup_iso.
 * [NEW] lemma l_coset_eq_set_mult.
 * [NEW] lemma r_coset_eq_set_mult.
 * [NEW] lemma (in subgroup) rcosets_not_empty.
 * [NEW] lemma (in group) diff_neutralizes.
 * [NEW] lemma (in monoid) set_mult_closed.
 * [NEW] lemma (in group) set_mult_assoc.
 * [NEW] lemma (in group) card_cosets_equal.

### AbelCoset.thy

 * [REN] from `theorem A_factGroup_iso` to `theorem A_FactGroup_iso_set`, and suppression of the symbol "≅".
 * [NEW] corollary (in abelian_group_hom) A_FactGroup_iso.


