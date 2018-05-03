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


### FiniteProd.thy

 * [SUP] lemma foldSetD_closed.
 

### Coset.thy

 * [REN] from `lemma lagrange` to `lemma lagrange_aux`.
 * [NEW] lemma lagrange (Lagrange's theorem for both finite and infinite groups).
 * [NEW] lemma (in subgroup) rcosets_not_empty.
 * [NEW] lemma (in group) diff_neutralizes.
 * [NEW] lemma (in monoid) set_mult_closed.
 * [NEW] lemma (in group) set_mult_assoc.
 * [NEW] lemma (in group) card_cosets_equal.
