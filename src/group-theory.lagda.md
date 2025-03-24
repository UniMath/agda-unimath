# Group theory

## Modules in the group theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import group-theory.abelian-groups funext univalence truncations public
open import group-theory.abelianization-groups funext univalence truncations public
open import group-theory.addition-homomorphisms-abelian-groups funext univalence truncations public
open import group-theory.automorphism-groups funext univalence truncations public
open import group-theory.cartesian-products-abelian-groups funext univalence truncations public
open import group-theory.cartesian-products-concrete-groups funext univalence truncations public
open import group-theory.cartesian-products-groups funext univalence truncations public
open import group-theory.cartesian-products-monoids funext univalence truncations public
open import group-theory.cartesian-products-semigroups funext univalence public
open import group-theory.category-of-abelian-groups funext univalence truncations public
open import group-theory.category-of-concrete-groups public
open import group-theory.category-of-group-actions funext univalence truncations public
open import group-theory.category-of-groups funext univalence truncations public
open import group-theory.category-of-orbits-groups funext univalence truncations public
open import group-theory.category-of-semigroups funext univalence truncations public
open import group-theory.cayleys-theorem funext univalence truncations public
open import group-theory.centers-groups funext univalence truncations public
open import group-theory.centers-monoids funext univalence truncations public
open import group-theory.centers-semigroups funext univalence truncations public
open import group-theory.central-elements-groups funext univalence truncations public
open import group-theory.central-elements-monoids funext univalence truncations public
open import group-theory.central-elements-semigroups funext univalence public
open import group-theory.centralizer-subgroups funext univalence truncations public
open import group-theory.characteristic-subgroups funext univalence truncations public
open import group-theory.commutative-monoids funext univalence truncations public
open import group-theory.commutator-subgroups funext univalence truncations public
open import group-theory.commutators-of-elements-groups funext univalence truncations public
open import group-theory.commuting-elements-groups funext univalence truncations public
open import group-theory.commuting-elements-monoids funext univalence truncations public
open import group-theory.commuting-elements-semigroups funext univalence public
open import group-theory.commuting-squares-of-group-homomorphisms funext univalence truncations public
open import group-theory.concrete-group-actions funext univalence truncations public
open import group-theory.concrete-groups funext univalence truncations public
open import group-theory.concrete-monoids funext univalence truncations public
open import group-theory.congruence-relations-abelian-groups funext univalence truncations public
open import group-theory.congruence-relations-commutative-monoids funext univalence truncations public
open import group-theory.congruence-relations-groups funext univalence truncations public
open import group-theory.congruence-relations-monoids funext univalence truncations public
open import group-theory.congruence-relations-semigroups funext univalence truncations public
open import group-theory.conjugation funext univalence truncations public
open import group-theory.conjugation-concrete-groups funext univalence truncations public
open import group-theory.contravariant-pushforward-concrete-group-actions funext univalence truncations public
open import group-theory.cores-monoids funext univalence truncations public
open import group-theory.cyclic-groups funext univalence truncations public
open import group-theory.decidable-subgroups funext univalence truncations public
open import group-theory.dependent-products-abelian-groups funext univalence truncations public
open import group-theory.dependent-products-commutative-monoids funext univalence truncations public
open import group-theory.dependent-products-groups funext univalence truncations public
open import group-theory.dependent-products-monoids funext univalence truncations public
open import group-theory.dependent-products-semigroups funext univalence public
open import group-theory.dihedral-group-construction funext univalence truncations public
open import group-theory.dihedral-groups funext univalence truncations public
open import group-theory.e8-lattice funext univalence truncations public
open import group-theory.elements-of-finite-order-groups funext univalence truncations public
open import group-theory.embeddings-abelian-groups funext univalence truncations public
open import group-theory.embeddings-groups funext univalence truncations public
open import group-theory.endomorphism-rings-abelian-groups funext univalence truncations public
open import group-theory.epimorphisms-groups funext univalence truncations public
open import group-theory.equivalences-concrete-group-actions funext univalence truncations public
open import group-theory.equivalences-concrete-groups funext univalence truncations public
open import group-theory.equivalences-group-actions funext univalence truncations public
open import group-theory.equivalences-semigroups funext univalence truncations public
open import group-theory.exponents-abelian-groups funext univalence truncations public
open import group-theory.exponents-groups funext univalence truncations public
open import group-theory.free-concrete-group-actions funext univalence truncations public
open import group-theory.free-groups-with-one-generator funext univalence truncations public
open import group-theory.full-subgroups funext univalence truncations public
open import group-theory.full-subsemigroups funext univalence truncations public
open import group-theory.function-abelian-groups funext univalence truncations public
open import group-theory.function-commutative-monoids funext univalence truncations public
open import group-theory.function-groups funext univalence truncations public
open import group-theory.function-monoids funext univalence truncations public
open import group-theory.function-semigroups funext univalence public
open import group-theory.functoriality-quotient-groups funext univalence truncations public
open import group-theory.furstenberg-groups funext univalence truncations public
open import group-theory.generating-elements-groups funext univalence truncations public
open import group-theory.generating-sets-groups funext univalence truncations public
open import group-theory.group-actions funext univalence truncations public
open import group-theory.groups funext univalence truncations public
open import group-theory.homomorphisms-abelian-groups funext univalence truncations public
open import group-theory.homomorphisms-commutative-monoids funext univalence truncations public
open import group-theory.homomorphisms-concrete-group-actions funext univalence truncations public
open import group-theory.homomorphisms-concrete-groups funext univalence truncations public
open import group-theory.homomorphisms-generated-subgroups funext univalence truncations public
open import group-theory.homomorphisms-group-actions funext univalence truncations public
open import group-theory.homomorphisms-groups funext univalence truncations public
open import group-theory.homomorphisms-groups-equipped-with-normal-subgroups funext univalence truncations public
open import group-theory.homomorphisms-monoids funext univalence truncations public
open import group-theory.homomorphisms-semigroups funext univalence truncations public
open import group-theory.homotopy-automorphism-groups funext univalence truncations public
open import group-theory.images-of-group-homomorphisms funext univalence truncations public
open import group-theory.images-of-semigroup-homomorphisms funext univalence truncations public
open import group-theory.integer-multiples-of-elements-abelian-groups funext univalence truncations public
open import group-theory.integer-powers-of-elements-groups funext univalence truncations public
open import group-theory.intersections-subgroups-abelian-groups funext univalence truncations public
open import group-theory.intersections-subgroups-groups funext univalence truncations public
open import group-theory.inverse-semigroups funext univalence public
open import group-theory.invertible-elements-monoids funext univalence truncations public
open import group-theory.isomorphisms-abelian-groups funext univalence truncations public
open import group-theory.isomorphisms-concrete-groups funext univalence truncations public
open import group-theory.isomorphisms-group-actions funext univalence truncations public
open import group-theory.isomorphisms-groups funext univalence truncations public
open import group-theory.isomorphisms-monoids funext univalence truncations public
open import group-theory.isomorphisms-semigroups funext univalence truncations public
open import group-theory.iterated-cartesian-products-concrete-groups funext univalence truncations public
open import group-theory.kernels-homomorphisms-abelian-groups funext univalence truncations public
open import group-theory.kernels-homomorphisms-concrete-groups funext univalence truncations public
open import group-theory.kernels-homomorphisms-groups funext univalence truncations public
open import group-theory.large-semigroups funext univalence public
open import group-theory.loop-groups-sets funext univalence truncations public
open import group-theory.mere-equivalences-concrete-group-actions funext univalence truncations public
open import group-theory.mere-equivalences-group-actions funext univalence truncations public
open import group-theory.minkowski-multiplication-commutative-monoids funext univalence truncations public
open import group-theory.minkowski-multiplication-monoids funext univalence truncations public
open import group-theory.minkowski-multiplication-semigroups funext univalence truncations public
open import group-theory.monoid-actions funext univalence truncations public
open import group-theory.monoids funext univalence truncations public
open import group-theory.monomorphisms-concrete-groups funext univalence truncations public
open import group-theory.monomorphisms-groups funext univalence truncations public
open import group-theory.multiples-of-elements-abelian-groups funext univalence truncations public
open import group-theory.nontrivial-groups funext univalence truncations public
open import group-theory.normal-closures-subgroups funext univalence truncations public
open import group-theory.normal-cores-subgroups funext univalence truncations public
open import group-theory.normal-subgroups funext univalence truncations public
open import group-theory.normal-subgroups-concrete-groups funext univalence truncations public
open import group-theory.normal-submonoids funext univalence truncations public
open import group-theory.normal-submonoids-commutative-monoids funext univalence truncations public
open import group-theory.normalizer-subgroups funext univalence truncations public
open import group-theory.nullifying-group-homomorphisms funext univalence truncations public
open import group-theory.opposite-groups funext univalence truncations public
open import group-theory.opposite-semigroups funext univalence public
open import group-theory.orbit-stabilizer-theorem-concrete-groups funext univalence truncations public
open import group-theory.orbits-concrete-group-actions funext univalence truncations public
open import group-theory.orbits-group-actions funext univalence truncations public
open import group-theory.orders-of-elements-groups funext univalence truncations public
open import group-theory.perfect-cores funext univalence truncations public
open import group-theory.perfect-groups funext univalence truncations public
open import group-theory.perfect-subgroups funext univalence truncations public
open import group-theory.powers-of-elements-commutative-monoids funext univalence truncations public
open import group-theory.powers-of-elements-groups funext univalence truncations public
open import group-theory.powers-of-elements-monoids funext univalence truncations public
open import group-theory.precategory-of-commutative-monoids funext univalence truncations public
open import group-theory.precategory-of-concrete-groups funext univalence truncations public
open import group-theory.precategory-of-group-actions funext univalence truncations public
open import group-theory.precategory-of-groups funext univalence truncations public
open import group-theory.precategory-of-monoids funext univalence truncations public
open import group-theory.precategory-of-orbits-monoid-actions funext univalence truncations public
open import group-theory.precategory-of-semigroups funext univalence truncations public
open import group-theory.principal-group-actions funext univalence truncations public
open import group-theory.principal-torsors-concrete-groups funext univalence truncations public
open import group-theory.products-of-elements-monoids funext univalence truncations public
open import group-theory.products-of-tuples-of-elements-commutative-monoids funext univalence truncations public
open import group-theory.pullbacks-subgroups funext univalence truncations public
open import group-theory.pullbacks-subsemigroups funext univalence truncations public
open import group-theory.quotient-groups funext univalence truncations public
open import group-theory.quotient-groups-concrete-groups funext univalence truncations public
open import group-theory.quotients-abelian-groups funext univalence truncations public
open import group-theory.rational-commutative-monoids funext univalence truncations public
open import group-theory.representations-monoids-precategories funext univalence truncations public
open import group-theory.saturated-congruence-relations-commutative-monoids funext univalence truncations public
open import group-theory.saturated-congruence-relations-monoids funext univalence truncations public
open import group-theory.semigroups funext univalence public
open import group-theory.sheargroups funext univalence public
open import group-theory.shriek-concrete-group-actions funext univalence truncations public
open import group-theory.stabilizer-groups funext univalence truncations public
open import group-theory.stabilizer-groups-concrete-group-actions funext univalence truncations public
open import group-theory.subgroups funext univalence truncations public
open import group-theory.subgroups-abelian-groups funext univalence truncations public
open import group-theory.subgroups-concrete-groups funext univalence truncations public
open import group-theory.subgroups-generated-by-elements-groups funext univalence truncations public
open import group-theory.subgroups-generated-by-families-of-elements-groups funext univalence truncations public
open import group-theory.subgroups-generated-by-subsets-groups funext univalence truncations public
open import group-theory.submonoids funext univalence truncations public
open import group-theory.submonoids-commutative-monoids funext univalence truncations public
open import group-theory.subsemigroups funext univalence truncations public
open import group-theory.subsets-abelian-groups funext univalence truncations public
open import group-theory.subsets-commutative-monoids funext univalence truncations public
open import group-theory.subsets-groups funext univalence truncations public
open import group-theory.subsets-monoids funext univalence truncations public
open import group-theory.subsets-semigroups funext univalence truncations public
open import group-theory.substitution-functor-concrete-group-actions funext univalence truncations public
open import group-theory.substitution-functor-group-actions funext univalence truncations public
open import group-theory.surjective-group-homomorphisms funext univalence truncations public
open import group-theory.surjective-semigroup-homomorphisms funext univalence truncations public
open import group-theory.symmetric-concrete-groups funext univalence truncations public
open import group-theory.symmetric-groups funext univalence truncations public
open import group-theory.torsion-elements-groups funext univalence truncations public
open import group-theory.torsion-free-groups funext univalence truncations public
open import group-theory.torsors funext univalence truncations public
open import group-theory.transitive-concrete-group-actions funext univalence truncations public
open import group-theory.transitive-group-actions funext univalence truncations public
open import group-theory.trivial-concrete-groups funext univalence truncations public
open import group-theory.trivial-group-homomorphisms funext univalence truncations public
open import group-theory.trivial-groups funext univalence truncations public
open import group-theory.trivial-subgroups funext univalence truncations public
open import group-theory.unordered-tuples-of-elements-commutative-monoids funext univalence truncations public
open import group-theory.wild-representations-monoids funext univalence truncations public
```
