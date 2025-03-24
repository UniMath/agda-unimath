# Ring theory

## Modules in the ring theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import ring-theory.additive-orders-of-elements-rings funext univalence truncations public
open import ring-theory.algebras-rings funext univalence truncations public
open import ring-theory.binomial-theorem-rings funext univalence truncations public
open import ring-theory.binomial-theorem-semirings funext univalence truncations public
open import ring-theory.category-of-cyclic-rings funext univalence truncations public
open import ring-theory.category-of-rings funext univalence truncations public
open import ring-theory.central-elements-rings funext univalence truncations public
open import ring-theory.central-elements-semirings funext univalence truncations public
open import ring-theory.characteristics-rings funext univalence truncations public
open import ring-theory.commuting-elements-rings funext univalence truncations public
open import ring-theory.congruence-relations-rings funext univalence truncations public
open import ring-theory.congruence-relations-semirings funext univalence truncations public
open import ring-theory.cyclic-rings funext univalence truncations public
open import ring-theory.dependent-products-rings funext univalence truncations public
open import ring-theory.dependent-products-semirings funext univalence truncations public
open import ring-theory.division-rings funext univalence truncations public
open import ring-theory.free-rings-with-one-generator funext univalence truncations public
open import ring-theory.full-ideals-rings funext univalence truncations public
open import ring-theory.function-rings funext univalence truncations public
open import ring-theory.function-semirings funext univalence truncations public
open import ring-theory.generating-elements-rings funext univalence truncations public
open import ring-theory.groups-of-units-rings funext univalence truncations public
open import ring-theory.homomorphisms-cyclic-rings funext univalence truncations public
open import ring-theory.homomorphisms-rings funext univalence truncations public
open import ring-theory.homomorphisms-semirings funext univalence truncations public
open import ring-theory.ideals-generated-by-subsets-rings funext univalence truncations public
open import ring-theory.ideals-rings funext univalence truncations public
open import ring-theory.ideals-semirings funext univalence truncations public
open import ring-theory.idempotent-elements-rings funext univalence truncations public
open import ring-theory.initial-rings funext univalence truncations public
open import ring-theory.integer-multiples-of-elements-rings funext univalence truncations public
open import ring-theory.intersections-ideals-rings funext univalence truncations public
open import ring-theory.intersections-ideals-semirings funext univalence truncations public
open import ring-theory.invariant-basis-property-rings funext univalence truncations public
open import ring-theory.invertible-elements-rings funext univalence truncations public
open import ring-theory.isomorphisms-rings funext univalence truncations public
open import ring-theory.joins-ideals-rings funext univalence truncations public
open import ring-theory.joins-left-ideals-rings funext univalence truncations public
open import ring-theory.joins-right-ideals-rings funext univalence truncations public
open import ring-theory.kernels-of-ring-homomorphisms funext univalence truncations public
open import ring-theory.left-ideals-generated-by-subsets-rings funext univalence truncations public
open import ring-theory.left-ideals-rings funext univalence truncations public
open import ring-theory.local-rings funext univalence truncations public
open import ring-theory.localizations-rings funext univalence truncations public
open import ring-theory.maximal-ideals-rings public
open import ring-theory.modules-rings funext univalence truncations public
open import ring-theory.multiples-of-elements-rings funext univalence truncations public
open import ring-theory.multiplicative-orders-of-units-rings public
open import ring-theory.nil-ideals-rings funext univalence truncations public
open import ring-theory.nilpotent-elements-rings funext univalence truncations public
open import ring-theory.nilpotent-elements-semirings funext univalence truncations public
open import ring-theory.opposite-rings funext univalence truncations public
open import ring-theory.poset-of-cyclic-rings funext univalence truncations public
open import ring-theory.poset-of-ideals-rings funext univalence truncations public
open import ring-theory.poset-of-left-ideals-rings funext univalence truncations public
open import ring-theory.poset-of-right-ideals-rings funext univalence truncations public
open import ring-theory.powers-of-elements-rings funext univalence truncations public
open import ring-theory.powers-of-elements-semirings funext univalence truncations public
open import ring-theory.precategory-of-rings funext univalence truncations public
open import ring-theory.precategory-of-semirings funext univalence truncations public
open import ring-theory.products-ideals-rings funext univalence truncations public
open import ring-theory.products-left-ideals-rings funext univalence truncations public
open import ring-theory.products-right-ideals-rings funext univalence truncations public
open import ring-theory.products-rings funext univalence truncations public
open import ring-theory.products-subsets-rings funext univalence truncations public
open import ring-theory.quotient-rings funext univalence truncations public
open import ring-theory.radical-ideals-rings funext univalence truncations public
open import ring-theory.right-ideals-generated-by-subsets-rings funext univalence truncations public
open import ring-theory.right-ideals-rings funext univalence truncations public
open import ring-theory.rings funext univalence truncations public
open import ring-theory.semirings funext univalence truncations public
open import ring-theory.subsets-rings funext univalence truncations public
open import ring-theory.subsets-semirings funext univalence truncations public
open import ring-theory.sums-rings funext univalence truncations public
open import ring-theory.sums-semirings funext univalence truncations public
open import ring-theory.transporting-ring-structure-along-isomorphisms-abelian-groups funext univalence truncations public
open import ring-theory.trivial-rings funext univalence truncations public
```
