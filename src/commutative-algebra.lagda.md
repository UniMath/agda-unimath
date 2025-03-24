# Commutative algebra

## Modules in the commutative algebra namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import commutative-algebra.binomial-theorem-commutative-rings funext univalence truncations public
open import commutative-algebra.binomial-theorem-commutative-semirings funext univalence truncations public
open import commutative-algebra.boolean-rings funext univalence truncations public
open import commutative-algebra.category-of-commutative-rings funext univalence truncations public
open import commutative-algebra.commutative-rings funext univalence truncations public
open import commutative-algebra.commutative-semirings funext univalence truncations public
open import commutative-algebra.dependent-products-commutative-rings funext univalence truncations public
open import commutative-algebra.dependent-products-commutative-semirings funext univalence truncations public
open import commutative-algebra.discrete-fields funext univalence truncations public
open import commutative-algebra.eisenstein-integers funext univalence truncations public
open import commutative-algebra.euclidean-domains funext univalence truncations public
open import commutative-algebra.full-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.function-commutative-rings funext univalence truncations public
open import commutative-algebra.function-commutative-semirings funext univalence truncations public
open import commutative-algebra.gaussian-integers funext univalence truncations public
open import commutative-algebra.groups-of-units-commutative-rings funext univalence truncations public
open import commutative-algebra.homomorphisms-commutative-rings funext univalence truncations public
open import commutative-algebra.homomorphisms-commutative-semirings funext univalence truncations public
open import commutative-algebra.ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.ideals-commutative-semirings funext univalence truncations public
open import commutative-algebra.ideals-generated-by-subsets-commutative-rings funext univalence truncations public
open import commutative-algebra.integer-multiples-of-elements-commutative-rings funext univalence truncations public
open import commutative-algebra.integral-domains funext univalence truncations public
open import commutative-algebra.intersections-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.intersections-radical-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.invertible-elements-commutative-rings funext univalence truncations public
open import commutative-algebra.isomorphisms-commutative-rings funext univalence truncations public
open import commutative-algebra.joins-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.joins-radical-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.local-commutative-rings funext univalence truncations public
open import commutative-algebra.maximal-ideals-commutative-rings public
open import commutative-algebra.multiples-of-elements-commutative-rings funext univalence truncations public
open import commutative-algebra.nilradical-commutative-rings funext univalence truncations public
open import commutative-algebra.nilradicals-commutative-semirings funext univalence truncations public
open import commutative-algebra.poset-of-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.poset-of-radical-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.powers-of-elements-commutative-rings funext univalence truncations public
open import commutative-algebra.powers-of-elements-commutative-semirings funext univalence truncations public
open import commutative-algebra.precategory-of-commutative-rings funext univalence truncations public
open import commutative-algebra.precategory-of-commutative-semirings funext univalence truncations public
open import commutative-algebra.prime-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.products-commutative-rings funext univalence truncations public
open import commutative-algebra.products-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.products-radical-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.products-subsets-commutative-rings funext univalence truncations public
open import commutative-algebra.radical-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.radical-ideals-generated-by-subsets-commutative-rings funext univalence truncations public
open import commutative-algebra.radicals-of-ideals-commutative-rings funext univalence truncations public
open import commutative-algebra.subsets-commutative-rings funext univalence truncations public
open import commutative-algebra.subsets-commutative-semirings funext univalence truncations public
open import commutative-algebra.sums-commutative-rings funext univalence truncations public
open import commutative-algebra.sums-commutative-semirings funext univalence truncations public
open import commutative-algebra.transporting-commutative-ring-structure-isomorphisms-abelian-groups funext univalence truncations public
open import commutative-algebra.trivial-commutative-rings funext univalence truncations public
open import commutative-algebra.zariski-locale funext univalence truncations public
open import commutative-algebra.zariski-topology funext univalence truncations public
```
