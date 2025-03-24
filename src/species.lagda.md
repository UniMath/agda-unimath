# Species

## Modules in the species namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import species.cartesian-exponents-species-of-types funext univalence public
open import species.cartesian-products-species-of-types funext univalence truncations public
open import species.cauchy-composition-species-of-types funext univalence public
open import species.cauchy-composition-species-of-types-in-subuniverses funext univalence public
open import species.cauchy-exponentials-species-of-types funext univalence truncations public
open import species.cauchy-exponentials-species-of-types-in-subuniverses funext univalence truncations public
open import species.cauchy-products-species-of-types funext univalence truncations public
open import species.cauchy-products-species-of-types-in-subuniverses funext univalence truncations public
open import species.cauchy-series-species-of-types funext univalence public
open import species.cauchy-series-species-of-types-in-subuniverses funext univalence public
open import species.composition-cauchy-series-species-of-types funext univalence public
open import species.composition-cauchy-series-species-of-types-in-subuniverses funext univalence public
open import species.coproducts-species-of-types funext univalence truncations public
open import species.coproducts-species-of-types-in-subuniverses funext univalence truncations public
open import species.cycle-index-series-species-of-types funext univalence truncations public
open import species.derivatives-species-of-types funext univalence truncations public
open import species.dirichlet-exponentials-species-of-types funext univalence truncations public
open import species.dirichlet-exponentials-species-of-types-in-subuniverses funext univalence truncations public
open import species.dirichlet-products-species-of-types funext univalence public
open import species.dirichlet-products-species-of-types-in-subuniverses funext univalence public
open import species.dirichlet-series-species-of-finite-inhabited-types funext univalence truncations public
open import species.dirichlet-series-species-of-types funext univalence public
open import species.dirichlet-series-species-of-types-in-subuniverses funext univalence public
open import species.equivalences-species-of-types funext univalence public
open import species.equivalences-species-of-types-in-subuniverses funext univalence public
open import species.exponentials-cauchy-series-of-types funext univalence truncations public
open import species.exponentials-cauchy-series-of-types-in-subuniverses funext univalence truncations public
open import species.hasse-weil-species funext univalence truncations public
open import species.morphisms-finite-species funext univalence truncations public
open import species.morphisms-species-of-types funext univalence truncations public
open import species.pointing-species-of-types funext univalence public
open import species.precategory-of-finite-species funext univalence truncations public
open import species.products-cauchy-series-species-of-types funext univalence truncations public
open import species.products-cauchy-series-species-of-types-in-subuniverses funext univalence truncations public
open import species.products-dirichlet-series-species-of-finite-inhabited-types funext univalence truncations public
open import species.products-dirichlet-series-species-of-types funext univalence public
open import species.products-dirichlet-series-species-of-types-in-subuniverses funext univalence truncations public
open import species.small-cauchy-composition-species-of-finite-inhabited-types funext univalence truncations public
open import species.small-cauchy-composition-species-of-types-in-subuniverses funext univalence truncations public
open import species.species-of-finite-inhabited-types funext univalence truncations public
open import species.species-of-finite-types funext univalence truncations public
open import species.species-of-inhabited-types funext univalence truncations public
open import species.species-of-types funext univalence public
open import species.species-of-types-in-subuniverses funext univalence public
open import species.unit-cauchy-composition-species-of-types funext univalence public
open import species.unit-cauchy-composition-species-of-types-in-subuniverses funext univalence public
open import species.unlabeled-structures-species funext univalence truncations public
```
