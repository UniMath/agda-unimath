# Finite algebra

## Modules in the finite algebra namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module finite-algebra
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import finite-algebra.commutative-finite-rings funext univalence truncations public
open import finite-algebra.dependent-products-commutative-finite-rings funext univalence truncations public
open import finite-algebra.dependent-products-finite-rings funext univalence truncations public
open import finite-algebra.finite-fields funext univalence truncations public
open import finite-algebra.finite-rings funext univalence truncations public
open import finite-algebra.homomorphisms-commutative-finite-rings funext univalence truncations public
open import finite-algebra.homomorphisms-finite-rings funext univalence truncations public
open import finite-algebra.products-commutative-finite-rings funext univalence truncations public
open import finite-algebra.products-finite-rings funext univalence truncations public
open import finite-algebra.semisimple-commutative-finite-rings funext univalence truncations public
```
