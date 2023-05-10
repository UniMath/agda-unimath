# Cartesian products of types equipped with endomorphisms

```agda
module structured-types.cartesian-products-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The cartesian product of `(A , f)` and `(B , g)` is defined as `(A × B , f × g)`

## Definitions

```agda
product-Endo :
  {l1 l2 : Level} → Endo l1 → Endo l2 → Endo (l1 ⊔ l2)
product-Endo A B =
  (type-Endo A × type-Endo B) ,
  map-prod (endomorphism-Endo A) (endomorphism-Endo B)
```
