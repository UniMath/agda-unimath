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

The **cartesian product** of two
[types equipped with an endomorphism](structured-types.types-equipped-with-endomorphisms.md)
`(A , f)` and `(B , g)` is defined as `(A × B , f × g)`

## Definitions

```agda
product-Type-With-Endomorphism :
  {l1 l2 : Level} →
  Type-With-Endomorphism l1 → Type-With-Endomorphism l2 →
  Type-With-Endomorphism (l1 ⊔ l2)
pr1 (product-Type-With-Endomorphism A B) =
  type-Type-With-Endomorphism A × type-Type-With-Endomorphism B
pr2 (product-Type-With-Endomorphism A B) =
  map-prod
    ( endomorphism-Type-With-Endomorphism A)
    ( endomorphism-Type-With-Endomorphism B)
```
