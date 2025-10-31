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

The
{{#concept "cartesian product" Disambiguation="of two types equipped with endomorphisms" Agda=product-Type-With-Endomorphism}}
of two
[types equipped with endomorphisms](structured-types.types-equipped-with-endomorphisms.md)
`(A , f)` and `(B , g)` is defined as `(A × B , f × g)`

## Definitions

```agda
module _
  {l1 l2 : Level}
  (A : Type-With-Endomorphism l1) (B : Type-With-Endomorphism l2)
  where

  type-product-Type-With-Endomorphism : UU (l1 ⊔ l2)
  type-product-Type-With-Endomorphism =
    type-Type-With-Endomorphism A × type-Type-With-Endomorphism B

  endomorphism-product-Type-With-Endomorphism :
    type-product-Type-With-Endomorphism → type-product-Type-With-Endomorphism
  endomorphism-product-Type-With-Endomorphism =
    map-product
      ( endomorphism-Type-With-Endomorphism A)
      ( endomorphism-Type-With-Endomorphism B)

  product-Type-With-Endomorphism :
    Type-With-Endomorphism (l1 ⊔ l2)
  pr1 product-Type-With-Endomorphism =
    type-product-Type-With-Endomorphism
  pr2 product-Type-With-Endomorphism =
    endomorphism-product-Type-With-Endomorphism
```
