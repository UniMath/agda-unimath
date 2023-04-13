# Cartesian products of higher groups

```agda
module higher-group-theory.cartesian-products-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import higher-group-theory.higher-groups

open import structured-types.cartesian-products-pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The Cartesian product of higher groups is also an higher group.

## Definition

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (R : ∞-Group l2)
  where

  product-∞-Group : ∞-Group (l1 ⊔ l2)
  pr1 product-∞-Group =
    product-Pointed-Type
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group R)
  pr2 product-∞-Group =
    is-0-connected-product
      ( classifying-type-∞-Group G)
      ( classifying-type-∞-Group R)
      ( is-0-connected-classifying-type-∞-Group G)
      ( is-0-connected-classifying-type-∞-Group R)
```

## Property

### The `type-∞-Group` of a product of a `∞-Group` is the product of the `type-∞-Group`

```agda
  equiv-type-∞-Group-product-∞-Group :
    ( type-∞-Group (product-∞-Group)) ≃
    ( type-∞-Group G × type-∞-Group R)
  equiv-type-∞-Group-product-∞-Group =
    equiv-pair-eq
      ( shape-∞-Group product-∞-Group)
      ( shape-∞-Group product-∞-Group)
```
