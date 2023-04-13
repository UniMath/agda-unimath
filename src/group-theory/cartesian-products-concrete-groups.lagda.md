# Cartesian products of concrete groups

```agda
module group-theory.cartesian-products-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups

open import higher-group-theory.cartesian-products-higher-groups
open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The cartesian product of two concrete groups is defined as the cartesian product
of their underlying `∞-group`

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (R : Concrete-Group l2)
  where

  product-Concrete-Group : Concrete-Group (l1 ⊔ l2)
  pr1 product-Concrete-Group =
    product-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group R)
  pr2 product-Concrete-Group =
    is-set-equiv
      ( type-∞-Group (pr1 G) ×
        type-∞-Group (pr1 R))
      ( equiv-type-∞-Group-product-∞-Group
          ( ∞-group-Concrete-Group G)
          ( ∞-group-Concrete-Group R))
      ( is-set-prod
          ( is-set-type-Concrete-Group G)
          ( is-set-type-Concrete-Group R))
```

## Property

```agda
  equiv-type-Concrete-Group-produt-Concrete-Group :
    type-Concrete-Group product-Concrete-Group ≃
    ( type-Concrete-Group G × type-Concrete-Group R)
  equiv-type-Concrete-Group-produt-Concrete-Group =
    equiv-type-∞-Group-product-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group R)
```
