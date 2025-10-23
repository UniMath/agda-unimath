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
open import foundation.mere-equality
open import foundation.propositions
open import foundation.universe-levels

open import higher-group-theory.higher-groups

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The **cartesian product** of
[higher groups](higher-group-theory.higher-groups.md) is also a higher group.

## Definition

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : ∞-Group l2)
  where

  product-∞-Group : ∞-Group (l1 ⊔ l2)
  pr1 product-∞-Group =
    product-Pointed-Type
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
  pr2 product-∞-Group =
    is-0-connected-product
      ( classifying-type-∞-Group G)
      ( classifying-type-∞-Group H)
      ( is-0-connected-classifying-type-∞-Group G)
      ( is-0-connected-classifying-type-∞-Group H)

  classifying-pointed-type-product-∞-Group : Pointed-Type (l1 ⊔ l2)
  classifying-pointed-type-product-∞-Group = pr1 product-∞-Group

  classifying-type-product-∞-Group : UU (l1 ⊔ l2)
  classifying-type-product-∞-Group =
    type-Pointed-Type classifying-pointed-type-product-∞-Group

  shape-product-∞-Group : classifying-type-product-∞-Group
  shape-product-∞-Group =
    point-Pointed-Type classifying-pointed-type-product-∞-Group

  is-0-connected-classifying-type-product-∞-Group :
    is-0-connected classifying-type-product-∞-Group
  is-0-connected-classifying-type-product-∞-Group = pr2 product-∞-Group

  mere-eq-classifying-type-product-∞-Group :
    (X Y : classifying-type-product-∞-Group) → mere-eq X Y
  mere-eq-classifying-type-product-∞-Group =
    mere-eq-is-0-connected
      is-0-connected-classifying-type-product-∞-Group

  elim-prop-classifying-type-product-∞-Group :
    {l2 : Level} (P : classifying-type-product-∞-Group → Prop l2) →
    type-Prop (P shape-product-∞-Group) →
    ((X : classifying-type-product-∞-Group) → type-Prop (P X))
  elim-prop-classifying-type-product-∞-Group =
    apply-dependent-universal-property-is-0-connected
      shape-product-∞-Group
      is-0-connected-classifying-type-product-∞-Group

  type-product-∞-Group : UU (l1 ⊔ l2)
  type-product-∞-Group = type-Ω classifying-pointed-type-product-∞-Group

  unit-product-∞-Group : type-product-∞-Group
  unit-product-∞-Group = refl-Ω classifying-pointed-type-product-∞-Group

  mul-product-∞-Group : (x y : type-product-∞-Group) → type-product-∞-Group
  mul-product-∞-Group = mul-Ω classifying-pointed-type-product-∞-Group

  assoc-mul-product-∞-Group :
    (x y z : type-product-∞-Group) →
    mul-product-∞-Group (mul-product-∞-Group x y) z ＝
    mul-product-∞-Group x (mul-product-∞-Group y z)
  assoc-mul-product-∞-Group =
    associative-mul-Ω classifying-pointed-type-product-∞-Group

  left-unit-law-mul-product-∞-Group :
    (x : type-product-∞-Group) →
    mul-product-∞-Group unit-product-∞-Group x ＝ x
  left-unit-law-mul-product-∞-Group =
    left-unit-law-mul-Ω classifying-pointed-type-product-∞-Group

  right-unit-law-mul-product-∞-Group :
    (y : type-product-∞-Group) →
    mul-product-∞-Group y unit-product-∞-Group ＝ y
  right-unit-law-mul-product-∞-Group =
    right-unit-law-mul-Ω classifying-pointed-type-product-∞-Group

  coherence-unit-laws-mul-product-∞-Group :
    left-unit-law-mul-product-∞-Group unit-product-∞-Group ＝
    right-unit-law-mul-product-∞-Group unit-product-∞-Group
  coherence-unit-laws-mul-product-∞-Group = refl

  inv-product-∞-Group : type-product-∞-Group → type-product-∞-Group
  inv-product-∞-Group = inv-Ω classifying-pointed-type-product-∞-Group

  left-inverse-law-mul-product-∞-Group :
    (x : type-product-∞-Group) →
    mul-product-∞-Group (inv-product-∞-Group x) x ＝ unit-product-∞-Group
  left-inverse-law-mul-product-∞-Group =
    left-inverse-law-mul-Ω classifying-pointed-type-product-∞-Group

  right-inverse-law-mul-product-∞-Group :
    (x : type-product-∞-Group) →
    mul-product-∞-Group x (inv-product-∞-Group x) ＝ unit-product-∞-Group
  right-inverse-law-mul-product-∞-Group =
    right-inverse-law-mul-Ω classifying-pointed-type-product-∞-Group
```

## Properties

### The underlying type of a product of higher groups is the product of their underlying types

```agda
  equiv-type-∞-Group-product-∞-Group :
    type-product-∞-Group ≃
    ( type-∞-Group G × type-∞-Group H)
  equiv-type-∞-Group-product-∞-Group =
    equiv-pair-eq shape-product-∞-Group shape-product-∞-Group
```
