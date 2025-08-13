# Cartesian products of groups

```agda
module group-theory.cartesian-products-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.cartesian-products-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The
{{#concept "cartesian product" disambiguation="of groups" Agda=product-Group WDID=Q173740 WD="Cartesian product"}}
of two [groups](group-theory.groups.md) `G` and `H` consists of the
[product](foundation.cartesian-products.md) `G × H` of the underlying
[sets](foundation.sets.md) and the componentwise operation on it.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  monoid-product-Group : Monoid (l1 ⊔ l2)
  monoid-product-Group = product-Monoid (monoid-Group G) (monoid-Group H)

  semigroup-product-Group : Semigroup (l1 ⊔ l2)
  semigroup-product-Group = semigroup-Monoid monoid-product-Group

  set-product-Group : Set (l1 ⊔ l2)
  set-product-Group = set-Semigroup semigroup-product-Group

  type-product-Group : UU (l1 ⊔ l2)
  type-product-Group = type-Semigroup semigroup-product-Group

  is-set-type-product-Group : is-set type-product-Group
  is-set-type-product-Group = is-set-type-Semigroup semigroup-product-Group

  mul-product-Group : (x y : type-product-Group) → type-product-Group
  mul-product-Group = mul-Semigroup semigroup-product-Group

  associative-mul-product-Group :
    (x y z : type-product-Group) →
    Id
      ( mul-product-Group (mul-product-Group x y) z)
      ( mul-product-Group x (mul-product-Group y z))
  associative-mul-product-Group =
    associative-mul-Semigroup semigroup-product-Group

  unit-product-Group : type-product-Group
  unit-product-Group = unit-Monoid monoid-product-Group

  left-unit-law-mul-product-Group :
    (x : type-product-Group) → Id (mul-product-Group unit-product-Group x) x
  left-unit-law-mul-product-Group =
    left-unit-law-mul-Monoid monoid-product-Group

  right-unit-law-mul-product-Group :
    (x : type-product-Group) → Id (mul-product-Group x unit-product-Group) x
  right-unit-law-mul-product-Group =
    right-unit-law-mul-Monoid monoid-product-Group

  inv-product-Group : type-product-Group → type-product-Group
  pr1 (inv-product-Group (pair x y)) = inv-Group G x
  pr2 (inv-product-Group (pair x y)) = inv-Group H y

  left-inverse-law-product-Group :
    (x : type-product-Group) →
    Id (mul-product-Group (inv-product-Group x) x) unit-product-Group
  left-inverse-law-product-Group (pair x y) =
    eq-pair (left-inverse-law-mul-Group G x) (left-inverse-law-mul-Group H y)

  right-inverse-law-product-Group :
    (x : type-product-Group) →
    Id (mul-product-Group x (inv-product-Group x)) unit-product-Group
  right-inverse-law-product-Group (pair x y) =
    eq-pair (right-inverse-law-mul-Group G x) (right-inverse-law-mul-Group H y)

  product-Group : Group (l1 ⊔ l2)
  pr1 product-Group = semigroup-product-Group
  pr1 (pr1 (pr2 product-Group)) = unit-product-Group
  pr1 (pr2 (pr1 (pr2 product-Group))) = left-unit-law-mul-product-Group
  pr2 (pr2 (pr1 (pr2 product-Group))) = right-unit-law-mul-product-Group
  pr1 (pr2 (pr2 product-Group)) = inv-product-Group
  pr1 (pr2 (pr2 (pr2 product-Group))) = left-inverse-law-product-Group
  pr2 (pr2 (pr2 (pr2 product-Group))) = right-inverse-law-product-Group
```
