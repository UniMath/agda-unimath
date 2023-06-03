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

The cartesian product of two groups `G` and `H` has the product of the
underlying sets of `G` and `H` as its underlying type, and is equipped with
pointwise multiplication.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  monoid-prod-Group : Monoid (l1 ⊔ l2)
  monoid-prod-Group = prod-Monoid (monoid-Group G) (monoid-Group H)

  semigroup-prod-Group : Semigroup (l1 ⊔ l2)
  semigroup-prod-Group = semigroup-Monoid monoid-prod-Group

  set-prod-Group : Set (l1 ⊔ l2)
  set-prod-Group = set-Semigroup semigroup-prod-Group

  type-prod-Group : UU (l1 ⊔ l2)
  type-prod-Group = type-Semigroup semigroup-prod-Group

  is-set-type-prod-Group : is-set type-prod-Group
  is-set-type-prod-Group = is-set-type-Semigroup semigroup-prod-Group

  mul-prod-Group : (x y : type-prod-Group) → type-prod-Group
  mul-prod-Group = mul-Semigroup semigroup-prod-Group

  associative-mul-prod-Group :
    (x y z : type-prod-Group) →
    Id
      ( mul-prod-Group (mul-prod-Group x y) z)
      ( mul-prod-Group x (mul-prod-Group y z))
  associative-mul-prod-Group = associative-mul-Semigroup semigroup-prod-Group

  unit-prod-Group : type-prod-Group
  unit-prod-Group = unit-Monoid monoid-prod-Group

  left-unit-law-mul-prod-Group :
    (x : type-prod-Group) → Id (mul-prod-Group unit-prod-Group x) x
  left-unit-law-mul-prod-Group = left-unit-law-mul-Monoid monoid-prod-Group

  right-unit-law-mul-prod-Group :
    (x : type-prod-Group) → Id (mul-prod-Group x unit-prod-Group) x
  right-unit-law-mul-prod-Group = right-unit-law-mul-Monoid monoid-prod-Group

  inv-prod-Group : type-prod-Group → type-prod-Group
  pr1 (inv-prod-Group (pair x y)) = inv-Group G x
  pr2 (inv-prod-Group (pair x y)) = inv-Group H y

  left-inverse-law-prod-Group :
    (x : type-prod-Group) →
    Id (mul-prod-Group (inv-prod-Group x) x) unit-prod-Group
  left-inverse-law-prod-Group (pair x y) =
    eq-pair (left-inverse-law-mul-Group G x) (left-inverse-law-mul-Group H y)

  right-inverse-law-prod-Group :
    (x : type-prod-Group) →
    Id (mul-prod-Group x (inv-prod-Group x)) unit-prod-Group
  right-inverse-law-prod-Group (pair x y) =
    eq-pair (right-inverse-law-mul-Group G x) (right-inverse-law-mul-Group H y)

  prod-Group : Group (l1 ⊔ l2)
  pr1 prod-Group = semigroup-prod-Group
  pr1 (pr1 (pr2 prod-Group)) = unit-prod-Group
  pr1 (pr2 (pr1 (pr2 prod-Group))) = left-unit-law-mul-prod-Group
  pr2 (pr2 (pr1 (pr2 prod-Group))) = right-unit-law-mul-prod-Group
  pr1 (pr2 (pr2 prod-Group)) = inv-prod-Group
  pr1 (pr2 (pr2 (pr2 prod-Group))) = left-inverse-law-prod-Group
  pr2 (pr2 (pr2 (pr2 prod-Group))) = right-inverse-law-prod-Group
```
