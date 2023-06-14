# Cartesian products of semigroups

```agda
module group-theory.cartesian-products-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

The cartesian product of two semigroups `A` and `B` consists of the cartesian
product of its underlying sets and the componentwise multiplication

## Definition

```agda
module _
  {l1 l2 : Level} (A : Semigroup l1) (B : Semigroup l2)
  where

  set-prod-Semigroup : Set (l1 ⊔ l2)
  set-prod-Semigroup = prod-Set (set-Semigroup A) (set-Semigroup B)

  type-prod-Semigroup : UU (l1 ⊔ l2)
  type-prod-Semigroup = type-Set set-prod-Semigroup

  is-set-type-prod-Semigroup : is-set type-prod-Semigroup
  is-set-type-prod-Semigroup = is-set-type-Set set-prod-Semigroup

  mul-prod-Semigroup :
    type-prod-Semigroup → type-prod-Semigroup → type-prod-Semigroup
  pr1 (mul-prod-Semigroup (pair x1 y1) (pair x2 y2)) = mul-Semigroup A x1 x2
  pr2 (mul-prod-Semigroup (pair x1 y1) (pair x2 y2)) = mul-Semigroup B y1 y2

  associative-mul-prod-Semigroup :
    (x y z : type-prod-Semigroup) →
    Id
      ( mul-prod-Semigroup (mul-prod-Semigroup x y) z)
      ( mul-prod-Semigroup x (mul-prod-Semigroup y z))
  associative-mul-prod-Semigroup (pair x1 y1) (pair x2 y2) (pair x3 y3) =
    eq-pair
      ( associative-mul-Semigroup A x1 x2 x3)
      ( associative-mul-Semigroup B y1 y2 y3)

  prod-Semigroup : Semigroup (l1 ⊔ l2)
  pr1 prod-Semigroup = set-prod-Semigroup
  pr1 (pr2 prod-Semigroup) = mul-prod-Semigroup
  pr2 (pr2 prod-Semigroup) = associative-mul-prod-Semigroup
```
