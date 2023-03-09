# Cartesian products of monoids

```agda
module group-theory.cartesian-products-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.cartesian-products-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The cartesian product of two monoids `M` and `N` consists of the product `M × N` of the underlying sets and the componentwise operation on it.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  semigroup-prod-Monoid : Semigroup (l1 ⊔ l2)
  semigroup-prod-Monoid =
    prod-Semigroup (semigroup-Monoid M) (semigroup-Monoid N)

  set-prod-Monoid : Set (l1 ⊔ l2)
  set-prod-Monoid = set-Semigroup semigroup-prod-Monoid

  type-prod-Monoid : UU (l1 ⊔ l2)
  type-prod-Monoid = type-Semigroup semigroup-prod-Monoid

  is-set-type-prod-Monoid : is-set type-prod-Monoid
  is-set-type-prod-Monoid = is-set-type-Semigroup semigroup-prod-Monoid

  mul-prod-Monoid : (x y : type-prod-Monoid) → type-prod-Monoid
  mul-prod-Monoid = mul-Semigroup semigroup-prod-Monoid

  associative-mul-prod-Monoid :
    (x y z : type-prod-Monoid) →
    Id ( mul-prod-Monoid (mul-prod-Monoid x y) z)
       ( mul-prod-Monoid x (mul-prod-Monoid y z))
  associative-mul-prod-Monoid =
    associative-mul-Semigroup semigroup-prod-Monoid

  unit-prod-Monoid : type-prod-Monoid
  pr1 unit-prod-Monoid = unit-Monoid M
  pr2 unit-prod-Monoid = unit-Monoid N

  left-unit-law-mul-prod-Monoid :
    (x : type-prod-Monoid) → Id (mul-prod-Monoid unit-prod-Monoid x) x
  left-unit-law-mul-prod-Monoid (pair x y) =
    eq-pair (left-unit-law-mul-Monoid M x) (left-unit-law-mul-Monoid N y)

  right-unit-law-mul-prod-Monoid :
    (x : type-prod-Monoid) → Id (mul-prod-Monoid x unit-prod-Monoid) x
  right-unit-law-mul-prod-Monoid (pair x y) =
    eq-pair (right-unit-law-mul-Monoid M x) (right-unit-law-mul-Monoid N y)

  prod-Monoid : Monoid (l1 ⊔ l2)
  pr1 prod-Monoid = semigroup-prod-Monoid
  pr1 (pr2 prod-Monoid) = unit-prod-Monoid
  pr1 (pr2 (pr2 prod-Monoid)) = left-unit-law-mul-prod-Monoid
  pr2 (pr2 (pr2 prod-Monoid)) = right-unit-law-mul-prod-Monoid
```
