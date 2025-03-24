# Cartesian products of monoids

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.cartesian-products-monoids
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.cartesian-products-semigroups funext univalence
open import group-theory.monoids funext univalence truncations
open import group-theory.semigroups funext univalence
```

</details>

## Idea

The cartesian product of two monoids `M` and `N` consists of the product `M × N`
of the underlying sets and the componentwise operation on it.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  semigroup-product-Monoid : Semigroup (l1 ⊔ l2)
  semigroup-product-Monoid =
    product-Semigroup (semigroup-Monoid M) (semigroup-Monoid N)

  set-product-Monoid : Set (l1 ⊔ l2)
  set-product-Monoid = set-Semigroup semigroup-product-Monoid

  type-product-Monoid : UU (l1 ⊔ l2)
  type-product-Monoid = type-Semigroup semigroup-product-Monoid

  is-set-type-product-Monoid : is-set type-product-Monoid
  is-set-type-product-Monoid = is-set-type-Semigroup semigroup-product-Monoid

  mul-product-Monoid : (x y : type-product-Monoid) → type-product-Monoid
  mul-product-Monoid = mul-Semigroup semigroup-product-Monoid

  associative-mul-product-Monoid :
    (x y z : type-product-Monoid) →
    Id
      ( mul-product-Monoid (mul-product-Monoid x y) z)
      ( mul-product-Monoid x (mul-product-Monoid y z))
  associative-mul-product-Monoid =
    associative-mul-Semigroup semigroup-product-Monoid

  unit-product-Monoid : type-product-Monoid
  pr1 unit-product-Monoid = unit-Monoid M
  pr2 unit-product-Monoid = unit-Monoid N

  left-unit-law-mul-product-Monoid :
    (x : type-product-Monoid) → Id (mul-product-Monoid unit-product-Monoid x) x
  left-unit-law-mul-product-Monoid (pair x y) =
    eq-pair (left-unit-law-mul-Monoid M x) (left-unit-law-mul-Monoid N y)

  right-unit-law-mul-product-Monoid :
    (x : type-product-Monoid) → Id (mul-product-Monoid x unit-product-Monoid) x
  right-unit-law-mul-product-Monoid (pair x y) =
    eq-pair (right-unit-law-mul-Monoid M x) (right-unit-law-mul-Monoid N y)

  product-Monoid : Monoid (l1 ⊔ l2)
  pr1 product-Monoid = semigroup-product-Monoid
  pr1 (pr2 product-Monoid) = unit-product-Monoid
  pr1 (pr2 (pr2 product-Monoid)) = left-unit-law-mul-product-Monoid
  pr2 (pr2 (pr2 product-Monoid)) = right-unit-law-mul-product-Monoid
```
