# Cartesian products of commutative monoids

```agda
module group-theory.cartesian-products-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.cartesian-products-monoids
open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.monoids
```

</details>

## Idea

The
{{#concept "cartesian product" disambiguation="of commutative monoids" Agda=product-Commutative-Monoid WDID=Q173740 WD="Cartesian product"}}
of two [commutative monoids](group-theory.commutative-monoids.md) `M` and `N`
consists of the product `M × N` of the underlying sets and the componentwise
operation on it.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  monoid-product-Commutative-Monoid : Monoid (l1 ⊔ l2)
  monoid-product-Commutative-Monoid =
    product-Monoid (monoid-Commutative-Monoid M) (monoid-Commutative-Monoid N)

  set-product-Commutative-Monoid : Set (l1 ⊔ l2)
  set-product-Commutative-Monoid = set-Monoid monoid-product-Commutative-Monoid

  type-product-Commutative-Monoid : UU (l1 ⊔ l2)
  type-product-Commutative-Monoid =
    type-Monoid monoid-product-Commutative-Monoid

  is-set-type-product-Commutative-Monoid :
    is-set type-product-Commutative-Monoid
  is-set-type-product-Commutative-Monoid =
    is-set-type-Set set-product-Commutative-Monoid

  mul-product-Commutative-Monoid :
    (x y : type-product-Commutative-Monoid) → type-product-Commutative-Monoid
  mul-product-Commutative-Monoid = mul-Monoid monoid-product-Commutative-Monoid

  associative-mul-product-Commutative-Monoid :
    (x y z : type-product-Commutative-Monoid) →
    Id
      ( mul-product-Commutative-Monoid (mul-product-Commutative-Monoid x y) z)
      ( mul-product-Commutative-Monoid x (mul-product-Commutative-Monoid y z))
  associative-mul-product-Commutative-Monoid =
    associative-mul-Monoid monoid-product-Commutative-Monoid

  unit-product-Commutative-Monoid : type-product-Commutative-Monoid
  unit-product-Commutative-Monoid =
    unit-Monoid monoid-product-Commutative-Monoid

  left-unit-law-mul-product-Commutative-Monoid :
    (x : type-product-Commutative-Monoid) →
    Id (mul-product-Commutative-Monoid unit-product-Commutative-Monoid x) x
  left-unit-law-mul-product-Commutative-Monoid =
    left-unit-law-mul-Monoid monoid-product-Commutative-Monoid

  right-unit-law-mul-product-Commutative-Monoid :
    (x : type-product-Commutative-Monoid) →
    Id (mul-product-Commutative-Monoid x unit-product-Commutative-Monoid) x
  right-unit-law-mul-product-Commutative-Monoid =
    right-unit-law-mul-Monoid monoid-product-Commutative-Monoid

  commutative-mul-product-Commutative-Monoid :
    (x y : type-product-Commutative-Monoid) →
    Id
      ( mul-product-Commutative-Monoid x y)
      ( mul-product-Commutative-Monoid y x)
  commutative-mul-product-Commutative-Monoid _ _ =
    eq-pair
      ( commutative-mul-Commutative-Monoid M _ _)
      ( commutative-mul-Commutative-Monoid N _ _)

  product-Commutative-Monoid : Commutative-Monoid (l1 ⊔ l2)
  product-Commutative-Monoid =
    monoid-product-Commutative-Monoid ,
    commutative-mul-product-Commutative-Monoid
```

## Properties

### The homomorphism from `M` to `M × N`

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  left-hom-product-Commutative-Monoid :
    hom-Commutative-Monoid M (product-Commutative-Monoid M N)
  left-hom-product-Commutative-Monoid =
    left-hom-product-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
```

### The homomorphism from `N` to `M × N`

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  right-hom-product-Commutative-Monoid :
    hom-Commutative-Monoid N (product-Commutative-Monoid M N)
  right-hom-product-Commutative-Monoid =
    right-hom-product-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
```
