# Products of monoids

```agda
module group-theory.products-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.isomorphisms-monoids
open import group-theory.monoids
open import group-theory.products-semigroups
```

</details>

## Idea

Given a pair of [monoids](group-theory.monoids.md) `M` and `N`, the
{{#concept "product" disambiguation="of monoids" Agda=product-Monoid}} `M × N`
consists of pairs of elements of M and N with the pairwise binary operation.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  type-product-Monoid : UU (l1 ⊔ l2)
  type-product-Monoid = type-Monoid M × type-Monoid N

  mul-product-Monoid :
    type-product-Monoid → type-product-Monoid → type-product-Monoid
  mul-product-Monoid =
    mul-product-Semigroup (semigroup-Monoid M) (semigroup-Monoid N)

  unit-product-Monoid : type-product-Monoid
  unit-product-Monoid = (unit-Monoid M , unit-Monoid N)

  left-unit-law-mul-product-Monoid :
    (x : type-product-Monoid) → mul-product-Monoid unit-product-Monoid x ＝ x
  left-unit-law-mul-product-Monoid (m , n) =
    eq-pair (left-unit-law-mul-Monoid M m) (left-unit-law-mul-Monoid N n)

  right-unit-law-mul-product-Monoid :
    (x : type-product-Monoid) → mul-product-Monoid x unit-product-Monoid ＝ x
  right-unit-law-mul-product-Monoid (m , n) =
    eq-pair (right-unit-law-mul-Monoid M m) (right-unit-law-mul-Monoid N n)

  product-Monoid : Monoid (l1 ⊔ l2)
  product-Monoid =
    product-Semigroup (semigroup-Monoid M) (semigroup-Monoid N) ,
    unit-product-Monoid ,
    left-unit-law-mul-product-Monoid ,
    right-unit-law-mul-product-Monoid
```

## Properties

### The monoid homomorphism from `M` to `M × N`

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  map-left-hom-product-Monoid : type-Monoid M → type-product-Monoid M N
  map-left-hom-product-Monoid m = (m , unit-Monoid N)

  left-hom-product-Monoid : hom-Monoid M (product-Monoid M N)
  left-hom-product-Monoid =
    ( map-left-hom-product-Monoid ,
      eq-pair refl (inv (left-unit-law-mul-Monoid N (unit-Monoid N)))) ,
    refl
```

### The monoid homomorphism from `N` to `M × N`

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  map-right-hom-product-Monoid : type-Monoid N → type-product-Monoid M N
  map-right-hom-product-Monoid n = (unit-Monoid M , n)

  right-hom-product-Monoid : hom-Monoid N (product-Monoid M N)
  right-hom-product-Monoid =
    ( map-right-hom-product-Monoid ,
      eq-pair (inv (left-unit-law-mul-Monoid M (unit-Monoid M))) refl) ,
    refl
```
