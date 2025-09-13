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
open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The
{{#concept "cartesian product" disambiguation="of monoids" Agda=product-Monoid WDID=Q173740 WD="Cartesian product"}}
of two [monoids](group-theory.monoids.md) `M` and `N` consists of the
[product](foundation.cartesian-product-types.md) `M × N` of the underlying
[sets](foundation.sets.md) and the componentwise operation on it.

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
    mul-product-Monoid (mul-product-Monoid x y) z ＝
    mul-product-Monoid x (mul-product-Monoid y z)
  associative-mul-product-Monoid =
    associative-mul-Semigroup semigroup-product-Monoid

  unit-product-Monoid : type-product-Monoid
  pr1 unit-product-Monoid = unit-Monoid M
  pr2 unit-product-Monoid = unit-Monoid N

  left-unit-law-mul-product-Monoid :
    (x : type-product-Monoid) → mul-product-Monoid unit-product-Monoid x ＝ x
  left-unit-law-mul-product-Monoid (pair x y) =
    eq-pair (left-unit-law-mul-Monoid M x) (left-unit-law-mul-Monoid N y)

  right-unit-law-mul-product-Monoid :
    (x : type-product-Monoid) → mul-product-Monoid x unit-product-Monoid ＝ x
  right-unit-law-mul-product-Monoid (pair x y) =
    eq-pair (right-unit-law-mul-Monoid M x) (right-unit-law-mul-Monoid N y)

  product-Monoid : Monoid (l1 ⊔ l2)
  pr1 product-Monoid = semigroup-product-Monoid
  pr1 (pr2 product-Monoid) = unit-product-Monoid
  pr1 (pr2 (pr2 product-Monoid)) = left-unit-law-mul-product-Monoid
  pr2 (pr2 (pr2 product-Monoid)) = right-unit-law-mul-product-Monoid
```

## Properties

### The homomorphism from `M` to `M × N`

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  map-left-hom-product-Monoid : type-Monoid M → type-product-Monoid M N
  map-left-hom-product-Monoid m = (m , unit-Monoid N)

  left-hom-product-Monoid : hom-Monoid M (product-Monoid M N)
  left-hom-product-Monoid =
    ( map-left-hom-product-Monoid ,
      eq-pair refl (inv (left-unit-law-mul-Monoid N _))) ,
    refl
```

### The homomorphism from `N` to `M × N`

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  map-right-hom-product-Monoid : type-Monoid N → type-product-Monoid M N
  map-right-hom-product-Monoid n = (unit-Monoid M , n)

  right-hom-product-Monoid : hom-Monoid N (product-Monoid M N)
  right-hom-product-Monoid =
    ( ( map-right-hom-product-Monoid ,
        eq-pair (inv (left-unit-law-mul-Monoid M _)) refl) ,
      refl)
```
