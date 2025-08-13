# Products of commutative monoids

```agda
module group-theory.products-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.products-monoids
```

</details>

## Idea

Given a pair of [commutative monoids](group-theory.commutative-monoids.md) `M`
and `N`, the
{{#concept "product" disambiguation="of commutative monoids" Agda=product-Commutative-Monoid}}
`M × N` consists of pairs of elements of M and N with the pairwise binary
operation.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  type-product-Commutative-Monoid : UU (l1 ⊔ l2)
  type-product-Commutative-Monoid =
    type-Commutative-Monoid M × type-Commutative-Monoid N

  set-product-Commutative-Monoid : Set (l1 ⊔ l2)
  set-product-Commutative-Monoid =
    product-Set (set-Commutative-Monoid M) (set-Commutative-Monoid N)

  mul-product-Commutative-Monoid :
    type-product-Commutative-Monoid → type-product-Commutative-Monoid →
    type-product-Commutative-Monoid
  mul-product-Commutative-Monoid =
    mul-product-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)

  commutative-mul-product-Commutative-Monoid :
    (x y : type-product-Commutative-Monoid) →
    mul-product-Commutative-Monoid x y ＝ mul-product-Commutative-Monoid y x
  commutative-mul-product-Commutative-Monoid _ _ =
    eq-pair
      ( commutative-mul-Commutative-Monoid M _ _)
      ( commutative-mul-Commutative-Monoid N _ _)

  product-Commutative-Monoid : Commutative-Monoid (l1 ⊔ l2)
  product-Commutative-Monoid =
    product-Monoid (monoid-Commutative-Monoid M) (monoid-Commutative-Monoid N) ,
    commutative-mul-product-Commutative-Monoid

  unit-product-Commutative-Monoid : type-product-Commutative-Monoid
  unit-product-Commutative-Monoid =
    unit-Commutative-Monoid product-Commutative-Monoid

  associative-mul-product-Commutative-Monoid :
    (x y z : type-product-Commutative-Monoid) →
    mul-product-Commutative-Monoid (mul-product-Commutative-Monoid x y) z ＝
    mul-product-Commutative-Monoid x (mul-product-Commutative-Monoid y z)
  associative-mul-product-Commutative-Monoid =
    associative-mul-Commutative-Monoid product-Commutative-Monoid
```

## Properties

### The commutative monoid homomorphism from `M` to `M × N`

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

### The monoid homomorphism from `N` to `M × N`

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
