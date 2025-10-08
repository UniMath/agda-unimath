# Products of commutative rings

```agda
module commutative-algebra.products-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.products-rings
open import ring-theory.rings
```

</details>

## Idea

Given two commutative rings R1 and R2, we define a commutative ring structure on
the product of R1 and R2.

## Definition

```agda
module _
  {l1 l2 : Level} (R1 : Commutative-Ring l1) (R2 : Commutative-Ring l2)
  where

  set-product-Commutative-Ring : Set (l1 ⊔ l2)
  set-product-Commutative-Ring =
    set-product-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  type-product-Commutative-Ring : UU (l1 ⊔ l2)
  type-product-Commutative-Ring =
    type-product-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  is-set-type-product-Commutative-Ring : is-set type-product-Commutative-Ring
  is-set-type-product-Commutative-Ring =
    is-set-type-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  add-product-Commutative-Ring :
    type-product-Commutative-Ring →
    type-product-Commutative-Ring →
    type-product-Commutative-Ring
  add-product-Commutative-Ring =
    add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  zero-product-Commutative-Ring : type-product-Commutative-Ring
  zero-product-Commutative-Ring =
    zero-product-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  neg-product-Commutative-Ring :
    type-product-Commutative-Ring → type-product-Commutative-Ring
  neg-product-Commutative-Ring =
    neg-product-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  left-unit-law-add-product-Commutative-Ring :
    (x : type-product-Commutative-Ring) →
    add-product-Commutative-Ring zero-product-Commutative-Ring x ＝ x
  left-unit-law-add-product-Commutative-Ring =
    left-unit-law-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-unit-law-add-product-Commutative-Ring :
    (x : type-product-Commutative-Ring) →
    add-product-Commutative-Ring x zero-product-Commutative-Ring ＝ x
  right-unit-law-add-product-Commutative-Ring =
    right-unit-law-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  left-inverse-law-add-product-Commutative-Ring :
    (x : type-product-Commutative-Ring) →
    add-product-Commutative-Ring (neg-product-Commutative-Ring x) x ＝
    zero-product-Commutative-Ring
  left-inverse-law-add-product-Commutative-Ring =
    left-inverse-law-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-inverse-law-add-product-Commutative-Ring :
    (x : type-product-Commutative-Ring) →
    add-product-Commutative-Ring x (neg-product-Commutative-Ring x) ＝
    zero-product-Commutative-Ring
  right-inverse-law-add-product-Commutative-Ring =
    right-inverse-law-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  associative-add-product-Commutative-Ring :
    (x y z : type-product-Commutative-Ring) →
    ( add-product-Commutative-Ring (add-product-Commutative-Ring x y) z) ＝
    ( add-product-Commutative-Ring x (add-product-Commutative-Ring y z))
  associative-add-product-Commutative-Ring =
    associative-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  commutative-add-product-Commutative-Ring :
    (x y : type-product-Commutative-Ring) →
    add-product-Commutative-Ring x y ＝ add-product-Commutative-Ring y x
  commutative-add-product-Commutative-Ring =
    commutative-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  mul-product-Commutative-Ring :
    type-product-Commutative-Ring →
    type-product-Commutative-Ring →
    type-product-Commutative-Ring
  mul-product-Commutative-Ring =
    mul-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  one-product-Commutative-Ring : type-product-Commutative-Ring
  one-product-Commutative-Ring =
    one-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  associative-mul-product-Commutative-Ring :
    (x y z : type-product-Commutative-Ring) →
    ( mul-product-Commutative-Ring (mul-product-Commutative-Ring x y) z) ＝
    ( mul-product-Commutative-Ring x (mul-product-Commutative-Ring y z))
  associative-mul-product-Commutative-Ring =
    associative-mul-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  left-unit-law-mul-product-Commutative-Ring :
    (x : type-product-Commutative-Ring) →
    mul-product-Commutative-Ring one-product-Commutative-Ring x ＝ x
  left-unit-law-mul-product-Commutative-Ring =
    left-unit-law-mul-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-unit-law-mul-product-Commutative-Ring :
    (x : type-product-Commutative-Ring) →
    mul-product-Commutative-Ring x one-product-Commutative-Ring ＝ x
  right-unit-law-mul-product-Commutative-Ring =
    right-unit-law-mul-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  left-distributive-mul-add-product-Commutative-Ring :
    (x y z : type-product-Commutative-Ring) →
    mul-product-Commutative-Ring x (add-product-Commutative-Ring y z) ＝
    add-product-Commutative-Ring
      ( mul-product-Commutative-Ring x y)
      ( mul-product-Commutative-Ring x z)
  left-distributive-mul-add-product-Commutative-Ring =
    left-distributive-mul-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-distributive-mul-add-product-Commutative-Ring :
    (x y z : type-product-Commutative-Ring) →
    mul-product-Commutative-Ring (add-product-Commutative-Ring x y) z ＝
    add-product-Commutative-Ring
      ( mul-product-Commutative-Ring x z)
      ( mul-product-Commutative-Ring y z)
  right-distributive-mul-add-product-Commutative-Ring =
    right-distributive-mul-add-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  semigroup-product-Commutative-Ring : Semigroup (l1 ⊔ l2)
  semigroup-product-Commutative-Ring =
    semigroup-product-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  group-product-Commutative-Ring : Group (l1 ⊔ l2)
  group-product-Commutative-Ring =
    group-product-Ring ( ring-Commutative-Ring R1) ( ring-Commutative-Ring R2)

  ab-product-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-product-Commutative-Ring =
    ab-product-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  ring-product-Commutative-Ring : Ring (l1 ⊔ l2)
  ring-product-Commutative-Ring =
    product-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  commutative-mul-product-Commutative-Ring :
    (x y : type-product-Commutative-Ring) →
    mul-product-Commutative-Ring x y ＝ mul-product-Commutative-Ring y x
  commutative-mul-product-Commutative-Ring (x1 , x2) (y1 , y2) =
    eq-pair
      ( commutative-mul-Commutative-Ring R1 x1 y1)
      ( commutative-mul-Commutative-Ring R2 x2 y2)

  product-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  pr1 product-Commutative-Ring = ring-product-Commutative-Ring
  pr2 product-Commutative-Ring = commutative-mul-product-Commutative-Ring
```
