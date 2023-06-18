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

  set-prod-Commutative-Ring : Set (l1 ⊔ l2)
  set-prod-Commutative-Ring =
    set-prod-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  type-prod-Commutative-Ring : UU (l1 ⊔ l2)
  type-prod-Commutative-Ring =
    type-prod-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  is-set-type-prod-Commutative-Ring : is-set type-prod-Commutative-Ring
  is-set-type-prod-Commutative-Ring =
    is-set-type-prod-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  add-prod-Commutative-Ring :
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring
  add-prod-Commutative-Ring =
    add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  zero-prod-Commutative-Ring : type-prod-Commutative-Ring
  zero-prod-Commutative-Ring =
    zero-prod-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  neg-prod-Commutative-Ring :
    type-prod-Commutative-Ring → type-prod-Commutative-Ring
  neg-prod-Commutative-Ring =
    neg-prod-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  left-unit-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    add-prod-Commutative-Ring zero-prod-Commutative-Ring x ＝ x
  left-unit-law-add-prod-Commutative-Ring =
    left-unit-law-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-unit-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    add-prod-Commutative-Ring x zero-prod-Commutative-Ring ＝ x
  right-unit-law-add-prod-Commutative-Ring =
    right-unit-law-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  left-inverse-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id
      ( add-prod-Commutative-Ring (neg-prod-Commutative-Ring x) x)
      zero-prod-Commutative-Ring
  left-inverse-law-add-prod-Commutative-Ring =
    left-inverse-law-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-inverse-law-add-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id
      ( add-prod-Commutative-Ring x (neg-prod-Commutative-Ring x))
      ( zero-prod-Commutative-Ring)
  right-inverse-law-add-prod-Commutative-Ring =
    right-inverse-law-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  associative-add-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( add-prod-Commutative-Ring (add-prod-Commutative-Ring x y) z)
      ( add-prod-Commutative-Ring x (add-prod-Commutative-Ring y z))
  associative-add-prod-Commutative-Ring =
    associative-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  commutative-add-prod-Commutative-Ring :
    (x y : type-prod-Commutative-Ring) →
    Id (add-prod-Commutative-Ring x y) (add-prod-Commutative-Ring y x)
  commutative-add-prod-Commutative-Ring =
    commutative-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  mul-prod-Commutative-Ring :
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring →
    type-prod-Commutative-Ring
  mul-prod-Commutative-Ring =
    mul-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  one-prod-Commutative-Ring : type-prod-Commutative-Ring
  one-prod-Commutative-Ring =
    one-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  associative-mul-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( mul-prod-Commutative-Ring (mul-prod-Commutative-Ring x y) z)
      ( mul-prod-Commutative-Ring x (mul-prod-Commutative-Ring y z))
  associative-mul-prod-Commutative-Ring =
    associative-mul-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  left-unit-law-mul-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id (mul-prod-Commutative-Ring one-prod-Commutative-Ring x) x
  left-unit-law-mul-prod-Commutative-Ring =
    left-unit-law-mul-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-unit-law-mul-prod-Commutative-Ring :
    (x : type-prod-Commutative-Ring) →
    Id (mul-prod-Commutative-Ring x one-prod-Commutative-Ring) x
  right-unit-law-mul-prod-Commutative-Ring =
    right-unit-law-mul-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  left-distributive-mul-add-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( mul-prod-Commutative-Ring x (add-prod-Commutative-Ring y z))
      ( add-prod-Commutative-Ring
        ( mul-prod-Commutative-Ring x y)
        ( mul-prod-Commutative-Ring x z))
  left-distributive-mul-add-prod-Commutative-Ring =
    left-distributive-mul-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  right-distributive-mul-add-prod-Commutative-Ring :
    (x y z : type-prod-Commutative-Ring) →
    Id
      ( mul-prod-Commutative-Ring (add-prod-Commutative-Ring x y) z)
      ( add-prod-Commutative-Ring
        ( mul-prod-Commutative-Ring x z)
        ( mul-prod-Commutative-Ring y z))
  right-distributive-mul-add-prod-Commutative-Ring =
    right-distributive-mul-add-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  semigroup-prod-Commutative-Ring : Semigroup (l1 ⊔ l2)
  semigroup-prod-Commutative-Ring =
    semigroup-prod-Ring
      ( ring-Commutative-Ring R1)
      ( ring-Commutative-Ring R2)

  group-prod-Commutative-Ring : Group (l1 ⊔ l2)
  group-prod-Commutative-Ring =
    group-prod-Ring ( ring-Commutative-Ring R1) ( ring-Commutative-Ring R2)

  ab-prod-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-prod-Commutative-Ring =
    ab-prod-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  ring-prod-Commutative-Ring : Ring (l1 ⊔ l2)
  ring-prod-Commutative-Ring =
    prod-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

  commutative-mul-prod-Commutative-Ring :
    (x y : type-prod-Commutative-Ring) →
    mul-prod-Commutative-Ring x y ＝ mul-prod-Commutative-Ring y x
  commutative-mul-prod-Commutative-Ring (x1 , x2) (y1 , y2) =
    eq-pair
      ( commutative-mul-Commutative-Ring R1 x1 y1)
      ( commutative-mul-Commutative-Ring R2 x2 y2)

  prod-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  pr1 prod-Commutative-Ring = ring-prod-Commutative-Ring
  pr2 prod-Commutative-Ring = commutative-mul-prod-Commutative-Ring
```
