# Products of commutative finite rings

```agda
module finite-algebra.products-commutative-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.products-commutative-rings

open import finite-algebra.commutative-finite-rings
open import finite-algebra.products-finite-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import univalent-combinatorics.finite-types
```

</details>

## Idea

Given two commutative finite rings R1 and R2, we define a commutative finite
ring structure on the product of R1 and R2.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R1 : Finite-Commutative-Ring l1) (R2 : Finite-Commutative-Ring l2)
  where

  set-product-Finite-Commutative-Ring : Set (l1 ⊔ l2)
  set-product-Finite-Commutative-Ring =
    set-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  type-product-Finite-Commutative-Ring : UU (l1 ⊔ l2)
  type-product-Finite-Commutative-Ring =
    type-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  is-set-type-product-Finite-Commutative-Ring :
    is-set type-product-Finite-Commutative-Ring
  is-set-type-product-Finite-Commutative-Ring =
    is-set-type-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  is-finite-type-product-Finite-Commutative-Ring :
    is-finite type-product-Finite-Commutative-Ring
  is-finite-type-product-Finite-Commutative-Ring =
    is-finite-type-product-Finite-Ring
      ( finite-ring-Finite-Commutative-Ring R1)
      ( finite-ring-Finite-Commutative-Ring R2)

  finite-type-product-Finite-Commutative-Ring : Finite-Type (l1 ⊔ l2)
  pr1 finite-type-product-Finite-Commutative-Ring =
    type-product-Finite-Commutative-Ring
  pr2 finite-type-product-Finite-Commutative-Ring =
    is-finite-type-product-Finite-Commutative-Ring

  add-product-Finite-Commutative-Ring :
    type-product-Finite-Commutative-Ring →
    type-product-Finite-Commutative-Ring →
    type-product-Finite-Commutative-Ring
  add-product-Finite-Commutative-Ring =
    add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  zero-product-Finite-Commutative-Ring : type-product-Finite-Commutative-Ring
  zero-product-Finite-Commutative-Ring =
    zero-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  neg-product-Finite-Commutative-Ring :
    type-product-Finite-Commutative-Ring → type-product-Finite-Commutative-Ring
  neg-product-Finite-Commutative-Ring =
    neg-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  left-unit-law-add-product-Finite-Commutative-Ring :
    (x : type-product-Finite-Commutative-Ring) →
    add-product-Finite-Commutative-Ring
      ( zero-product-Finite-Commutative-Ring)
      ( x) ＝
    x
  left-unit-law-add-product-Finite-Commutative-Ring =
    left-unit-law-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  right-unit-law-add-product-Finite-Commutative-Ring :
    (x : type-product-Finite-Commutative-Ring) →
    add-product-Finite-Commutative-Ring
      ( x)
      ( zero-product-Finite-Commutative-Ring) ＝
    x
  right-unit-law-add-product-Finite-Commutative-Ring =
    right-unit-law-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  left-inverse-law-add-product-Finite-Commutative-Ring :
    (x : type-product-Finite-Commutative-Ring) →
      add-product-Finite-Commutative-Ring
        ( neg-product-Finite-Commutative-Ring x)
        ( x) ＝
      zero-product-Finite-Commutative-Ring
  left-inverse-law-add-product-Finite-Commutative-Ring =
    left-inverse-law-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  right-inverse-law-add-product-Finite-Commutative-Ring :
    (x : type-product-Finite-Commutative-Ring) →
    add-product-Finite-Commutative-Ring
      ( x)
      ( neg-product-Finite-Commutative-Ring x) ＝
    zero-product-Finite-Commutative-Ring
  right-inverse-law-add-product-Finite-Commutative-Ring =
    right-inverse-law-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  associative-add-product-Finite-Commutative-Ring :
    (x y z : type-product-Finite-Commutative-Ring) →
    add-product-Finite-Commutative-Ring
      ( add-product-Finite-Commutative-Ring x y)
      ( z) ＝
    add-product-Finite-Commutative-Ring
      ( x)
      ( add-product-Finite-Commutative-Ring y z)
  associative-add-product-Finite-Commutative-Ring =
    associative-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  commutative-add-product-Finite-Commutative-Ring :
    (x y : type-product-Finite-Commutative-Ring) →
    add-product-Finite-Commutative-Ring x y ＝
    add-product-Finite-Commutative-Ring y x
  commutative-add-product-Finite-Commutative-Ring =
    commutative-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  mul-product-Finite-Commutative-Ring :
    type-product-Finite-Commutative-Ring →
    type-product-Finite-Commutative-Ring →
    type-product-Finite-Commutative-Ring
  mul-product-Finite-Commutative-Ring =
    mul-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  one-product-Finite-Commutative-Ring : type-product-Finite-Commutative-Ring
  one-product-Finite-Commutative-Ring =
    one-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  associative-mul-product-Finite-Commutative-Ring :
    (x y z : type-product-Finite-Commutative-Ring) →
    mul-product-Finite-Commutative-Ring
      ( mul-product-Finite-Commutative-Ring x y)
      ( z) ＝
    mul-product-Finite-Commutative-Ring
      ( x)
      ( mul-product-Finite-Commutative-Ring y z)
  associative-mul-product-Finite-Commutative-Ring =
    associative-mul-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  left-unit-law-mul-product-Finite-Commutative-Ring :
    (x : type-product-Finite-Commutative-Ring) →
    mul-product-Finite-Commutative-Ring one-product-Finite-Commutative-Ring x ＝
    x
  left-unit-law-mul-product-Finite-Commutative-Ring =
    left-unit-law-mul-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  right-unit-law-mul-product-Finite-Commutative-Ring :
    (x : type-product-Finite-Commutative-Ring) →
    mul-product-Finite-Commutative-Ring x one-product-Finite-Commutative-Ring ＝
    x
  right-unit-law-mul-product-Finite-Commutative-Ring =
    right-unit-law-mul-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  left-distributive-mul-add-product-Finite-Commutative-Ring :
    (x y z : type-product-Finite-Commutative-Ring) →
    mul-product-Finite-Commutative-Ring
      ( x)
      ( add-product-Finite-Commutative-Ring y z) ＝
    add-product-Finite-Commutative-Ring
      ( mul-product-Finite-Commutative-Ring x y)
      ( mul-product-Finite-Commutative-Ring x z)
  left-distributive-mul-add-product-Finite-Commutative-Ring =
    left-distributive-mul-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  right-distributive-mul-add-product-Finite-Commutative-Ring :
    (x y z : type-product-Finite-Commutative-Ring) →
    mul-product-Finite-Commutative-Ring
      ( add-product-Finite-Commutative-Ring x y)
      ( z) ＝
    add-product-Finite-Commutative-Ring
      ( mul-product-Finite-Commutative-Ring x z)
      ( mul-product-Finite-Commutative-Ring y z)
  right-distributive-mul-add-product-Finite-Commutative-Ring =
    right-distributive-mul-add-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  semigroup-product-Finite-Commutative-Ring : Semigroup (l1 ⊔ l2)
  semigroup-product-Finite-Commutative-Ring =
    semigroup-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  group-product-Finite-Commutative-Ring : Group (l1 ⊔ l2)
  group-product-Finite-Commutative-Ring =
    group-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  ab-product-Finite-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-product-Finite-Commutative-Ring =
    ab-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  ring-product-Finite-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  ring-product-Finite-Commutative-Ring =
    product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  commutative-mul-product-Finite-Commutative-Ring :
    (x y : type-product-Finite-Commutative-Ring) →
    mul-product-Finite-Commutative-Ring x y ＝
    mul-product-Finite-Commutative-Ring y x
  commutative-mul-product-Finite-Commutative-Ring =
    commutative-mul-product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  commutative-ring-product-Finite-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  commutative-ring-product-Finite-Commutative-Ring =
    product-Commutative-Ring
      ( commutative-ring-Finite-Commutative-Ring R1)
      ( commutative-ring-Finite-Commutative-Ring R2)

  product-Finite-Commutative-Ring : Finite-Commutative-Ring (l1 ⊔ l2)
  pr1 product-Finite-Commutative-Ring =
    product-Finite-Ring
      ( finite-ring-Finite-Commutative-Ring R1)
      ( finite-ring-Finite-Commutative-Ring R2)
  pr2 product-Finite-Commutative-Ring =
    commutative-mul-product-Finite-Commutative-Ring
```
