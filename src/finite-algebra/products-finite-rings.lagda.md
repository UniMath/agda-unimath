# Products of finite rings

```agda
module finite-algebra.products-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.products-rings
open import ring-theory.rings

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Given two [finite rings](finite-algebra.finite-rings.md) `R1` and `R2`, then the
{{#concept "product" Disambiguation="of finite rings" Agda=product-Finite-Ring}}
finite ring `R1 × R2` is defined componentwise.

## Definition

```agda
module _
  {l1 l2 : Level} (R1 : Finite-Ring l1) (R2 : Finite-Ring l2)
  where

  set-product-Finite-Ring : Set (l1 ⊔ l2)
  set-product-Finite-Ring =
    set-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  type-product-Finite-Ring : UU (l1 ⊔ l2)
  type-product-Finite-Ring =
    type-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  is-set-type-product-Finite-Ring : is-set type-product-Finite-Ring
  is-set-type-product-Finite-Ring =
    is-set-type-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  is-finite-type-product-Finite-Ring : is-finite type-product-Finite-Ring
  is-finite-type-product-Finite-Ring =
    is-finite-product
      ( is-finite-type-Finite-Ring R1)
      ( is-finite-type-Finite-Ring R2)

  finite-type-product-Finite-Ring : Finite-Type (l1 ⊔ l2)
  pr1 finite-type-product-Finite-Ring = type-product-Finite-Ring
  pr2 finite-type-product-Finite-Ring = is-finite-type-product-Finite-Ring

  add-product-Finite-Ring :
    type-product-Finite-Ring →
    type-product-Finite-Ring →
    type-product-Finite-Ring
  add-product-Finite-Ring =
    add-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  zero-product-Finite-Ring : type-product-Finite-Ring
  zero-product-Finite-Ring =
    zero-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  neg-product-Finite-Ring : type-product-Finite-Ring → type-product-Finite-Ring
  neg-product-Finite-Ring =
    neg-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  left-unit-law-add-product-Finite-Ring :
    (x : type-product-Finite-Ring) →
    add-product-Finite-Ring zero-product-Finite-Ring x ＝ x
  left-unit-law-add-product-Finite-Ring =
    left-unit-law-add-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  right-unit-law-add-product-Finite-Ring :
    (x : type-product-Finite-Ring) →
    add-product-Finite-Ring x zero-product-Finite-Ring ＝ x
  right-unit-law-add-product-Finite-Ring =
    right-unit-law-add-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  left-inverse-law-add-product-Finite-Ring :
    (x : type-product-Finite-Ring) →
    add-product-Finite-Ring (neg-product-Finite-Ring x) x ＝
    zero-product-Finite-Ring
  left-inverse-law-add-product-Finite-Ring =
    left-inverse-law-add-product-Ring
      ( ring-Finite-Ring R1)
      ( ring-Finite-Ring R2)

  right-inverse-law-add-product-Finite-Ring :
    (x : type-product-Finite-Ring) →
    add-product-Finite-Ring x (neg-product-Finite-Ring x) ＝
    zero-product-Finite-Ring
  right-inverse-law-add-product-Finite-Ring =
    right-inverse-law-add-product-Ring
      ( ring-Finite-Ring R1)
      ( ring-Finite-Ring R2)

  associative-add-product-Finite-Ring :
    (x y z : type-product-Finite-Ring) →
    add-product-Finite-Ring (add-product-Finite-Ring x y) z ＝
    add-product-Finite-Ring x (add-product-Finite-Ring y z)
  associative-add-product-Finite-Ring =
    associative-add-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  commutative-add-product-Finite-Ring :
    (x y : type-product-Finite-Ring) →
    add-product-Finite-Ring x y ＝ add-product-Finite-Ring y x
  commutative-add-product-Finite-Ring =
    commutative-add-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  mul-product-Finite-Ring :
    type-product-Finite-Ring →
    type-product-Finite-Ring →
    type-product-Finite-Ring
  mul-product-Finite-Ring =
    mul-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  one-product-Finite-Ring : type-product-Finite-Ring
  one-product-Finite-Ring =
    one-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  associative-mul-product-Finite-Ring :
    (x y z : type-product-Finite-Ring) →
    mul-product-Finite-Ring (mul-product-Finite-Ring x y) z ＝
    mul-product-Finite-Ring x (mul-product-Finite-Ring y z)
  associative-mul-product-Finite-Ring =
    associative-mul-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  left-unit-law-mul-product-Finite-Ring :
    (x : type-product-Finite-Ring) →
    mul-product-Finite-Ring one-product-Finite-Ring x ＝ x
  left-unit-law-mul-product-Finite-Ring =
    left-unit-law-mul-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  right-unit-law-mul-product-Finite-Ring :
    (x : type-product-Finite-Ring) →
    mul-product-Finite-Ring x one-product-Finite-Ring ＝ x
  right-unit-law-mul-product-Finite-Ring =
    right-unit-law-mul-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  left-distributive-mul-add-product-Finite-Ring :
    (x y z : type-product-Finite-Ring) →
    mul-product-Finite-Ring x (add-product-Finite-Ring y z) ＝
    add-product-Finite-Ring
      ( mul-product-Finite-Ring x y)
      ( mul-product-Finite-Ring x z)
  left-distributive-mul-add-product-Finite-Ring =
    left-distributive-mul-add-product-Ring
      ( ring-Finite-Ring R1)
      ( ring-Finite-Ring R2)

  right-distributive-mul-add-product-Finite-Ring :
    (x y z : type-product-Finite-Ring) →
    mul-product-Finite-Ring (add-product-Finite-Ring x y) z ＝
    add-product-Finite-Ring
      ( mul-product-Finite-Ring x z)
      ( mul-product-Finite-Ring y z)
  right-distributive-mul-add-product-Finite-Ring =
    right-distributive-mul-add-product-Ring
      ( ring-Finite-Ring R1)
      ( ring-Finite-Ring R2)

  semigroup-product-Finite-Ring : Semigroup (l1 ⊔ l2)
  semigroup-product-Finite-Ring =
    semigroup-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  group-product-Finite-Ring : Group (l1 ⊔ l2)
  group-product-Finite-Ring =
    group-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  ab-product-Finite-Ring : Ab (l1 ⊔ l2)
  ab-product-Finite-Ring =
    ab-product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  ring-product-Finite-Ring : Ring (l1 ⊔ l2)
  ring-product-Finite-Ring =
    product-Ring (ring-Finite-Ring R1) (ring-Finite-Ring R2)

  product-Finite-Ring : Finite-Ring (l1 ⊔ l2)
  product-Finite-Ring =
    finite-ring-is-finite-Ring
      ring-product-Finite-Ring
      is-finite-type-product-Finite-Ring
```
