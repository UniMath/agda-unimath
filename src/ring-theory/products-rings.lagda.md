# Products of rings

```agda
module ring-theory.products-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

Given two [rings](ring-theory.rings.md) `R1` and `R2`, the
{{#concept "product" Disambiguation="of a pair of rings" Agda=product-Ring}}
ring `R1 × R2` is a ring structure on the
[cartesian product](foundation.cartesian-product-types.md) of `R1` and `R2`
given by componentwise operations.

## Definition

```agda
module _
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
  where

  set-product-Ring : Set (l1 ⊔ l2)
  set-product-Ring = product-Set (set-Ring R1) (set-Ring R2)

  type-product-Ring : UU (l1 ⊔ l2)
  type-product-Ring = type-Set set-product-Ring

  is-set-type-product-Ring : is-set type-product-Ring
  is-set-type-product-Ring = is-set-type-Set set-product-Ring

  add-product-Ring : type-product-Ring → type-product-Ring → type-product-Ring
  pr1 (add-product-Ring (x1 , y1) (x2 , y2)) = add-Ring R1 x1 x2
  pr2 (add-product-Ring (x1 , y1) (x2 , y2)) = add-Ring R2 y1 y2

  zero-product-Ring : type-product-Ring
  pr1 zero-product-Ring = zero-Ring R1
  pr2 zero-product-Ring = zero-Ring R2

  neg-product-Ring : type-product-Ring → type-product-Ring
  pr1 (neg-product-Ring (x , y)) = neg-Ring R1 x
  pr2 (neg-product-Ring (x , y)) = neg-Ring R2 y

  left-unit-law-add-product-Ring :
    (x : type-product-Ring) → add-product-Ring zero-product-Ring x ＝ x
  left-unit-law-add-product-Ring (x , y) =
    eq-pair (left-unit-law-add-Ring R1 x) (left-unit-law-add-Ring R2 y)

  right-unit-law-add-product-Ring :
    (x : type-product-Ring) → add-product-Ring x zero-product-Ring ＝ x
  right-unit-law-add-product-Ring (x , y) =
    eq-pair (right-unit-law-add-Ring R1 x) (right-unit-law-add-Ring R2 y)

  left-inverse-law-add-product-Ring :
    (x : type-product-Ring) →
    add-product-Ring (neg-product-Ring x) x ＝ zero-product-Ring
  left-inverse-law-add-product-Ring (x , y) =
    eq-pair (left-inverse-law-add-Ring R1 x) (left-inverse-law-add-Ring R2 y)

  right-inverse-law-add-product-Ring :
    (x : type-product-Ring) →
    add-product-Ring x (neg-product-Ring x) ＝ zero-product-Ring
  right-inverse-law-add-product-Ring (x , y) =
    eq-pair (right-inverse-law-add-Ring R1 x) (right-inverse-law-add-Ring R2 y)

  associative-add-product-Ring :
    (x y z : type-product-Ring) →
    add-product-Ring (add-product-Ring x y) z ＝
    add-product-Ring x (add-product-Ring y z)
  associative-add-product-Ring (x1 , y1) (x2 , y2) (x3 , y3) =
    eq-pair
      ( associative-add-Ring R1 x1 x2 x3)
      ( associative-add-Ring R2 y1 y2 y3)

  commutative-add-product-Ring :
    (x y : type-product-Ring) → add-product-Ring x y ＝ add-product-Ring y x
  commutative-add-product-Ring (x1 , y1) (x2 , y2) =
    eq-pair
      ( commutative-add-Ring R1 x1 x2)
      ( commutative-add-Ring R2 y1 y2)

  mul-product-Ring : type-product-Ring → type-product-Ring → type-product-Ring
  pr1 (mul-product-Ring (x1 , y1) (x2 , y2)) = mul-Ring R1 x1 x2
  pr2 (mul-product-Ring (x1 , y1) (x2 , y2)) = mul-Ring R2 y1 y2

  one-product-Ring : type-product-Ring
  pr1 one-product-Ring = one-Ring R1
  pr2 one-product-Ring = one-Ring R2

  associative-mul-product-Ring :
    (x y z : type-product-Ring) →
    mul-product-Ring (mul-product-Ring x y) z ＝
    mul-product-Ring x (mul-product-Ring y z)
  associative-mul-product-Ring (x1 , y1) (x2 , y2) (x3 , y3) =
    eq-pair
      ( associative-mul-Ring R1 x1 x2 x3)
      ( associative-mul-Ring R2 y1 y2 y3)

  left-unit-law-mul-product-Ring :
    (x : type-product-Ring) → mul-product-Ring one-product-Ring x ＝ x
  left-unit-law-mul-product-Ring (x , y) =
    eq-pair (left-unit-law-mul-Ring R1 x) (left-unit-law-mul-Ring R2 y)

  right-unit-law-mul-product-Ring :
    (x : type-product-Ring) → mul-product-Ring x one-product-Ring ＝ x
  right-unit-law-mul-product-Ring (x , y) =
    eq-pair (right-unit-law-mul-Ring R1 x) (right-unit-law-mul-Ring R2 y)

  left-distributive-mul-add-product-Ring :
    (x y z : type-product-Ring) →
    mul-product-Ring x (add-product-Ring y z) ＝
    add-product-Ring (mul-product-Ring x y) (mul-product-Ring x z)
  left-distributive-mul-add-product-Ring (x1 , y1) (x2 , y2) (x3 , y3) =
    eq-pair
      ( left-distributive-mul-add-Ring R1 x1 x2 x3)
      ( left-distributive-mul-add-Ring R2 y1 y2 y3)

  right-distributive-mul-add-product-Ring :
    (x y z : type-product-Ring) →
    mul-product-Ring (add-product-Ring x y) z ＝
    add-product-Ring (mul-product-Ring x z) (mul-product-Ring y z)
  right-distributive-mul-add-product-Ring (x1 , y1) (x2 , y2) (x3 , y3) =
    eq-pair
      ( right-distributive-mul-add-Ring R1 x1 x2 x3)
      ( right-distributive-mul-add-Ring R2 y1 y2 y3)

  semigroup-product-Ring : Semigroup (l1 ⊔ l2)
  pr1 semigroup-product-Ring = set-product-Ring
  pr1 (pr2 semigroup-product-Ring) = add-product-Ring
  pr2 (pr2 semigroup-product-Ring) = associative-add-product-Ring

  group-product-Ring : Group (l1 ⊔ l2)
  pr1 group-product-Ring = semigroup-product-Ring
  pr1 (pr1 (pr2 group-product-Ring)) = zero-product-Ring
  pr1 (pr2 (pr1 (pr2 group-product-Ring))) = left-unit-law-add-product-Ring
  pr2 (pr2 (pr1 (pr2 group-product-Ring))) = right-unit-law-add-product-Ring
  pr1 (pr2 (pr2 group-product-Ring)) = neg-product-Ring
  pr1 (pr2 (pr2 (pr2 group-product-Ring))) = left-inverse-law-add-product-Ring
  pr2 (pr2 (pr2 (pr2 group-product-Ring))) = right-inverse-law-add-product-Ring

  ab-product-Ring : Ab (l1 ⊔ l2)
  pr1 ab-product-Ring = group-product-Ring
  pr2 ab-product-Ring = commutative-add-product-Ring

  product-Ring : Ring (l1 ⊔ l2)
  pr1 product-Ring = ab-product-Ring
  pr1 (pr1 (pr2 product-Ring)) = mul-product-Ring
  pr2 (pr1 (pr2 product-Ring)) = associative-mul-product-Ring
  pr1 (pr1 (pr2 (pr2 product-Ring))) = one-product-Ring
  pr1 (pr2 (pr1 (pr2 (pr2 product-Ring)))) = left-unit-law-mul-product-Ring
  pr2 (pr2 (pr1 (pr2 (pr2 product-Ring)))) = right-unit-law-mul-product-Ring
  pr1 (pr2 (pr2 (pr2 product-Ring))) = left-distributive-mul-add-product-Ring
  pr2 (pr2 (pr2 (pr2 product-Ring))) = right-distributive-mul-add-product-Ring
```
