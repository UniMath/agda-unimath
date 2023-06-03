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

Given two ringrs R1 and R2, we define a ring structure on the product of R1 and
R2.

## Definition

```agda
module _
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
  where

  set-prod-Ring : Set (l1 ⊔ l2)
  set-prod-Ring = prod-Set (set-Ring R1) (set-Ring R2)

  type-prod-Ring : UU (l1 ⊔ l2)
  type-prod-Ring = type-Set set-prod-Ring

  is-set-type-prod-Ring : is-set type-prod-Ring
  is-set-type-prod-Ring = is-set-type-Set set-prod-Ring

  add-prod-Ring : type-prod-Ring → type-prod-Ring → type-prod-Ring
  pr1 (add-prod-Ring (pair x1 y1) (pair x2 y2)) = add-Ring R1 x1 x2
  pr2 (add-prod-Ring (pair x1 y1) (pair x2 y2)) = add-Ring R2 y1 y2

  zero-prod-Ring : type-prod-Ring
  pr1 zero-prod-Ring = zero-Ring R1
  pr2 zero-prod-Ring = zero-Ring R2

  neg-prod-Ring : type-prod-Ring → type-prod-Ring
  pr1 (neg-prod-Ring (pair x y)) = neg-Ring R1 x
  pr2 (neg-prod-Ring (pair x y)) = neg-Ring R2 y

  left-unit-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring zero-prod-Ring x) x
  left-unit-law-add-prod-Ring (pair x y) =
    eq-pair (left-unit-law-add-Ring R1 x) (left-unit-law-add-Ring R2 y)

  right-unit-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring x zero-prod-Ring) x
  right-unit-law-add-prod-Ring (pair x y) =
    eq-pair (right-unit-law-add-Ring R1 x) (right-unit-law-add-Ring R2 y)

  left-inverse-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring (neg-prod-Ring x) x) zero-prod-Ring
  left-inverse-law-add-prod-Ring (pair x y) =
    eq-pair (left-inverse-law-add-Ring R1 x) (left-inverse-law-add-Ring R2 y)

  right-inverse-law-add-prod-Ring :
    (x : type-prod-Ring) → Id (add-prod-Ring x (neg-prod-Ring x)) zero-prod-Ring
  right-inverse-law-add-prod-Ring (pair x y) =
    eq-pair (right-inverse-law-add-Ring R1 x) (right-inverse-law-add-Ring R2 y)

  associative-add-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( add-prod-Ring (add-prod-Ring x y) z)
      ( add-prod-Ring x (add-prod-Ring y z))
  associative-add-prod-Ring (pair x1 y1) (pair x2 y2) (pair x3 y3) =
    eq-pair
      ( associative-add-Ring R1 x1 x2 x3)
      ( associative-add-Ring R2 y1 y2 y3)

  commutative-add-prod-Ring :
    (x y : type-prod-Ring) → Id (add-prod-Ring x y) (add-prod-Ring y x)
  commutative-add-prod-Ring (pair x1 y1) (pair x2 y2) =
    eq-pair
      ( commutative-add-Ring R1 x1 x2)
      ( commutative-add-Ring R2 y1 y2)

  mul-prod-Ring : type-prod-Ring → type-prod-Ring → type-prod-Ring
  pr1 (mul-prod-Ring (pair x1 y1) (pair x2 y2)) = mul-Ring R1 x1 x2
  pr2 (mul-prod-Ring (pair x1 y1) (pair x2 y2)) = mul-Ring R2 y1 y2

  one-prod-Ring : type-prod-Ring
  pr1 one-prod-Ring = one-Ring R1
  pr2 one-prod-Ring = one-Ring R2

  associative-mul-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( mul-prod-Ring (mul-prod-Ring x y) z)
      ( mul-prod-Ring x (mul-prod-Ring y z))
  associative-mul-prod-Ring (pair x1 y1) (pair x2 y2) (pair x3 y3) =
    eq-pair
      ( associative-mul-Ring R1 x1 x2 x3)
      ( associative-mul-Ring R2 y1 y2 y3)

  left-unit-law-mul-prod-Ring :
    (x : type-prod-Ring) → Id (mul-prod-Ring one-prod-Ring x) x
  left-unit-law-mul-prod-Ring (pair x y) =
    eq-pair (left-unit-law-mul-Ring R1 x) (left-unit-law-mul-Ring R2 y)

  right-unit-law-mul-prod-Ring :
    (x : type-prod-Ring) → Id (mul-prod-Ring x one-prod-Ring) x
  right-unit-law-mul-prod-Ring (pair x y) =
    eq-pair (right-unit-law-mul-Ring R1 x) (right-unit-law-mul-Ring R2 y)

  left-distributive-mul-add-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( mul-prod-Ring x (add-prod-Ring y z))
      ( add-prod-Ring (mul-prod-Ring x y) (mul-prod-Ring x z))
  left-distributive-mul-add-prod-Ring (pair x1 y1) (pair x2 y2) (pair x3 y3) =
    eq-pair
      ( left-distributive-mul-add-Ring R1 x1 x2 x3)
      ( left-distributive-mul-add-Ring R2 y1 y2 y3)

  right-distributive-mul-add-prod-Ring :
    (x y z : type-prod-Ring) →
    Id
      ( mul-prod-Ring (add-prod-Ring x y) z)
      ( add-prod-Ring (mul-prod-Ring x z) (mul-prod-Ring y z))
  right-distributive-mul-add-prod-Ring (pair x1 y1) (pair x2 y2) (pair x3 y3) =
    eq-pair
      ( right-distributive-mul-add-Ring R1 x1 x2 x3)
      ( right-distributive-mul-add-Ring R2 y1 y2 y3)

  semigroup-prod-Ring : Semigroup (l1 ⊔ l2)
  pr1 semigroup-prod-Ring = set-prod-Ring
  pr1 (pr2 semigroup-prod-Ring) = add-prod-Ring
  pr2 (pr2 semigroup-prod-Ring) = associative-add-prod-Ring

  group-prod-Ring : Group (l1 ⊔ l2)
  pr1 group-prod-Ring = semigroup-prod-Ring
  pr1 (pr1 (pr2 group-prod-Ring)) = zero-prod-Ring
  pr1 (pr2 (pr1 (pr2 group-prod-Ring))) = left-unit-law-add-prod-Ring
  pr2 (pr2 (pr1 (pr2 group-prod-Ring))) = right-unit-law-add-prod-Ring
  pr1 (pr2 (pr2 group-prod-Ring)) = neg-prod-Ring
  pr1 (pr2 (pr2 (pr2 group-prod-Ring))) = left-inverse-law-add-prod-Ring
  pr2 (pr2 (pr2 (pr2 group-prod-Ring))) = right-inverse-law-add-prod-Ring

  ab-prod-Ring : Ab (l1 ⊔ l2)
  pr1 ab-prod-Ring = group-prod-Ring
  pr2 ab-prod-Ring = commutative-add-prod-Ring

  prod-Ring : Ring (l1 ⊔ l2)
  pr1 prod-Ring = ab-prod-Ring
  pr1 (pr1 (pr2 prod-Ring)) = mul-prod-Ring
  pr2 (pr1 (pr2 prod-Ring)) = associative-mul-prod-Ring
  pr1 (pr1 (pr2 (pr2 prod-Ring))) = one-prod-Ring
  pr1 (pr2 (pr1 (pr2 (pr2 prod-Ring)))) = left-unit-law-mul-prod-Ring
  pr2 (pr2 (pr1 (pr2 (pr2 prod-Ring)))) = right-unit-law-mul-prod-Ring
  pr1 (pr2 (pr2 (pr2 prod-Ring))) = left-distributive-mul-add-prod-Ring
  pr2 (pr2 (pr2 (pr2 prod-Ring))) = right-distributive-mul-add-prod-Ring
```
