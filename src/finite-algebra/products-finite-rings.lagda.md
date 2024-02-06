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

Given two finite rings R1 and R2, we define a ring structure on the product of
R1 and R2.

## Definition

```agda
module _
  {l1 l2 : Level} (R1 : Ring-𝔽 l1) (R2 : Ring-𝔽 l2)
  where

  set-product-Ring-𝔽 : Set (l1 ⊔ l2)
  set-product-Ring-𝔽 = set-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  type-product-Ring-𝔽 : UU (l1 ⊔ l2)
  type-product-Ring-𝔽 = type-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  is-set-type-product-Ring-𝔽 : is-set type-product-Ring-𝔽
  is-set-type-product-Ring-𝔽 =
    is-set-type-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  is-finite-type-product-Ring-𝔽 : is-finite type-product-Ring-𝔽
  is-finite-type-product-Ring-𝔽 =
    is-finite-product (is-finite-type-Ring-𝔽 R1) (is-finite-type-Ring-𝔽 R2)

  finite-type-product-Ring-𝔽 : 𝔽 (l1 ⊔ l2)
  pr1 finite-type-product-Ring-𝔽 = type-product-Ring-𝔽
  pr2 finite-type-product-Ring-𝔽 = is-finite-type-product-Ring-𝔽

  add-product-Ring-𝔽 :
    type-product-Ring-𝔽 → type-product-Ring-𝔽 → type-product-Ring-𝔽
  add-product-Ring-𝔽 = add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  zero-product-Ring-𝔽 : type-product-Ring-𝔽
  zero-product-Ring-𝔽 = zero-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  neg-product-Ring-𝔽 : type-product-Ring-𝔽 → type-product-Ring-𝔽
  neg-product-Ring-𝔽 = neg-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-unit-law-add-product-Ring-𝔽 :
    (x : type-product-Ring-𝔽) → Id (add-product-Ring-𝔽 zero-product-Ring-𝔽 x) x
  left-unit-law-add-product-Ring-𝔽 =
    left-unit-law-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-unit-law-add-product-Ring-𝔽 :
    (x : type-product-Ring-𝔽) → Id (add-product-Ring-𝔽 x zero-product-Ring-𝔽) x
  right-unit-law-add-product-Ring-𝔽 =
    right-unit-law-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-inverse-law-add-product-Ring-𝔽 :
    (x : type-product-Ring-𝔽) →
    Id (add-product-Ring-𝔽 (neg-product-Ring-𝔽 x) x) zero-product-Ring-𝔽
  left-inverse-law-add-product-Ring-𝔽 =
    left-inverse-law-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-inverse-law-add-product-Ring-𝔽 :
    (x : type-product-Ring-𝔽) →
    Id (add-product-Ring-𝔽 x (neg-product-Ring-𝔽 x)) zero-product-Ring-𝔽
  right-inverse-law-add-product-Ring-𝔽 =
    right-inverse-law-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  associative-add-product-Ring-𝔽 :
    (x y z : type-product-Ring-𝔽) →
    Id
      ( add-product-Ring-𝔽 (add-product-Ring-𝔽 x y) z)
      ( add-product-Ring-𝔽 x (add-product-Ring-𝔽 y z))
  associative-add-product-Ring-𝔽 =
    associative-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  commutative-add-product-Ring-𝔽 :
    (x y : type-product-Ring-𝔽) →
    Id (add-product-Ring-𝔽 x y) (add-product-Ring-𝔽 y x)
  commutative-add-product-Ring-𝔽 =
    commutative-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  mul-product-Ring-𝔽 :
    type-product-Ring-𝔽 → type-product-Ring-𝔽 → type-product-Ring-𝔽
  mul-product-Ring-𝔽 = mul-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  one-product-Ring-𝔽 : type-product-Ring-𝔽
  one-product-Ring-𝔽 = one-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  associative-mul-product-Ring-𝔽 :
    (x y z : type-product-Ring-𝔽) →
    Id
      ( mul-product-Ring-𝔽 (mul-product-Ring-𝔽 x y) z)
      ( mul-product-Ring-𝔽 x (mul-product-Ring-𝔽 y z))
  associative-mul-product-Ring-𝔽 =
    associative-mul-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-unit-law-mul-product-Ring-𝔽 :
    (x : type-product-Ring-𝔽) → Id (mul-product-Ring-𝔽 one-product-Ring-𝔽 x) x
  left-unit-law-mul-product-Ring-𝔽 =
    left-unit-law-mul-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-unit-law-mul-product-Ring-𝔽 :
    (x : type-product-Ring-𝔽) → Id (mul-product-Ring-𝔽 x one-product-Ring-𝔽) x
  right-unit-law-mul-product-Ring-𝔽 =
    right-unit-law-mul-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-distributive-mul-add-product-Ring-𝔽 :
    (x y z : type-product-Ring-𝔽) →
    Id
      ( mul-product-Ring-𝔽 x (add-product-Ring-𝔽 y z))
      ( add-product-Ring-𝔽 (mul-product-Ring-𝔽 x y) (mul-product-Ring-𝔽 x z))
  left-distributive-mul-add-product-Ring-𝔽 =
    left-distributive-mul-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-distributive-mul-add-product-Ring-𝔽 :
    (x y z : type-product-Ring-𝔽) →
    Id
      ( mul-product-Ring-𝔽 (add-product-Ring-𝔽 x y) z)
      ( add-product-Ring-𝔽 (mul-product-Ring-𝔽 x z) (mul-product-Ring-𝔽 y z))
  right-distributive-mul-add-product-Ring-𝔽 =
    right-distributive-mul-add-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  semigroup-product-Ring-𝔽 : Semigroup (l1 ⊔ l2)
  semigroup-product-Ring-𝔽 =
    semigroup-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  group-product-Ring-𝔽 : Group (l1 ⊔ l2)
  group-product-Ring-𝔽 = group-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  ab-product-Ring-𝔽 : Ab (l1 ⊔ l2)
  ab-product-Ring-𝔽 = ab-product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  ring-product-Ring-𝔽 : Ring (l1 ⊔ l2)
  ring-product-Ring-𝔽 = product-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  product-Ring-𝔽 : Ring-𝔽 (l1 ⊔ l2)
  product-Ring-𝔽 =
    finite-ring-is-finite-Ring ring-product-Ring-𝔽 is-finite-type-product-Ring-𝔽
```
