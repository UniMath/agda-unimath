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

  set-prod-Ring-𝔽 : Set (l1 ⊔ l2)
  set-prod-Ring-𝔽 = set-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  type-prod-Ring-𝔽 : UU (l1 ⊔ l2)
  type-prod-Ring-𝔽 = type-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  is-set-type-prod-Ring-𝔽 : is-set type-prod-Ring-𝔽
  is-set-type-prod-Ring-𝔽 =
    is-set-type-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  is-finite-type-prod-Ring-𝔽 : is-finite type-prod-Ring-𝔽
  is-finite-type-prod-Ring-𝔽 =
    is-finite-prod (is-finite-type-Ring-𝔽 R1) (is-finite-type-Ring-𝔽 R2)

  finite-type-prod-Ring-𝔽 : 𝔽 (l1 ⊔ l2)
  pr1 finite-type-prod-Ring-𝔽 = type-prod-Ring-𝔽
  pr2 finite-type-prod-Ring-𝔽 = is-finite-type-prod-Ring-𝔽

  add-prod-Ring-𝔽 : type-prod-Ring-𝔽 → type-prod-Ring-𝔽 → type-prod-Ring-𝔽
  add-prod-Ring-𝔽 = add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  zero-prod-Ring-𝔽 : type-prod-Ring-𝔽
  zero-prod-Ring-𝔽 = zero-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  neg-prod-Ring-𝔽 : type-prod-Ring-𝔽 → type-prod-Ring-𝔽
  neg-prod-Ring-𝔽 = neg-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-unit-law-add-prod-Ring-𝔽 :
    (x : type-prod-Ring-𝔽) → Id (add-prod-Ring-𝔽 zero-prod-Ring-𝔽 x) x
  left-unit-law-add-prod-Ring-𝔽 =
    left-unit-law-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-unit-law-add-prod-Ring-𝔽 :
    (x : type-prod-Ring-𝔽) → Id (add-prod-Ring-𝔽 x zero-prod-Ring-𝔽) x
  right-unit-law-add-prod-Ring-𝔽 =
    right-unit-law-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-inverse-law-add-prod-Ring-𝔽 :
    (x : type-prod-Ring-𝔽) →
    Id (add-prod-Ring-𝔽 (neg-prod-Ring-𝔽 x) x) zero-prod-Ring-𝔽
  left-inverse-law-add-prod-Ring-𝔽 =
    left-inverse-law-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-inverse-law-add-prod-Ring-𝔽 :
    (x : type-prod-Ring-𝔽) →
    Id (add-prod-Ring-𝔽 x (neg-prod-Ring-𝔽 x)) zero-prod-Ring-𝔽
  right-inverse-law-add-prod-Ring-𝔽 =
    right-inverse-law-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  associative-add-prod-Ring-𝔽 :
    (x y z : type-prod-Ring-𝔽) →
    Id
      ( add-prod-Ring-𝔽 (add-prod-Ring-𝔽 x y) z)
      ( add-prod-Ring-𝔽 x (add-prod-Ring-𝔽 y z))
  associative-add-prod-Ring-𝔽 =
    associative-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  commutative-add-prod-Ring-𝔽 :
    (x y : type-prod-Ring-𝔽) → Id (add-prod-Ring-𝔽 x y) (add-prod-Ring-𝔽 y x)
  commutative-add-prod-Ring-𝔽 =
    commutative-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  mul-prod-Ring-𝔽 : type-prod-Ring-𝔽 → type-prod-Ring-𝔽 → type-prod-Ring-𝔽
  mul-prod-Ring-𝔽 = mul-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  one-prod-Ring-𝔽 : type-prod-Ring-𝔽
  one-prod-Ring-𝔽 = one-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  associative-mul-prod-Ring-𝔽 :
    (x y z : type-prod-Ring-𝔽) →
    Id
      ( mul-prod-Ring-𝔽 (mul-prod-Ring-𝔽 x y) z)
      ( mul-prod-Ring-𝔽 x (mul-prod-Ring-𝔽 y z))
  associative-mul-prod-Ring-𝔽 =
    associative-mul-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-unit-law-mul-prod-Ring-𝔽 :
    (x : type-prod-Ring-𝔽) → Id (mul-prod-Ring-𝔽 one-prod-Ring-𝔽 x) x
  left-unit-law-mul-prod-Ring-𝔽 =
    left-unit-law-mul-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-unit-law-mul-prod-Ring-𝔽 :
    (x : type-prod-Ring-𝔽) → Id (mul-prod-Ring-𝔽 x one-prod-Ring-𝔽) x
  right-unit-law-mul-prod-Ring-𝔽 =
    right-unit-law-mul-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  left-distributive-mul-add-prod-Ring-𝔽 :
    (x y z : type-prod-Ring-𝔽) →
    Id
      ( mul-prod-Ring-𝔽 x (add-prod-Ring-𝔽 y z))
      ( add-prod-Ring-𝔽 (mul-prod-Ring-𝔽 x y) (mul-prod-Ring-𝔽 x z))
  left-distributive-mul-add-prod-Ring-𝔽 =
    left-distributive-mul-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  right-distributive-mul-add-prod-Ring-𝔽 :
    (x y z : type-prod-Ring-𝔽) →
    Id
      ( mul-prod-Ring-𝔽 (add-prod-Ring-𝔽 x y) z)
      ( add-prod-Ring-𝔽 (mul-prod-Ring-𝔽 x z) (mul-prod-Ring-𝔽 y z))
  right-distributive-mul-add-prod-Ring-𝔽 =
    right-distributive-mul-add-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  semigroup-prod-Ring-𝔽 : Semigroup (l1 ⊔ l2)
  semigroup-prod-Ring-𝔽 = semigroup-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  group-prod-Ring-𝔽 : Group (l1 ⊔ l2)
  group-prod-Ring-𝔽 = group-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  ab-prod-Ring-𝔽 : Ab (l1 ⊔ l2)
  ab-prod-Ring-𝔽 = ab-prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  ring-prod-Ring-𝔽 : Ring (l1 ⊔ l2)
  ring-prod-Ring-𝔽 = prod-Ring (ring-Ring-𝔽 R1) (ring-Ring-𝔽 R2)

  prod-Ring-𝔽 : Ring-𝔽 (l1 ⊔ l2)
  prod-Ring-𝔽 = compute-ring-𝔽 ring-prod-Ring-𝔽 is-finite-type-prod-Ring-𝔽
```
