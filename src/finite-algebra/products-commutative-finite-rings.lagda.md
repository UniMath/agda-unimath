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
  {l1 l2 : Level} (R1 : Commutative-Ring-𝔽 l1) (R2 : Commutative-Ring-𝔽 l2)
  where

  set-prod-Commutative-Ring-𝔽 : Set (l1 ⊔ l2)
  set-prod-Commutative-Ring-𝔽 =
    set-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  type-prod-Commutative-Ring-𝔽 : UU (l1 ⊔ l2)
  type-prod-Commutative-Ring-𝔽 =
    type-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  is-set-type-prod-Commutative-Ring-𝔽 : is-set type-prod-Commutative-Ring-𝔽
  is-set-type-prod-Commutative-Ring-𝔽 =
    is-set-type-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  is-finite-type-prod-Commutative-Ring-𝔽 :
    is-finite type-prod-Commutative-Ring-𝔽
  is-finite-type-prod-Commutative-Ring-𝔽 =
    is-finite-type-prod-Ring-𝔽
      ( finite-ring-Commutative-Ring-𝔽 R1)
      ( finite-ring-Commutative-Ring-𝔽 R2)

  finite-type-prod-Commutative-Ring-𝔽 : 𝔽 (l1 ⊔ l2)
  pr1 finite-type-prod-Commutative-Ring-𝔽 = type-prod-Commutative-Ring-𝔽
  pr2 finite-type-prod-Commutative-Ring-𝔽 =
    is-finite-type-prod-Commutative-Ring-𝔽

  add-prod-Commutative-Ring-𝔽 :
    type-prod-Commutative-Ring-𝔽 →
    type-prod-Commutative-Ring-𝔽 →
    type-prod-Commutative-Ring-𝔽
  add-prod-Commutative-Ring-𝔽 =
    add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  zero-prod-Commutative-Ring-𝔽 : type-prod-Commutative-Ring-𝔽
  zero-prod-Commutative-Ring-𝔽 =
    zero-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  neg-prod-Commutative-Ring-𝔽 :
    type-prod-Commutative-Ring-𝔽 → type-prod-Commutative-Ring-𝔽
  neg-prod-Commutative-Ring-𝔽 =
    neg-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-unit-law-add-prod-Commutative-Ring-𝔽 :
    (x : type-prod-Commutative-Ring-𝔽) →
    Id (add-prod-Commutative-Ring-𝔽 zero-prod-Commutative-Ring-𝔽 x) x
  left-unit-law-add-prod-Commutative-Ring-𝔽 =
    left-unit-law-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-unit-law-add-prod-Commutative-Ring-𝔽 :
    (x : type-prod-Commutative-Ring-𝔽) →
    Id (add-prod-Commutative-Ring-𝔽 x zero-prod-Commutative-Ring-𝔽) x
  right-unit-law-add-prod-Commutative-Ring-𝔽 =
    right-unit-law-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-inverse-law-add-prod-Commutative-Ring-𝔽 :
    (x : type-prod-Commutative-Ring-𝔽) →
    Id
      ( add-prod-Commutative-Ring-𝔽 (neg-prod-Commutative-Ring-𝔽 x) x)
      zero-prod-Commutative-Ring-𝔽
  left-inverse-law-add-prod-Commutative-Ring-𝔽 =
    left-inverse-law-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-inverse-law-add-prod-Commutative-Ring-𝔽 :
    (x : type-prod-Commutative-Ring-𝔽) →
    Id
      ( add-prod-Commutative-Ring-𝔽 x (neg-prod-Commutative-Ring-𝔽 x))
      ( zero-prod-Commutative-Ring-𝔽)
  right-inverse-law-add-prod-Commutative-Ring-𝔽 =
    right-inverse-law-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  associative-add-prod-Commutative-Ring-𝔽 :
    (x y z : type-prod-Commutative-Ring-𝔽) →
    Id
      ( add-prod-Commutative-Ring-𝔽 (add-prod-Commutative-Ring-𝔽 x y) z)
      ( add-prod-Commutative-Ring-𝔽 x (add-prod-Commutative-Ring-𝔽 y z))
  associative-add-prod-Commutative-Ring-𝔽 =
    associative-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  commutative-add-prod-Commutative-Ring-𝔽 :
    (x y : type-prod-Commutative-Ring-𝔽) →
    Id (add-prod-Commutative-Ring-𝔽 x y) (add-prod-Commutative-Ring-𝔽 y x)
  commutative-add-prod-Commutative-Ring-𝔽 =
    commutative-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  mul-prod-Commutative-Ring-𝔽 :
    type-prod-Commutative-Ring-𝔽 →
    type-prod-Commutative-Ring-𝔽 →
    type-prod-Commutative-Ring-𝔽
  mul-prod-Commutative-Ring-𝔽 =
    mul-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  one-prod-Commutative-Ring-𝔽 : type-prod-Commutative-Ring-𝔽
  one-prod-Commutative-Ring-𝔽 =
    one-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  associative-mul-prod-Commutative-Ring-𝔽 :
    (x y z : type-prod-Commutative-Ring-𝔽) →
    Id
      ( mul-prod-Commutative-Ring-𝔽 (mul-prod-Commutative-Ring-𝔽 x y) z)
      ( mul-prod-Commutative-Ring-𝔽 x (mul-prod-Commutative-Ring-𝔽 y z))
  associative-mul-prod-Commutative-Ring-𝔽 =
    associative-mul-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-unit-law-mul-prod-Commutative-Ring-𝔽 :
    (x : type-prod-Commutative-Ring-𝔽) →
    Id (mul-prod-Commutative-Ring-𝔽 one-prod-Commutative-Ring-𝔽 x) x
  left-unit-law-mul-prod-Commutative-Ring-𝔽 =
    left-unit-law-mul-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-unit-law-mul-prod-Commutative-Ring-𝔽 :
    (x : type-prod-Commutative-Ring-𝔽) →
    Id (mul-prod-Commutative-Ring-𝔽 x one-prod-Commutative-Ring-𝔽) x
  right-unit-law-mul-prod-Commutative-Ring-𝔽 =
    right-unit-law-mul-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-distributive-mul-add-prod-Commutative-Ring-𝔽 :
    (x y z : type-prod-Commutative-Ring-𝔽) →
    Id
      ( mul-prod-Commutative-Ring-𝔽 x (add-prod-Commutative-Ring-𝔽 y z))
      ( add-prod-Commutative-Ring-𝔽
        ( mul-prod-Commutative-Ring-𝔽 x y)
        ( mul-prod-Commutative-Ring-𝔽 x z))
  left-distributive-mul-add-prod-Commutative-Ring-𝔽 =
    left-distributive-mul-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-distributive-mul-add-prod-Commutative-Ring-𝔽 :
    (x y z : type-prod-Commutative-Ring-𝔽) →
    Id
      ( mul-prod-Commutative-Ring-𝔽 (add-prod-Commutative-Ring-𝔽 x y) z)
      ( add-prod-Commutative-Ring-𝔽
        ( mul-prod-Commutative-Ring-𝔽 x z)
        ( mul-prod-Commutative-Ring-𝔽 y z))
  right-distributive-mul-add-prod-Commutative-Ring-𝔽 =
    right-distributive-mul-add-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  semigroup-prod-Commutative-Ring-𝔽 : Semigroup (l1 ⊔ l2)
  semigroup-prod-Commutative-Ring-𝔽 =
    semigroup-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  group-prod-Commutative-Ring-𝔽 : Group (l1 ⊔ l2)
  group-prod-Commutative-Ring-𝔽 =
    group-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  ab-prod-Commutative-Ring-𝔽 : Ab (l1 ⊔ l2)
  ab-prod-Commutative-Ring-𝔽 =
    ab-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  ring-prod-Commutative-Ring-𝔽 : Commutative-Ring (l1 ⊔ l2)
  ring-prod-Commutative-Ring-𝔽 =
    prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  commutative-mul-prod-Commutative-Ring-𝔽 :
    (x y : type-prod-Commutative-Ring-𝔽) →
    mul-prod-Commutative-Ring-𝔽 x y ＝ mul-prod-Commutative-Ring-𝔽 y x
  commutative-mul-prod-Commutative-Ring-𝔽 =
    commutative-mul-prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  commutative-ring-prod-Commutative-Ring-𝔽 : Commutative-Ring (l1 ⊔ l2)
  commutative-ring-prod-Commutative-Ring-𝔽 =
    prod-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  prod-Commutative-Ring-𝔽 : Commutative-Ring-𝔽 (l1 ⊔ l2)
  pr1 prod-Commutative-Ring-𝔽 =
    prod-Ring-𝔽
      ( finite-ring-Commutative-Ring-𝔽 R1)
      ( finite-ring-Commutative-Ring-𝔽 R2)
  pr2 prod-Commutative-Ring-𝔽 = commutative-mul-prod-Commutative-Ring-𝔽
```
