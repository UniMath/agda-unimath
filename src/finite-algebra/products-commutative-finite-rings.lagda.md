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

  set-product-Commutative-Ring-𝔽 : Set (l1 ⊔ l2)
  set-product-Commutative-Ring-𝔽 =
    set-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  type-product-Commutative-Ring-𝔽 : UU (l1 ⊔ l2)
  type-product-Commutative-Ring-𝔽 =
    type-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  is-set-type-product-Commutative-Ring-𝔽 :
    is-set type-product-Commutative-Ring-𝔽
  is-set-type-product-Commutative-Ring-𝔽 =
    is-set-type-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  is-finite-type-product-Commutative-Ring-𝔽 :
    is-finite type-product-Commutative-Ring-𝔽
  is-finite-type-product-Commutative-Ring-𝔽 =
    is-finite-type-product-Ring-𝔽
      ( finite-ring-Commutative-Ring-𝔽 R1)
      ( finite-ring-Commutative-Ring-𝔽 R2)

  finite-type-product-Commutative-Ring-𝔽 : 𝔽 (l1 ⊔ l2)
  pr1 finite-type-product-Commutative-Ring-𝔽 = type-product-Commutative-Ring-𝔽
  pr2 finite-type-product-Commutative-Ring-𝔽 =
    is-finite-type-product-Commutative-Ring-𝔽

  add-product-Commutative-Ring-𝔽 :
    type-product-Commutative-Ring-𝔽 →
    type-product-Commutative-Ring-𝔽 →
    type-product-Commutative-Ring-𝔽
  add-product-Commutative-Ring-𝔽 =
    add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  zero-product-Commutative-Ring-𝔽 : type-product-Commutative-Ring-𝔽
  zero-product-Commutative-Ring-𝔽 =
    zero-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  neg-product-Commutative-Ring-𝔽 :
    type-product-Commutative-Ring-𝔽 → type-product-Commutative-Ring-𝔽
  neg-product-Commutative-Ring-𝔽 =
    neg-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-unit-law-add-product-Commutative-Ring-𝔽 :
    (x : type-product-Commutative-Ring-𝔽) →
    Id (add-product-Commutative-Ring-𝔽 zero-product-Commutative-Ring-𝔽 x) x
  left-unit-law-add-product-Commutative-Ring-𝔽 =
    left-unit-law-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-unit-law-add-product-Commutative-Ring-𝔽 :
    (x : type-product-Commutative-Ring-𝔽) →
    Id (add-product-Commutative-Ring-𝔽 x zero-product-Commutative-Ring-𝔽) x
  right-unit-law-add-product-Commutative-Ring-𝔽 =
    right-unit-law-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-inverse-law-add-product-Commutative-Ring-𝔽 :
    (x : type-product-Commutative-Ring-𝔽) →
    Id
      ( add-product-Commutative-Ring-𝔽 (neg-product-Commutative-Ring-𝔽 x) x)
      zero-product-Commutative-Ring-𝔽
  left-inverse-law-add-product-Commutative-Ring-𝔽 =
    left-inverse-law-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-inverse-law-add-product-Commutative-Ring-𝔽 :
    (x : type-product-Commutative-Ring-𝔽) →
    Id
      ( add-product-Commutative-Ring-𝔽 x (neg-product-Commutative-Ring-𝔽 x))
      ( zero-product-Commutative-Ring-𝔽)
  right-inverse-law-add-product-Commutative-Ring-𝔽 =
    right-inverse-law-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  associative-add-product-Commutative-Ring-𝔽 :
    (x y z : type-product-Commutative-Ring-𝔽) →
    Id
      ( add-product-Commutative-Ring-𝔽 (add-product-Commutative-Ring-𝔽 x y) z)
      ( add-product-Commutative-Ring-𝔽 x (add-product-Commutative-Ring-𝔽 y z))
  associative-add-product-Commutative-Ring-𝔽 =
    associative-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  commutative-add-product-Commutative-Ring-𝔽 :
    (x y : type-product-Commutative-Ring-𝔽) →
    Id (add-product-Commutative-Ring-𝔽 x y) (add-product-Commutative-Ring-𝔽 y x)
  commutative-add-product-Commutative-Ring-𝔽 =
    commutative-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  mul-product-Commutative-Ring-𝔽 :
    type-product-Commutative-Ring-𝔽 →
    type-product-Commutative-Ring-𝔽 →
    type-product-Commutative-Ring-𝔽
  mul-product-Commutative-Ring-𝔽 =
    mul-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  one-product-Commutative-Ring-𝔽 : type-product-Commutative-Ring-𝔽
  one-product-Commutative-Ring-𝔽 =
    one-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  associative-mul-product-Commutative-Ring-𝔽 :
    (x y z : type-product-Commutative-Ring-𝔽) →
    Id
      ( mul-product-Commutative-Ring-𝔽 (mul-product-Commutative-Ring-𝔽 x y) z)
      ( mul-product-Commutative-Ring-𝔽 x (mul-product-Commutative-Ring-𝔽 y z))
  associative-mul-product-Commutative-Ring-𝔽 =
    associative-mul-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-unit-law-mul-product-Commutative-Ring-𝔽 :
    (x : type-product-Commutative-Ring-𝔽) →
    Id (mul-product-Commutative-Ring-𝔽 one-product-Commutative-Ring-𝔽 x) x
  left-unit-law-mul-product-Commutative-Ring-𝔽 =
    left-unit-law-mul-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-unit-law-mul-product-Commutative-Ring-𝔽 :
    (x : type-product-Commutative-Ring-𝔽) →
    Id (mul-product-Commutative-Ring-𝔽 x one-product-Commutative-Ring-𝔽) x
  right-unit-law-mul-product-Commutative-Ring-𝔽 =
    right-unit-law-mul-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  left-distributive-mul-add-product-Commutative-Ring-𝔽 :
    (x y z : type-product-Commutative-Ring-𝔽) →
    Id
      ( mul-product-Commutative-Ring-𝔽 x (add-product-Commutative-Ring-𝔽 y z))
      ( add-product-Commutative-Ring-𝔽
        ( mul-product-Commutative-Ring-𝔽 x y)
        ( mul-product-Commutative-Ring-𝔽 x z))
  left-distributive-mul-add-product-Commutative-Ring-𝔽 =
    left-distributive-mul-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  right-distributive-mul-add-product-Commutative-Ring-𝔽 :
    (x y z : type-product-Commutative-Ring-𝔽) →
    Id
      ( mul-product-Commutative-Ring-𝔽 (add-product-Commutative-Ring-𝔽 x y) z)
      ( add-product-Commutative-Ring-𝔽
        ( mul-product-Commutative-Ring-𝔽 x z)
        ( mul-product-Commutative-Ring-𝔽 y z))
  right-distributive-mul-add-product-Commutative-Ring-𝔽 =
    right-distributive-mul-add-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  semigroup-product-Commutative-Ring-𝔽 : Semigroup (l1 ⊔ l2)
  semigroup-product-Commutative-Ring-𝔽 =
    semigroup-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  group-product-Commutative-Ring-𝔽 : Group (l1 ⊔ l2)
  group-product-Commutative-Ring-𝔽 =
    group-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  ab-product-Commutative-Ring-𝔽 : Ab (l1 ⊔ l2)
  ab-product-Commutative-Ring-𝔽 =
    ab-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  ring-product-Commutative-Ring-𝔽 : Commutative-Ring (l1 ⊔ l2)
  ring-product-Commutative-Ring-𝔽 =
    product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  commutative-mul-product-Commutative-Ring-𝔽 :
    (x y : type-product-Commutative-Ring-𝔽) →
    mul-product-Commutative-Ring-𝔽 x y ＝ mul-product-Commutative-Ring-𝔽 y x
  commutative-mul-product-Commutative-Ring-𝔽 =
    commutative-mul-product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  commutative-ring-product-Commutative-Ring-𝔽 : Commutative-Ring (l1 ⊔ l2)
  commutative-ring-product-Commutative-Ring-𝔽 =
    product-Commutative-Ring
      ( commutative-ring-Commutative-Ring-𝔽 R1)
      ( commutative-ring-Commutative-Ring-𝔽 R2)

  product-Commutative-Ring-𝔽 : Commutative-Ring-𝔽 (l1 ⊔ l2)
  pr1 product-Commutative-Ring-𝔽 =
    product-Ring-𝔽
      ( finite-ring-Commutative-Ring-𝔽 R1)
      ( finite-ring-Commutative-Ring-𝔽 R2)
  pr2 product-Commutative-Ring-𝔽 = commutative-mul-product-Commutative-Ring-𝔽
```
