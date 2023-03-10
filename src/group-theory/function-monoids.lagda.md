# Function monoids

```agda
module group-theory.function-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.function-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

<details>

## Idea

Given a monoid `M` and a type `X`, the function monoid `M^X`
consists of functions from `X` to the underlying type of `M`. The
multiplicative operation and the unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (X : UU l2)
  where

  semigroup-function-Monoid : Semigroup (l1 ⊔ l2)
  semigroup-function-Monoid =
    function-Semigroup (semigroup-Monoid M) X

  set-function-Monoid : Set (l1 ⊔ l2)
  set-function-Monoid = set-Semigroup semigroup-function-Monoid

  type-function-Monoid : UU (l1 ⊔ l2)
  type-function-Monoid = type-Semigroup semigroup-function-Monoid

  mul-function-Monoid :
    (f g : type-function-Monoid) → type-function-Monoid
  mul-function-Monoid = mul-Semigroup semigroup-function-Monoid

  associative-mul-function-Monoid :
    (f g h : type-function-Monoid) →
    mul-function-Monoid (mul-function-Monoid f g) h ＝
    mul-function-Monoid f (mul-function-Monoid g h)
  associative-mul-function-Monoid =
    associative-mul-Semigroup semigroup-function-Monoid

  unit-function-Monoid : type-function-Monoid
  unit-function-Monoid x = unit-Monoid M

  left-unit-law-mul-function-Monoid :
    (f : type-function-Monoid) →
    mul-function-Monoid unit-function-Monoid f ＝ f
  left-unit-law-mul-function-Monoid f =
    eq-htpy (λ x → left-unit-law-mul-Monoid M (f x))

  right-unit-law-mul-function-Monoid :
    (f : type-function-Monoid) →
    mul-function-Monoid f unit-function-Monoid ＝ f
  right-unit-law-mul-function-Monoid f =
    eq-htpy (λ x → right-unit-law-mul-Monoid M (f x))

  is-unital-function-Monoid :
    is-unital-Semigroup semigroup-function-Monoid
  pr1 is-unital-function-Monoid =
    unit-function-Monoid
  pr1 (pr2 is-unital-function-Monoid) =
    left-unit-law-mul-function-Monoid
  pr2 (pr2 is-unital-function-Monoid) =
    right-unit-law-mul-function-Monoid

  function-Monoid : Monoid (l1 ⊔ l2)
  pr1 function-Monoid = semigroup-function-Monoid
  pr2 function-Monoid = is-unital-function-Monoid
```
