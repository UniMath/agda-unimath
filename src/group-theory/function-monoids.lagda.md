# Function monoids

```agda
module group-theory.function-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.dependent-products-monoids
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

Given a monoid `M` and a type `X`, the function monoid `M^X` consists of
functions from `X` to the underlying type of `M`. The multiplicative operation
and the unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (X : UU l2)
  where

  function-Monoid : Monoid (l1 ⊔ l2)
  function-Monoid = Π-Monoid X (λ _ → M)

  semigroup-function-Monoid : Semigroup (l1 ⊔ l2)
  semigroup-function-Monoid = semigroup-Π-Monoid X (λ _ → M)

  set-function-Monoid : Set (l1 ⊔ l2)
  set-function-Monoid = set-Π-Monoid X (λ _ → M)

  type-function-Monoid : UU (l1 ⊔ l2)
  type-function-Monoid = type-Π-Monoid X (λ _ → M)

  mul-function-Monoid :
    (f g : type-function-Monoid) → type-function-Monoid
  mul-function-Monoid = mul-Π-Monoid X (λ _ → M)

  associative-mul-function-Monoid :
    (f g h : type-function-Monoid) →
    mul-function-Monoid (mul-function-Monoid f g) h ＝
    mul-function-Monoid f (mul-function-Monoid g h)
  associative-mul-function-Monoid =
    associative-mul-Π-Monoid X (λ _ → M)

  unit-function-Monoid : type-function-Monoid
  unit-function-Monoid = unit-Π-Monoid X (λ _ → M)

  left-unit-law-mul-function-Monoid :
    (f : type-function-Monoid) →
    mul-function-Monoid unit-function-Monoid f ＝ f
  left-unit-law-mul-function-Monoid =
    left-unit-law-mul-Π-Monoid X (λ _ → M)

  right-unit-law-mul-function-Monoid :
    (f : type-function-Monoid) →
    mul-function-Monoid f unit-function-Monoid ＝ f
  right-unit-law-mul-function-Monoid =
    right-unit-law-mul-Π-Monoid X (λ _ → M)

  is-unital-function-Monoid :
    is-unital-Semigroup semigroup-function-Monoid
  is-unital-function-Monoid = is-unital-Π-Monoid X (λ _ → M)
```
