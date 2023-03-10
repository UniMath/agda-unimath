# Function rings

```agda
module ring-theory.function-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.function-abelian-groups
open import group-theory.function-monoids
open import group-theory.monoids

open import ring-theory.rings
```

<details>

## Idea

Given a ring `R` and a type `X`, the exponent ring `R^X` consists of
functions from `X` into the underlying type of `R`. The operations on
`R^X` are defined pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (X : UU l2)
  where

  ab-function-Ring : Ab (l1 ⊔ l2)
  ab-function-Ring = function-Ab (ab-Ring R) X

  multiplicative-monoid-function-Ring : Monoid (l1 ⊔ l2)
  multiplicative-monoid-function-Ring =
    function-Monoid (multiplicative-monoid-Ring R) X
  
  set-function-Ring : Set (l1 ⊔ l2)
  set-function-Ring = function-Set X (set-Ring R)

  type-function-Ring : UU (l1 ⊔ l2)
  type-function-Ring = type-Set set-function-Ring

  zero-function-Ring : type-function-Ring
  zero-function-Ring = zero-function-Ab (ab-Ring R) X

  one-function-Ring : type-function-Ring
  one-function-Ring =
    unit-function-Monoid (multiplicative-monoid-Ring R) X

  add-function-Ring : (f g : type-function-Ring) → type-function-Ring
  add-function-Ring = add-function-Ab (ab-Ring R) X

  neg-function-Ring : type-function-Ring → type-function-Ring
  neg-function-Ring = neg-function-Ab (ab-Ring R) X

  mul-function-Ring : (f g : type-function-Ring) → type-function-Ring
  mul-function-Ring =
    mul-function-Monoid (multiplicative-monoid-Ring R) X

  associative-add-function-Ring :
    (f g h : type-function-Ring) →
    add-function-Ring (add-function-Ring f g) h ＝
    add-function-Ring f (add-function-Ring g h)
  associative-add-function-Ring =
    associative-add-function-Ab (ab-Ring R) X

  commutative-add-function-Ring :
    (f g : type-function-Ring) →
    add-function-Ring f g ＝ add-function-Ring g f
  commutative-add-function-Ring =
    commutative-add-function-Ab (ab-Ring R) X

  left-unit-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring zero-function-Ring f ＝ f
  left-unit-law-add-function-Ring =
    left-unit-law-add-function-Ab (ab-Ring R) X

  right-unit-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring f zero-function-Ring ＝ f
  right-unit-law-add-function-Ring =
    right-unit-law-add-function-Ab (ab-Ring R) X

  left-inverse-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring (neg-function-Ring f) f ＝ zero-function-Ring
  left-inverse-law-add-function-Ring =
    left-inverse-law-add-function-Ab (ab-Ring R) X

  right-inverse-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring f (neg-function-Ring f) ＝ zero-function-Ring
  right-inverse-law-add-function-Ring =
    right-inverse-law-add-function-Ab (ab-Ring R) X

  associative-mul-function-Ring :
    (f g h : type-function-Ring) →
    mul-function-Ring (mul-function-Ring f g) h ＝
    mul-function-Ring f (mul-function-Ring g h)
  associative-mul-function-Ring =
    associative-mul-function-Monoid (multiplicative-monoid-Ring R) X

  left-unit-law-mul-function-Ring :
    (f : type-function-Ring) →
    mul-function-Ring one-function-Ring f ＝ f
  left-unit-law-mul-function-Ring =
    left-unit-law-mul-function-Monoid (multiplicative-monoid-Ring R) X

  right-unit-law-mul-function-Ring :
    (f : type-function-Ring) →
    mul-function-Ring f one-function-Ring ＝ f
  right-unit-law-mul-function-Ring =
    right-unit-law-mul-function-Monoid (multiplicative-monoid-Ring R) X

  left-distributive-mul-add-function-Ring :
    (f g h : type-function-Ring) →
    mul-function-Ring f (add-function-Ring g h) ＝
    add-function-Ring (mul-function-Ring f g) (mul-function-Ring f h)
  left-distributive-mul-add-function-Ring f g h =
    eq-htpy
      ( λ x → left-distributive-mul-add-Ring R (f x) (g x) (h x))

  right-distributive-mul-add-function-Ring :
    (f g h : type-function-Ring) →
    mul-function-Ring (add-function-Ring f g) h ＝
    add-function-Ring (mul-function-Ring f h) (mul-function-Ring g h)
  right-distributive-mul-add-function-Ring f g h =
    eq-htpy
      ( λ x → right-distributive-mul-add-Ring R (f x) (g x) (h x))
```
