# Function semirings

```agda
module ring-theory.function-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids

open import ring-theory.dependent-products-semirings
open import ring-theory.semirings
```

</details>

## Idea

Given a [semiring](ring-theory.semirings.md) `R` and a type `X`, the
{{#concept "exponent semiring" Agda=function-Semiring}} `R^X` consists of
functions from `X` into the underlying type of `R`. The semiring operations are
defined pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (X : UU l2)
  where

  additive-commutative-monoid-function-Semiring : Commutative-Monoid (l1 ⊔ l2)
  additive-commutative-monoid-function-Semiring =
    additive-commutative-monoid-Π-Semiring X (λ _ → R)

  multiplicative-monoid-function-Semiring : Monoid (l1 ⊔ l2)
  multiplicative-monoid-function-Semiring =
    multiplicative-monoid-Π-Semiring X (λ _ → R)

  set-function-Semiring : Set (l1 ⊔ l2)
  set-function-Semiring = set-Π-Semiring X (λ _ → R)

  type-function-Semiring : UU (l1 ⊔ l2)
  type-function-Semiring = type-Π-Semiring X (λ _ → R)

  is-set-type-function-Semiring : is-set type-function-Semiring
  is-set-type-function-Semiring =
    is-set-type-Π-Semiring X (λ _ → R)

  add-function-Semiring :
    type-function-Semiring → type-function-Semiring → type-function-Semiring
  add-function-Semiring = add-Π-Semiring X (λ _ → R)

  zero-function-Semiring : type-function-Semiring
  zero-function-Semiring = zero-Π-Semiring X (λ _ → R)

  associative-add-function-Semiring :
    (x y z : type-function-Semiring) →
    add-function-Semiring (add-function-Semiring x y) z ＝
    add-function-Semiring x (add-function-Semiring y z)
  associative-add-function-Semiring =
    associative-add-Π-Semiring X (λ _ → R)

  left-unit-law-add-function-Semiring :
    (x : type-function-Semiring) →
    add-function-Semiring zero-function-Semiring x ＝ x
  left-unit-law-add-function-Semiring =
    left-unit-law-add-Π-Semiring X (λ _ → R)

  right-unit-law-add-function-Semiring :
    (x : type-function-Semiring) →
    add-function-Semiring x zero-function-Semiring ＝ x
  right-unit-law-add-function-Semiring =
    right-unit-law-add-Π-Semiring X (λ _ → R)

  commutative-add-function-Semiring :
    (x y : type-function-Semiring) →
    add-function-Semiring x y ＝ add-function-Semiring y x
  commutative-add-function-Semiring =
    commutative-add-Π-Semiring X (λ _ → R)

  mul-function-Semiring :
    type-function-Semiring → type-function-Semiring → type-function-Semiring
  mul-function-Semiring =
    mul-Π-Semiring X (λ _ → R)

  one-function-Semiring : type-function-Semiring
  one-function-Semiring = one-Π-Semiring X (λ _ → R)

  associative-mul-function-Semiring :
    (x y z : type-function-Semiring) →
    mul-function-Semiring (mul-function-Semiring x y) z ＝
    mul-function-Semiring x (mul-function-Semiring y z)
  associative-mul-function-Semiring =
    associative-mul-Π-Semiring X (λ _ → R)

  left-unit-law-mul-function-Semiring :
    (x : type-function-Semiring) →
    mul-function-Semiring one-function-Semiring x ＝ x
  left-unit-law-mul-function-Semiring =
    left-unit-law-mul-Π-Semiring X (λ _ → R)

  right-unit-law-mul-function-Semiring :
    (x : type-function-Semiring) →
    mul-function-Semiring x one-function-Semiring ＝ x
  right-unit-law-mul-function-Semiring =
    right-unit-law-mul-Π-Semiring X (λ _ → R)

  left-distributive-mul-add-function-Semiring :
    (f g h : type-function-Semiring) →
    mul-function-Semiring f (add-function-Semiring g h) ＝
    add-function-Semiring
      ( mul-function-Semiring f g)
      ( mul-function-Semiring f h)
  left-distributive-mul-add-function-Semiring =
    left-distributive-mul-add-Π-Semiring X (λ _ → R)

  right-distributive-mul-add-function-Semiring :
    (f g h : type-function-Semiring) →
    mul-function-Semiring (add-function-Semiring f g) h ＝
    add-function-Semiring
      ( mul-function-Semiring f h)
      ( mul-function-Semiring g h)
  right-distributive-mul-add-function-Semiring =
    right-distributive-mul-add-Π-Semiring X (λ _ → R)

  left-zero-law-mul-function-Semiring :
    (f : type-function-Semiring) →
    mul-function-Semiring zero-function-Semiring f ＝ zero-function-Semiring
  left-zero-law-mul-function-Semiring =
    left-zero-law-mul-Π-Semiring X (λ _ → R)

  right-zero-law-mul-function-Semiring :
    (f : type-function-Semiring) →
    mul-function-Semiring f zero-function-Semiring ＝ zero-function-Semiring
  right-zero-law-mul-function-Semiring =
    right-zero-law-mul-Π-Semiring X (λ _ → R)

  function-Semiring : Semiring (l1 ⊔ l2)
  pr1 function-Semiring = additive-commutative-monoid-function-Semiring
  pr1 (pr1 (pr1 (pr2 function-Semiring))) = mul-function-Semiring
  pr2 (pr1 (pr1 (pr2 function-Semiring))) = associative-mul-function-Semiring
  pr1 (pr1 (pr2 (pr1 (pr2 function-Semiring)))) = one-function-Semiring
  pr1 (pr2 (pr1 (pr2 (pr1 (pr2 function-Semiring))))) =
    left-unit-law-mul-function-Semiring
  pr2 (pr2 (pr1 (pr2 (pr1 (pr2 function-Semiring))))) =
    right-unit-law-mul-function-Semiring
  pr1 (pr2 (pr2 (pr1 (pr2 function-Semiring)))) =
    left-distributive-mul-add-function-Semiring
  pr2 (pr2 (pr2 (pr1 (pr2 function-Semiring)))) =
    right-distributive-mul-add-function-Semiring
  pr1 (pr2 (pr2 function-Semiring)) = left-zero-law-mul-function-Semiring
  pr2 (pr2 (pr2 function-Semiring)) = right-zero-law-mul-function-Semiring
```
