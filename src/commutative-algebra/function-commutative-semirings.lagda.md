# Function commutative semirings

```agda
module commutative-algebra.function-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.dependent-products-commutative-semirings

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids

open import ring-theory.semirings
```

</details>

## Idea

Given a commutative semiring `R` and a type `X`, the type `R^X` of functions
from `X` to the underlying type of `R` is again a commutative semiring.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (X : UU l2)
  where

  function-Commutative-Semiring : Commutative-Semiring (l1 ⊔ l2)
  function-Commutative-Semiring =
    Π-Commutative-Semiring X (λ _ → R)

  semiring-function-Commutative-Semiring : Semiring (l1 ⊔ l2)
  semiring-function-Commutative-Semiring =
    semiring-Π-Commutative-Semiring X (λ _ → R)

  additive-commutative-monoid-function-Commutative-Semiring :
    Commutative-Monoid (l1 ⊔ l2)
  additive-commutative-monoid-function-Commutative-Semiring =
    additive-commutative-monoid-Π-Commutative-Semiring X (λ _ → R)

  multiplicative-commutative-monoid-function-Commutative-Semiring :
    Commutative-Monoid (l1 ⊔ l2)
  multiplicative-commutative-monoid-function-Commutative-Semiring =
    multiplicative-commutative-monoid-Π-Commutative-Semiring X (λ _ → R)

  set-function-Commutative-Semiring : Set (l1 ⊔ l2)
  set-function-Commutative-Semiring =
    set-Π-Commutative-Semiring X (λ _ → R)

  type-function-Commutative-Semiring : UU (l1 ⊔ l2)
  type-function-Commutative-Semiring =
    type-Π-Commutative-Semiring X (λ _ → R)

  is-set-type-function-Commutative-Semiring :
    is-set type-function-Commutative-Semiring
  is-set-type-function-Commutative-Semiring =
    is-set-type-Π-Commutative-Semiring X (λ _ → R)

  add-function-Commutative-Semiring :
    type-function-Commutative-Semiring → type-function-Commutative-Semiring →
    type-function-Commutative-Semiring
  add-function-Commutative-Semiring =
    add-Π-Commutative-Semiring X (λ _ → R)

  zero-function-Commutative-Semiring : type-function-Commutative-Semiring
  zero-function-Commutative-Semiring =
    zero-Π-Commutative-Semiring X (λ _ → R)

  associative-add-function-Commutative-Semiring :
    (x y z : type-function-Commutative-Semiring) →
    add-function-Commutative-Semiring
      ( add-function-Commutative-Semiring x y)
      ( z) ＝
    add-function-Commutative-Semiring
      ( x)
      ( add-function-Commutative-Semiring y z)
  associative-add-function-Commutative-Semiring =
    associative-add-Π-Commutative-Semiring X (λ _ → R)

  left-unit-law-add-function-Commutative-Semiring :
    (x : type-function-Commutative-Semiring) →
    add-function-Commutative-Semiring zero-function-Commutative-Semiring x ＝ x
  left-unit-law-add-function-Commutative-Semiring =
    left-unit-law-add-Π-Commutative-Semiring X (λ _ → R)

  right-unit-law-add-function-Commutative-Semiring :
    (x : type-function-Commutative-Semiring) →
    add-function-Commutative-Semiring x zero-function-Commutative-Semiring ＝ x
  right-unit-law-add-function-Commutative-Semiring =
    right-unit-law-add-Π-Commutative-Semiring X (λ _ → R)

  commutative-add-function-Commutative-Semiring :
    (x y : type-function-Commutative-Semiring) →
    add-function-Commutative-Semiring x y ＝
    add-function-Commutative-Semiring y x
  commutative-add-function-Commutative-Semiring =
    commutative-add-Π-Commutative-Semiring X (λ _ → R)

  mul-function-Commutative-Semiring :
    type-function-Commutative-Semiring → type-function-Commutative-Semiring →
    type-function-Commutative-Semiring
  mul-function-Commutative-Semiring =
    mul-Π-Commutative-Semiring X (λ _ → R)

  one-function-Commutative-Semiring : type-function-Commutative-Semiring
  one-function-Commutative-Semiring =
    one-Π-Commutative-Semiring X (λ _ → R)

  associative-mul-function-Commutative-Semiring :
    (x y z : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring
      ( mul-function-Commutative-Semiring x y)
      ( z) ＝
    mul-function-Commutative-Semiring
      ( x)
      ( mul-function-Commutative-Semiring y z)
  associative-mul-function-Commutative-Semiring =
    associative-mul-Π-Commutative-Semiring X (λ _ → R)

  left-unit-law-mul-function-Commutative-Semiring :
    (x : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring one-function-Commutative-Semiring x ＝ x
  left-unit-law-mul-function-Commutative-Semiring =
    left-unit-law-mul-Π-Commutative-Semiring X (λ _ → R)

  right-unit-law-mul-function-Commutative-Semiring :
    (x : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring x one-function-Commutative-Semiring ＝ x
  right-unit-law-mul-function-Commutative-Semiring =
    right-unit-law-mul-Π-Commutative-Semiring X (λ _ → R)

  left-distributive-mul-add-function-Commutative-Semiring :
    (f g h : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring f
      ( add-function-Commutative-Semiring g h) ＝
    add-function-Commutative-Semiring
      ( mul-function-Commutative-Semiring f g)
      ( mul-function-Commutative-Semiring f h)
  left-distributive-mul-add-function-Commutative-Semiring =
    left-distributive-mul-add-Π-Commutative-Semiring X (λ _ → R)

  right-distributive-mul-add-function-Commutative-Semiring :
    (f g h : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring
      ( add-function-Commutative-Semiring f g) h ＝
    add-function-Commutative-Semiring
      ( mul-function-Commutative-Semiring f h)
      ( mul-function-Commutative-Semiring g h)
  right-distributive-mul-add-function-Commutative-Semiring =
    right-distributive-mul-add-Π-Commutative-Semiring X (λ _ → R)

  left-zero-law-mul-function-Commutative-Semiring :
    (f : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring zero-function-Commutative-Semiring f ＝
    zero-function-Commutative-Semiring
  left-zero-law-mul-function-Commutative-Semiring =
    left-zero-law-mul-Π-Commutative-Semiring X (λ _ → R)

  right-zero-law-mul-function-Commutative-Semiring :
    (f : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring f zero-function-Commutative-Semiring ＝
    zero-function-Commutative-Semiring
  right-zero-law-mul-function-Commutative-Semiring =
    right-zero-law-mul-Π-Commutative-Semiring X (λ _ → R)

  commutative-mul-function-Commutative-Semiring :
    (f g : type-function-Commutative-Semiring) →
    mul-function-Commutative-Semiring f g ＝
    mul-function-Commutative-Semiring g f
  commutative-mul-function-Commutative-Semiring =
    commutative-mul-Commutative-Monoid
      multiplicative-commutative-monoid-function-Commutative-Semiring
```
