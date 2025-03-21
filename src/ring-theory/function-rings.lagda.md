# Function rings

```agda
module ring-theory.function-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.monoids

open import ring-theory.dependent-products-rings
open import ring-theory.rings
```

</details>

## Idea

Given a ring `R` and a type `X`, the exponent ring `R^X` consists of functions
from `X` into the underlying type of `R`. The operations on `R^X` are defined
pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (X : UU l2)
  where

  function-Ring : Ring (l1 ⊔ l2)
  function-Ring = Π-Ring X (λ _ → R)

  ab-function-Ring : Ab (l1 ⊔ l2)
  ab-function-Ring = ab-Π-Ring X (λ _ → R)

  multiplicative-monoid-function-Ring : Monoid (l1 ⊔ l2)
  multiplicative-monoid-function-Ring =
    multiplicative-monoid-Π-Ring X (λ _ → R)

  set-function-Ring : Set (l1 ⊔ l2)
  set-function-Ring = set-Π-Ring X (λ _ → R)

  type-function-Ring : UU (l1 ⊔ l2)
  type-function-Ring = type-Π-Ring X (λ _ → R)

  zero-function-Ring : type-function-Ring
  zero-function-Ring = zero-Π-Ring X (λ _ → R)

  one-function-Ring : type-function-Ring
  one-function-Ring = one-Π-Ring X (λ _ → R)

  add-function-Ring : (f g : type-function-Ring) → type-function-Ring
  add-function-Ring = add-Π-Ring X (λ _ → R)

  neg-function-Ring : type-function-Ring → type-function-Ring
  neg-function-Ring = neg-Π-Ring X (λ _ → R)

  mul-function-Ring : (f g : type-function-Ring) → type-function-Ring
  mul-function-Ring = mul-Π-Ring X (λ _ → R)

  associative-add-function-Ring :
    (f g h : type-function-Ring) →
    add-function-Ring (add-function-Ring f g) h ＝
    add-function-Ring f (add-function-Ring g h)
  associative-add-function-Ring = associative-add-Π-Ring X (λ _ → R)

  commutative-add-function-Ring :
    (f g : type-function-Ring) →
    add-function-Ring f g ＝ add-function-Ring g f
  commutative-add-function-Ring = commutative-add-Π-Ring X (λ _ → R)

  left-unit-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring zero-function-Ring f ＝ f
  left-unit-law-add-function-Ring =
    left-unit-law-add-Π-Ring X (λ _ → R)

  right-unit-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring f zero-function-Ring ＝ f
  right-unit-law-add-function-Ring =
    right-unit-law-add-Π-Ring X (λ _ → R)

  left-inverse-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring (neg-function-Ring f) f ＝ zero-function-Ring
  left-inverse-law-add-function-Ring =
    left-inverse-law-add-Π-Ring X (λ _ → R)

  right-inverse-law-add-function-Ring :
    (f : type-function-Ring) →
    add-function-Ring f (neg-function-Ring f) ＝ zero-function-Ring
  right-inverse-law-add-function-Ring =
    right-inverse-law-add-Π-Ring X (λ _ → R)

  associative-mul-function-Ring :
    (f g h : type-function-Ring) →
    mul-function-Ring (mul-function-Ring f g) h ＝
    mul-function-Ring f (mul-function-Ring g h)
  associative-mul-function-Ring =
    associative-mul-Π-Ring X (λ _ → R)

  left-unit-law-mul-function-Ring :
    (f : type-function-Ring) →
    mul-function-Ring one-function-Ring f ＝ f
  left-unit-law-mul-function-Ring =
    left-unit-law-mul-Π-Ring X (λ _ → R)

  right-unit-law-mul-function-Ring :
    (f : type-function-Ring) →
    mul-function-Ring f one-function-Ring ＝ f
  right-unit-law-mul-function-Ring =
    right-unit-law-mul-Π-Ring X (λ _ → R)

  left-distributive-mul-add-function-Ring :
    (f g h : type-function-Ring) →
    mul-function-Ring f (add-function-Ring g h) ＝
    add-function-Ring (mul-function-Ring f g) (mul-function-Ring f h)
  left-distributive-mul-add-function-Ring =
    left-distributive-mul-add-Π-Ring X (λ _ → R)

  right-distributive-mul-add-function-Ring :
    (f g h : type-function-Ring) →
    mul-function-Ring (add-function-Ring f g) h ＝
    add-function-Ring (mul-function-Ring f h) (mul-function-Ring g h)
  right-distributive-mul-add-function-Ring =
    right-distributive-mul-add-Π-Ring X (λ _ → R)
```
