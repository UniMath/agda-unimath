# Function commutative rings

```agda
module commutative-algebra.function-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.dependent-products-commutative-rings

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids

open import linear-algebra.dependent-products-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings

open import ring-theory.rings
```

</details>

## Idea

Given a [commutative ring](commutative-algebra.commutative-rings.md) `A` and a
type `X`, the type `A^X` of functions from `X` into the underlying type of `A`
is a commutative ring, and a
[left module](linear-algebra.left-modules-rings.md).

## Definition

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (X : UU l2)
  where

  function-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  function-Commutative-Ring = Π-Commutative-Ring X (λ _ → A)

  ring-function-Commutative-Ring : Ring (l1 ⊔ l2)
  ring-function-Commutative-Ring =
    ring-Commutative-Ring function-Commutative-Ring

  ab-function-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-function-Commutative-Ring =
    ab-Commutative-Ring function-Commutative-Ring

  multiplicative-commutative-monoid-function-Commutative-Ring :
    Commutative-Monoid (l1 ⊔ l2)
  multiplicative-commutative-monoid-function-Commutative-Ring =
    multiplicative-commutative-monoid-Commutative-Ring function-Commutative-Ring

  set-function-Commutative-Ring : Set (l1 ⊔ l2)
  set-function-Commutative-Ring = set-Ring ring-function-Commutative-Ring

  type-function-Commutative-Ring : UU (l1 ⊔ l2)
  type-function-Commutative-Ring = type-Ring ring-function-Commutative-Ring

  is-set-type-function-Commutative-Ring : is-set type-function-Commutative-Ring
  is-set-type-function-Commutative-Ring =
    is-set-type-Commutative-Ring function-Commutative-Ring

  add-function-Commutative-Ring :
    type-function-Commutative-Ring → type-function-Commutative-Ring →
    type-function-Commutative-Ring
  add-function-Commutative-Ring =
    add-Commutative-Ring function-Commutative-Ring

  zero-function-Commutative-Ring : type-function-Commutative-Ring
  zero-function-Commutative-Ring =
    zero-Commutative-Ring function-Commutative-Ring

  associative-add-function-Commutative-Ring :
    (x y z : type-function-Commutative-Ring) →
    add-function-Commutative-Ring (add-function-Commutative-Ring x y) z ＝
    add-function-Commutative-Ring x (add-function-Commutative-Ring y z)
  associative-add-function-Commutative-Ring =
    associative-add-Commutative-Ring function-Commutative-Ring

  left-unit-law-add-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    add-function-Commutative-Ring zero-function-Commutative-Ring x ＝ x
  left-unit-law-add-function-Commutative-Ring =
    left-unit-law-add-Commutative-Ring function-Commutative-Ring

  right-unit-law-add-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    add-function-Commutative-Ring x zero-function-Commutative-Ring ＝ x
  right-unit-law-add-function-Commutative-Ring =
    right-unit-law-add-Commutative-Ring function-Commutative-Ring

  commutative-add-function-Commutative-Ring :
    (x y : type-function-Commutative-Ring) →
    add-function-Commutative-Ring x y ＝ add-function-Commutative-Ring y x
  commutative-add-function-Commutative-Ring =
    commutative-add-Commutative-Ring function-Commutative-Ring

  mul-function-Commutative-Ring :
    type-function-Commutative-Ring → type-function-Commutative-Ring →
    type-function-Commutative-Ring
  mul-function-Commutative-Ring =
    mul-Commutative-Ring function-Commutative-Ring

  one-function-Commutative-Ring : type-function-Commutative-Ring
  one-function-Commutative-Ring =
    one-Commutative-Ring function-Commutative-Ring

  associative-mul-function-Commutative-Ring :
    (x y z : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring (mul-function-Commutative-Ring x y) z ＝
    mul-function-Commutative-Ring x (mul-function-Commutative-Ring y z)
  associative-mul-function-Commutative-Ring =
    associative-mul-Commutative-Ring function-Commutative-Ring

  left-unit-law-mul-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring one-function-Commutative-Ring x ＝ x
  left-unit-law-mul-function-Commutative-Ring =
    left-unit-law-mul-Commutative-Ring function-Commutative-Ring

  right-unit-law-mul-function-Commutative-Ring :
    (x : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring x one-function-Commutative-Ring ＝ x
  right-unit-law-mul-function-Commutative-Ring =
    right-unit-law-mul-Commutative-Ring function-Commutative-Ring

  left-distributive-mul-add-function-Commutative-Ring :
    (f g h : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring f (add-function-Commutative-Ring g h) ＝
    add-function-Commutative-Ring
      ( mul-function-Commutative-Ring f g)
      ( mul-function-Commutative-Ring f h)
  left-distributive-mul-add-function-Commutative-Ring =
    left-distributive-mul-add-Commutative-Ring function-Commutative-Ring

  right-distributive-mul-add-function-Commutative-Ring :
    (f g h : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring (add-function-Commutative-Ring f g) h ＝
    add-function-Commutative-Ring
      ( mul-function-Commutative-Ring f h)
      ( mul-function-Commutative-Ring g h)
  right-distributive-mul-add-function-Commutative-Ring =
    right-distributive-mul-add-Commutative-Ring function-Commutative-Ring

  left-zero-law-mul-function-Commutative-Ring :
    (f : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring zero-function-Commutative-Ring f ＝
    zero-function-Commutative-Ring
  left-zero-law-mul-function-Commutative-Ring =
    left-zero-law-mul-Commutative-Ring function-Commutative-Ring

  right-zero-law-mul-function-Commutative-Ring :
    (f : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring f zero-function-Commutative-Ring ＝
    zero-function-Commutative-Ring
  right-zero-law-mul-function-Commutative-Ring =
    right-zero-law-mul-Commutative-Ring function-Commutative-Ring

  commutative-mul-function-Commutative-Ring :
    (f g : type-function-Commutative-Ring) →
    mul-function-Commutative-Ring f g ＝ mul-function-Commutative-Ring g f
  commutative-mul-function-Commutative-Ring =
    commutative-mul-Commutative-Ring function-Commutative-Ring
```

## Properties

### The function commutative ring is a left module over the commutative ring

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (X : UU l2)
  where

  left-module-function-Commutative-Ring :
    left-module-Commutative-Ring (l1 ⊔ l2) R
  left-module-function-Commutative-Ring =
    Π-left-module-Commutative-Ring R X
      ( λ _ → left-module-commutative-ring-Commutative-Ring R)
```
