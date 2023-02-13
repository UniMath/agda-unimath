{{#title  Commutative rings}}

```agda
module commutative-algebra.commutative-rings where

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.rings
```

## Idea

A ring `R` is said to be commutative if its multiplicative operation is commutative, i.e., if `xy = yx` for all `x, y ∈ R`.

## Definition

```agda
is-commutative-Ring :
  { l : Level} → Ring l → UU l
is-commutative-Ring R =
  (x y : type-Ring R) → mul-Ring R x y ＝ mul-Ring R y x

is-prop-is-commutative-Ring :
  { l : Level} (R : Ring l) → is-prop (is-commutative-Ring R)
is-prop-is-commutative-Ring R =
  is-prop-Π
    ( λ x →
      is-prop-Π
      ( λ y →
        is-set-type-Ring R (mul-Ring R x y) (mul-Ring R y x)))

Commutative-Ring :
  ( l : Level) → UU (lsuc l)
Commutative-Ring l = Σ (Ring l) is-commutative-Ring

module _
  {l : Level} (R : Commutative-Ring l)
  where
  
  ring-Commutative-Ring : Ring l
  ring-Commutative-Ring = pr1 R

  set-Commutative-Ring : Set l
  set-Commutative-Ring = set-Ring ring-Commutative-Ring

  type-Commutative-Ring : UU l
  type-Commutative-Ring = type-Ring ring-Commutative-Ring

  is-set-type-Commutative-Ring : is-set type-Commutative-Ring
  is-set-type-Commutative-Ring = is-set-type-Ring ring-Commutative-Ring

  zero-Commutative-Ring : type-Commutative-Ring
  zero-Commutative-Ring = zero-Ring ring-Commutative-Ring

  is-zero-Commutative-Ring : type-Commutative-Ring → UU l
  is-zero-Commutative-Ring = is-zero-Ring ring-Commutative-Ring

  is-nonzero-Commutative-Ring : type-Commutative-Ring → UU l
  is-nonzero-Commutative-Ring = is-nonzero-Ring ring-Commutative-Ring

  add-Commutative-Ring :
    type-Commutative-Ring → type-Commutative-Ring → type-Commutative-Ring
  add-Commutative-Ring = add-Ring ring-Commutative-Ring

  neg-Commutative-Ring : type-Commutative-Ring → type-Commutative-Ring
  neg-Commutative-Ring = neg-Ring ring-Commutative-Ring

  associative-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( add-Commutative-Ring (add-Commutative-Ring x y) z) ＝
    ( add-Commutative-Ring x (add-Commutative-Ring y z))
  associative-add-Commutative-Ring =
    associative-add-Ring ring-Commutative-Ring

  left-unit-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring zero-Commutative-Ring x ＝ x
  left-unit-law-add-Commutative-Ring =
    left-unit-law-add-Ring ring-Commutative-Ring

  right-unit-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring x zero-Commutative-Ring ＝ x
  right-unit-law-add-Commutative-Ring =
    right-unit-law-add-Ring ring-Commutative-Ring

  left-inverse-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring (neg-Commutative-Ring x) x ＝ zero-Commutative-Ring
  left-inverse-law-add-Commutative-Ring =
    left-inverse-law-add-Ring ring-Commutative-Ring

  right-inverse-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring x (neg-Commutative-Ring x) ＝ zero-Commutative-Ring
  right-inverse-law-add-Commutative-Ring =
    right-inverse-law-add-Ring ring-Commutative-Ring

  commutative-add-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    add-Commutative-Ring x y ＝ add-Commutative-Ring y x
  commutative-add-Commutative-Ring =
    commutative-add-Ring ring-Commutative-Ring

  mul-Commutative-Ring : (x y : type-Commutative-Ring) → type-Commutative-Ring
  mul-Commutative-Ring = mul-Ring ring-Commutative-Ring

  one-Commutative-Ring : type-Commutative-Ring
  one-Commutative-Ring = one-Ring ring-Commutative-Ring

  left-unit-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring one-Commutative-Ring x ＝ x
  left-unit-law-mul-Commutative-Ring =
    left-unit-law-mul-Ring ring-Commutative-Ring

  right-unit-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring x one-Commutative-Ring ＝ x
  right-unit-law-mul-Commutative-Ring =
    right-unit-law-mul-Ring ring-Commutative-Ring

  left-distributive-mul-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( mul-Commutative-Ring x (add-Commutative-Ring y z)) ＝
    ( add-Commutative-Ring
      ( mul-Commutative-Ring x y)
      ( mul-Commutative-Ring x z))
  left-distributive-mul-add-Commutative-Ring =
    left-distributive-mul-add-Ring ring-Commutative-Ring

  right-distributive-mul-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( mul-Commutative-Ring (add-Commutative-Ring x y) z) ＝
    ( add-Commutative-Ring
      ( mul-Commutative-Ring x z)
      ( mul-Commutative-Ring y z))
  right-distributive-mul-add-Commutative-Ring =
    right-distributive-mul-add-Ring ring-Commutative-Ring

  commutative-mul-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    mul-Commutative-Ring x y ＝ mul-Commutative-Ring y x
  commutative-mul-Commutative-Ring = pr2 R
```
