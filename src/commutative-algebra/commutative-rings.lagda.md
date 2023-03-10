# Commutative rings

```agda
module commutative-algebra.commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

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

  add-Commutative-Ring' :
    type-Commutative-Ring → type-Commutative-Ring → type-Commutative-Ring
  add-Commutative-Ring' = add-Ring' ring-Commutative-Ring

  ap-add-Commutative-Ring :
    {x x' y y' : type-Commutative-Ring} →
    (x ＝ x') → (y ＝ y') →
    add-Commutative-Ring x y ＝ add-Commutative-Ring x' y'
  ap-add-Commutative-Ring = ap-add-Ring ring-Commutative-Ring

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

  interchange-add-add-Commutative-Ring :
    (x y x' y' : type-Commutative-Ring) →
    ( add-Commutative-Ring
      ( add-Commutative-Ring x y)
      ( add-Commutative-Ring x' y')) ＝
    ( add-Commutative-Ring
      ( add-Commutative-Ring x x')
      ( add-Commutative-Ring y y'))
  interchange-add-add-Commutative-Ring =
    interchange-add-add-Ring ring-Commutative-Ring

  right-swap-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( add-Commutative-Ring (add-Commutative-Ring x y) z) ＝
    ( add-Commutative-Ring (add-Commutative-Ring x z) y)
  right-swap-add-Commutative-Ring =
    right-swap-add-Ring ring-Commutative-Ring

  left-swap-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( add-Commutative-Ring x (add-Commutative-Ring y z)) ＝
    ( add-Commutative-Ring y (add-Commutative-Ring x z))
  left-swap-add-Commutative-Ring =
    left-swap-add-Ring ring-Commutative-Ring

  mul-Commutative-Ring : (x y : type-Commutative-Ring) → type-Commutative-Ring
  mul-Commutative-Ring = mul-Ring ring-Commutative-Ring

  mul-Commutative-Ring' : (x y : type-Commutative-Ring) → type-Commutative-Ring
  mul-Commutative-Ring' = mul-Ring' ring-Commutative-Ring

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

  associative-mul-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring (mul-Commutative-Ring x y) z ＝
    mul-Commutative-Ring x (mul-Commutative-Ring y z)
  associative-mul-Commutative-Ring =
    associative-mul-Ring ring-Commutative-Ring

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

  left-zero-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring zero-Commutative-Ring x ＝
    zero-Commutative-Ring
  left-zero-law-mul-Commutative-Ring =
    left-zero-law-mul-Ring ring-Commutative-Ring

  right-zero-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring x zero-Commutative-Ring ＝
    zero-Commutative-Ring
  right-zero-law-mul-Commutative-Ring =
    right-zero-law-mul-Ring ring-Commutative-Ring

  right-swap-mul-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring (mul-Commutative-Ring x y) z ＝
    mul-Commutative-Ring (mul-Commutative-Ring x z) y
  right-swap-mul-Commutative-Ring x y z =
    ( associative-mul-Commutative-Ring x y z) ∙
    ( ( ap
        ( mul-Commutative-Ring x)
        ( commutative-mul-Commutative-Ring y z)) ∙
      ( inv (associative-mul-Commutative-Ring x z y)))

  left-swap-mul-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring x (mul-Commutative-Ring y z) ＝
    mul-Commutative-Ring y (mul-Commutative-Ring x z)
  left-swap-mul-Commutative-Ring x y z =
    ( inv (associative-mul-Commutative-Ring x y z)) ∙
    ( ( ap
        ( mul-Commutative-Ring' z)
        ( commutative-mul-Commutative-Ring x y)) ∙
      ( associative-mul-Commutative-Ring y x z))
```

### Scalar multiplication of elements of a commutative ring by natural numbers

```agda
  mul-nat-scalar-Commutative-Ring :
    ℕ → type-Commutative-Ring → type-Commutative-Ring
  mul-nat-scalar-Commutative-Ring =
    mul-nat-scalar-Ring ring-Commutative-Ring

  ap-mul-nat-scalar-Commutative-Ring :
    {m n : ℕ} {x y : type-Commutative-Ring} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Commutative-Ring m x ＝
    mul-nat-scalar-Commutative-Ring n y
  ap-mul-nat-scalar-Commutative-Ring =
    ap-mul-nat-scalar-Ring ring-Commutative-Ring

  left-unit-law-mul-nat-scalar-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-nat-scalar-Commutative-Ring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Commutative-Ring =
    left-unit-law-mul-nat-scalar-Ring ring-Commutative-Ring

  left-nat-scalar-law-mul-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring) →
    mul-Commutative-Ring (mul-nat-scalar-Commutative-Ring n x) y ＝
    mul-nat-scalar-Commutative-Ring n (mul-Commutative-Ring x y)
  left-nat-scalar-law-mul-Commutative-Ring =
    left-nat-scalar-law-mul-Ring ring-Commutative-Ring

  right-nat-scalar-law-mul-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring) →
    mul-Commutative-Ring x (mul-nat-scalar-Commutative-Ring n y) ＝
    mul-nat-scalar-Commutative-Ring n (mul-Commutative-Ring x y)
  right-nat-scalar-law-mul-Commutative-Ring =
    right-nat-scalar-law-mul-Ring ring-Commutative-Ring

  left-distributive-mul-nat-scalar-add-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring) →
    mul-nat-scalar-Commutative-Ring n (add-Commutative-Ring x y) ＝
    add-Commutative-Ring
      ( mul-nat-scalar-Commutative-Ring n x)
      ( mul-nat-scalar-Commutative-Ring n y)
  left-distributive-mul-nat-scalar-add-Commutative-Ring =
    left-distributive-mul-nat-scalar-add-Ring ring-Commutative-Ring

  right-distributive-mul-nat-scalar-add-Commutative-Ring :
    (m n : ℕ) (x : type-Commutative-Ring) →
    mul-nat-scalar-Commutative-Ring (add-ℕ m n) x ＝
    add-Commutative-Ring
      ( mul-nat-scalar-Commutative-Ring m x)
      ( mul-nat-scalar-Commutative-Ring n x)
  right-distributive-mul-nat-scalar-add-Commutative-Ring =
    right-distributive-mul-nat-scalar-add-Ring ring-Commutative-Ring
```
