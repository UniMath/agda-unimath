# Matrices on commutative rings

```agda
module linear-algebra.matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.matrices-on-rings
```

</details>

## Idea

A [matrix](linear-algebra.matrices.md) on a
[commutative ring](commutative-algebra.commutative-rings.md) is a matrix whose
elements are elements of the ring.

## Definition

```agda
matrix-Commutative-Ring : {l : Level} → Commutative-Ring l → ℕ → ℕ → UU l
matrix-Commutative-Ring R = matrix-Ring (ring-Commutative-Ring R)
```

## Properties

### Matrices on a commutative ring form a left module over that ring

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n : ℕ)
  where

  left-module-matrix-Commutative-Ring : left-module-Commutative-Ring l R
  left-module-matrix-Commutative-Ring =
    left-module-matrix-Ring (ring-Commutative-Ring R) m n

  set-matrix-Commutative-Ring : Set l
  set-matrix-Commutative-Ring =
    set-left-module-Commutative-Ring R left-module-matrix-Commutative-Ring

  add-matrix-Commutative-Ring :
    matrix-Commutative-Ring R m n → matrix-Commutative-Ring R m n →
    matrix-Commutative-Ring R m n
  add-matrix-Commutative-Ring =
    add-left-module-Commutative-Ring R left-module-matrix-Commutative-Ring

  zero-matrix-Commutative-Ring : matrix-Commutative-Ring R m n
  zero-matrix-Commutative-Ring =
    zero-left-module-Commutative-Ring R left-module-matrix-Commutative-Ring

  left-unit-law-add-matrix-Commutative-Ring :
    (A : matrix-Commutative-Ring R m n) →
    add-matrix-Commutative-Ring zero-matrix-Commutative-Ring A ＝ A
  left-unit-law-add-matrix-Commutative-Ring =
    left-unit-law-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  right-unit-law-add-matrix-Commutative-Ring :
    (A : matrix-Commutative-Ring R m n) →
    add-matrix-Commutative-Ring A zero-matrix-Commutative-Ring ＝ A
  right-unit-law-add-matrix-Commutative-Ring =
    right-unit-law-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  associative-add-matrix-Commutative-Ring :
    (A B C : matrix-Commutative-Ring R m n) →
    add-matrix-Commutative-Ring (add-matrix-Commutative-Ring A B) C ＝
    add-matrix-Commutative-Ring A (add-matrix-Commutative-Ring B C)
  associative-add-matrix-Commutative-Ring =
    associative-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  commutative-add-matrix-Commutative-Ring :
    (A B : matrix-Commutative-Ring R m n) →
    add-matrix-Commutative-Ring A B ＝ add-matrix-Commutative-Ring B A
  commutative-add-matrix-Commutative-Ring =
    commutative-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  neg-matrix-Commutative-Ring :
    matrix-Commutative-Ring R m n → matrix-Commutative-Ring R m n
  neg-matrix-Commutative-Ring =
    neg-left-module-Commutative-Ring R left-module-matrix-Commutative-Ring

  left-inverse-law-add-matrix-Commutative-Ring :
    (A : matrix-Commutative-Ring R m n) →
    add-matrix-Commutative-Ring (neg-matrix-Commutative-Ring A) A ＝
    zero-matrix-Commutative-Ring
  left-inverse-law-add-matrix-Commutative-Ring =
    left-inverse-law-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  right-inverse-law-add-matrix-Commutative-Ring :
    (A : matrix-Commutative-Ring R m n) →
    add-matrix-Commutative-Ring A (neg-matrix-Commutative-Ring A) ＝
    zero-matrix-Commutative-Ring
  right-inverse-law-add-matrix-Commutative-Ring =
    right-inverse-law-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  scalar-mul-matrix-Commutative-Ring :
    type-Commutative-Ring R → matrix-Commutative-Ring R m n →
    matrix-Commutative-Ring R m n
  scalar-mul-matrix-Commutative-Ring =
    mul-left-module-Commutative-Ring R left-module-matrix-Commutative-Ring

  left-unit-law-scalar-mul-matrix-Commutative-Ring :
    (A : matrix-Commutative-Ring R m n) →
    scalar-mul-matrix-Commutative-Ring (one-Commutative-Ring R) A ＝ A
  left-unit-law-scalar-mul-matrix-Commutative-Ring =
    left-unit-law-mul-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  associative-scalar-mul-matrix-Commutative-Ring :
    (r s : type-Commutative-Ring R) (A : matrix-Commutative-Ring R m n) →
    scalar-mul-matrix-Commutative-Ring (mul-Commutative-Ring R r s) A ＝
    scalar-mul-matrix-Commutative-Ring
      ( r)
      ( scalar-mul-matrix-Commutative-Ring s A)
  associative-scalar-mul-matrix-Commutative-Ring =
    associative-mul-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  left-distributive-scalar-mul-add-matrix-Commutative-Ring :
    (r : type-Commutative-Ring R) (A B : matrix-Commutative-Ring R m n) →
    scalar-mul-matrix-Commutative-Ring r (add-matrix-Commutative-Ring A B) ＝
    add-matrix-Commutative-Ring
      ( scalar-mul-matrix-Commutative-Ring r A)
      ( scalar-mul-matrix-Commutative-Ring r B)
  left-distributive-scalar-mul-add-matrix-Commutative-Ring =
    left-distributive-mul-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)

  right-distributive-scalar-mul-add-matrix-Commutative-Ring :
    (r s : type-Commutative-Ring R) (A : matrix-Commutative-Ring R m n) →
    scalar-mul-matrix-Commutative-Ring (add-Commutative-Ring R r s) A ＝
    add-matrix-Commutative-Ring
      ( scalar-mul-matrix-Commutative-Ring r A)
      ( scalar-mul-matrix-Commutative-Ring s A)
  right-distributive-scalar-mul-add-matrix-Commutative-Ring =
    right-distributive-mul-add-left-module-Commutative-Ring
      ( R)
      ( left-module-matrix-Commutative-Ring)
```
