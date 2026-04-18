# Matrices on rings

```agda
module linear-algebra.matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.dependent-products-left-modules-rings
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.matrices

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [matrix](linear-algebra.matrices.md) on a [ring](ring-theory.rings.md) is a
matrix whose elements are elements of the ring.

## Definition

```agda
matrix-Ring : {l : Level} → Ring l → ℕ → ℕ → UU l
matrix-Ring R = matrix (type-Ring R)
```

## Properties

### Matrices on a ring form a left module over that ring

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  where

  left-module-matrix-Ring : left-module-Ring l R
  left-module-matrix-Ring =
    Π-left-module-Ring
      ( R)
      ( Fin m)
      ( λ _ → Π-left-module-Ring R (Fin n) (λ _ → left-module-ring-Ring R))

  set-matrix-Ring : Set l
  set-matrix-Ring = set-left-module-Ring R left-module-matrix-Ring

  add-matrix-Ring : matrix-Ring R m n → matrix-Ring R m n → matrix-Ring R m n
  add-matrix-Ring = add-left-module-Ring R left-module-matrix-Ring

  zero-matrix-Ring : matrix-Ring R m n
  zero-matrix-Ring = zero-left-module-Ring R left-module-matrix-Ring

  left-unit-law-add-matrix-Ring :
    (A : matrix-Ring R m n) → add-matrix-Ring zero-matrix-Ring A ＝ A
  left-unit-law-add-matrix-Ring =
    left-unit-law-add-left-module-Ring R left-module-matrix-Ring

  right-unit-law-add-matrix-Ring :
    (A : matrix-Ring R m n) → add-matrix-Ring A zero-matrix-Ring ＝ A
  right-unit-law-add-matrix-Ring =
    right-unit-law-add-left-module-Ring R left-module-matrix-Ring

  associative-add-matrix-Ring :
    (A B C : matrix-Ring R m n) →
    add-matrix-Ring (add-matrix-Ring A B) C ＝
    add-matrix-Ring A (add-matrix-Ring B C)
  associative-add-matrix-Ring =
    associative-add-left-module-Ring R left-module-matrix-Ring

  commutative-add-matrix-Ring :
    (A B : matrix-Ring R m n) →
    add-matrix-Ring A B ＝ add-matrix-Ring B A
  commutative-add-matrix-Ring =
    commutative-add-left-module-Ring R left-module-matrix-Ring

  neg-matrix-Ring : matrix-Ring R m n → matrix-Ring R m n
  neg-matrix-Ring = neg-left-module-Ring R left-module-matrix-Ring

  left-inverse-law-add-matrix-Ring :
    (A : matrix-Ring R m n) →
    add-matrix-Ring (neg-matrix-Ring A) A ＝ zero-matrix-Ring
  left-inverse-law-add-matrix-Ring =
    left-inverse-law-add-left-module-Ring R left-module-matrix-Ring

  right-inverse-law-add-matrix-Ring :
    (A : matrix-Ring R m n) →
    add-matrix-Ring A (neg-matrix-Ring A) ＝ zero-matrix-Ring
  right-inverse-law-add-matrix-Ring =
    right-inverse-law-add-left-module-Ring R left-module-matrix-Ring

  scalar-mul-matrix-Ring : type-Ring R → matrix-Ring R m n → matrix-Ring R m n
  scalar-mul-matrix-Ring =
    mul-left-module-Ring R left-module-matrix-Ring

  left-unit-law-scalar-mul-matrix-Ring :
    (A : matrix-Ring R m n) →
    scalar-mul-matrix-Ring (one-Ring R) A ＝ A
  left-unit-law-scalar-mul-matrix-Ring =
    left-unit-law-mul-left-module-Ring R left-module-matrix-Ring

  associative-scalar-mul-matrix-Ring :
    (r s : type-Ring R) (A : matrix-Ring R m n) →
    scalar-mul-matrix-Ring (mul-Ring R r s) A ＝
    scalar-mul-matrix-Ring r (scalar-mul-matrix-Ring s A)
  associative-scalar-mul-matrix-Ring =
    associative-mul-left-module-Ring R left-module-matrix-Ring

  left-distributive-scalar-mul-add-matrix-Ring :
    (r : type-Ring R) (A B : matrix-Ring R m n) →
    scalar-mul-matrix-Ring r (add-matrix-Ring A B) ＝
    add-matrix-Ring (scalar-mul-matrix-Ring r A) (scalar-mul-matrix-Ring r B)
  left-distributive-scalar-mul-add-matrix-Ring =
    left-distributive-mul-add-left-module-Ring R left-module-matrix-Ring

  right-distributive-scalar-mul-add-matrix-Ring :
    (r s : type-Ring R) (A : matrix-Ring R m n) →
    scalar-mul-matrix-Ring (add-Ring R r s) A ＝
    add-matrix-Ring (scalar-mul-matrix-Ring r A) (scalar-mul-matrix-Ring s A)
  right-distributive-scalar-mul-add-matrix-Ring =
    right-distributive-mul-add-left-module-Ring R left-module-matrix-Ring
```
