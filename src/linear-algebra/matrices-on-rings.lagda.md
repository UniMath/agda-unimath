# Matrices on rings

```agda
module linear-algebra.matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.constant-matrices
open import linear-algebra.functoriality-matrices
open import linear-algebra.matrices
open import linear-algebra.tuples-on-rings

open import lists.tuples

open import ring-theory.rings
```

</details>

## Definitions

A [matrix](linear-algebra.matrices.md) on a [ring](ring-theory.rings.md) is a
matrix whose elements are elements of the ring.

### Matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  matrix-Ring : ℕ → ℕ → UU l
  matrix-Ring m n = matrix (type-Ring R) m n
```

### The zero matrix

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-matrix-Ring : {m n : ℕ} → matrix-Ring R m n
  zero-matrix-Ring = constant-matrix (zero-Ring R)
```

### Addition of matrices on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-matrix-Ring : {m n : ℕ} (A B : matrix-Ring R m n) → matrix-Ring R m n
  add-matrix-Ring = binary-map-matrix (add-Ring R)
```

## Properties

### Addition of matrices is associative

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-matrix-Ring :
    {m n : ℕ} (A B C : matrix-Ring R m n) →
    Id
      ( add-matrix-Ring R (add-matrix-Ring R A B) C)
      ( add-matrix-Ring R A (add-matrix-Ring R B C))
  associative-add-matrix-Ring empty-tuple empty-tuple empty-tuple = refl
  associative-add-matrix-Ring (v ∷ A) (w ∷ B) (z ∷ C) =
    ap-binary _∷_
      ( associative-add-tuple-Ring R v w z)
      ( associative-add-matrix-Ring A B C)
```

### Addition of matrices is commutative

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-matrix-Ring :
    {m n : ℕ} (A B : matrix-Ring R m n) →
    add-matrix-Ring R A B ＝ add-matrix-Ring R B A
  commutative-add-matrix-Ring empty-tuple empty-tuple = refl
  commutative-add-matrix-Ring (v ∷ A) (w ∷ B) =
    ap-binary _∷_
      ( commutative-add-tuple-Ring R v w)
      ( commutative-add-matrix-Ring A B)
```

### Left unit law for addition of matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-matrix-Ring :
    {m n : ℕ} (A : matrix-Ring R m n) →
    Id (add-matrix-Ring R (zero-matrix-Ring R) A) A
  left-unit-law-add-matrix-Ring empty-tuple = refl
  left-unit-law-add-matrix-Ring (v ∷ A) =
    ap-binary _∷_
      ( left-unit-law-add-tuple-Ring R v)
      ( left-unit-law-add-matrix-Ring A)
```

### Right unit law for addition of matrices

```agda
module _
  {l : Level} (R : Ring l)
  where

  right-unit-law-add-matrix-Ring :
    {m n : ℕ} (A : matrix-Ring R m n) →
    Id (add-matrix-Ring R A (zero-matrix-Ring R)) A
  right-unit-law-add-matrix-Ring empty-tuple = refl
  right-unit-law-add-matrix-Ring (v ∷ A) =
    ap-binary _∷_
      ( right-unit-law-add-tuple-Ring R v)
      ( right-unit-law-add-matrix-Ring A)
```
