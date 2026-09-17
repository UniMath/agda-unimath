# Grids on rings

```agda
module linear-algebra.grids-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.constant-grids
open import linear-algebra.functoriality-grids
open import linear-algebra.grids
open import linear-algebra.tuples-on-rings

open import lists.tuples

open import ring-theory.rings
```

</details>

## Definitions

A [grid](linear-algebra.grids.md) on a [ring](ring-theory.rings.md) is a grid
whose elements are elements of the ring.

### Grids

```agda
module _
  {l : Level} (R : Ring l)
  where

  grid-Ring : ℕ → ℕ → UU l
  grid-Ring m n = grid (type-Ring R) m n
```

### The zero grid

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-grid-Ring : {m n : ℕ} → grid-Ring R m n
  zero-grid-Ring = constant-grid (zero-Ring R)
```

### Addition of grids on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-grid-Ring : {m n : ℕ} (A B : grid-Ring R m n) → grid-Ring R m n
  add-grid-Ring = binary-map-grid (add-Ring R)
```

## Properties

### Addition of grids is associative

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-grid-Ring :
    {m n : ℕ} (A B C : grid-Ring R m n) →
    add-grid-Ring R (add-grid-Ring R A B) C ＝
    add-grid-Ring R A (add-grid-Ring R B C)
  associative-add-grid-Ring empty-tuple empty-tuple empty-tuple = refl
  associative-add-grid-Ring (v ∷ A) (w ∷ B) (z ∷ C) =
    ap-binary _∷_
      ( associative-add-tuple-Ring R v w z)
      ( associative-add-grid-Ring A B C)
```

### Addition of grids is commutative

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-grid-Ring :
    {m n : ℕ} (A B : grid-Ring R m n) →
    add-grid-Ring R A B ＝ add-grid-Ring R B A
  commutative-add-grid-Ring empty-tuple empty-tuple = refl
  commutative-add-grid-Ring (v ∷ A) (w ∷ B) =
    ap-binary _∷_
      ( commutative-add-tuple-Ring R v w)
      ( commutative-add-grid-Ring A B)
```

### Left unit law for addition of grids

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-grid-Ring :
    {m n : ℕ} (A : grid-Ring R m n) →
    add-grid-Ring R (zero-grid-Ring R) A ＝ A
  left-unit-law-add-grid-Ring empty-tuple = refl
  left-unit-law-add-grid-Ring (v ∷ A) =
    ap-binary _∷_
      ( left-unit-law-add-tuple-Ring R v)
      ( left-unit-law-add-grid-Ring A)
```

### Right unit law for addition of grids

```agda
module _
  {l : Level} (R : Ring l)
  where

  right-unit-law-add-grid-Ring :
    {m n : ℕ} (A : grid-Ring R m n) →
    add-grid-Ring R A (zero-grid-Ring R) ＝ A
  right-unit-law-add-grid-Ring empty-tuple = refl
  right-unit-law-add-grid-Ring (v ∷ A) =
    ap-binary _∷_
      ( right-unit-law-add-tuple-Ring R v)
      ( right-unit-law-add-grid-Ring A)
```
