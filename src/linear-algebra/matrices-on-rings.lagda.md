# Matrices on rings

```agda
module linear-algebra.matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.matrices

open import ring-theory.rings
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

### Matrices in a ring form a set

```agda
set-matrix-Ring : {l : Level} → Ring l → ℕ → ℕ → Set l
set-matrix-Ring R = matrix-Set (set-Ring R)
```
