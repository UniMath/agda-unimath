# Matrices

```agda
module linear-algebra.matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An `m × n` {{#concept "matrix" Agda=matrix WD="matrix" WDID=Q44337}} of elements
in `A` is a [finite sequence](lists.finite-sequences.md) of length `m` of finite
sequences of length `n` in `A`.

## Definition

```agda
matrix : {l : Level} (A : UU l) → ℕ → ℕ → UU l
matrix A m n = fin-sequence (fin-sequence A n) m
```

## Properties

### The top row of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  top-row-matrix : matrix A (succ-ℕ m) n → fin-sequence A n
  top-row-matrix = head-fin-sequence m
```

### The vertical tail of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  vertical-tail-matrix : matrix A (succ-ℕ m) n → matrix A m n
  vertical-tail-matrix = tail-fin-sequence m
```

### The bottom row of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  bottom-row-matrix : matrix A (succ-ℕ m) n → fin-sequence A n
  bottom-row-matrix M = M (zero-Fin m)
```

### The vertical initial segment of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  vertical-init-matrix : matrix A (succ-ℕ m) n → matrix A m n
  vertical-init-matrix M i = M (skip-zero-Fin m i)
```

### The first column of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  first-column-matrix : matrix A m (succ-ℕ n) → fin-sequence A m
  first-column-matrix M = head-fin-sequence n ∘ M
```

### The horizontal tail of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  horizontal-tail-matrix : matrix A m (succ-ℕ n) → matrix A m n
  horizontal-tail-matrix M = tail-fin-sequence n ∘ M
```

### The last column of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  last-column-matrix : matrix A m (succ-ℕ n) → fin-sequence A m
  last-column-matrix M i = M i (zero-Fin n)
```

### The horizontal initial segment of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  horizontal-init-matrix : matrix A m (succ-ℕ n) → matrix A m n
  horizontal-init-matrix M i j = M i (skip-zero-Fin n j)
```

### Truncation of matrix types

```agda
abstract
  is-trunc-matrix :
    (k : 𝕋) {l : Level} {A : UU l} (m n : ℕ) →
    is-trunc k A →
    is-trunc k (matrix A m n)
  is-trunc-matrix k m n tA =
    is-trunc-function-type k (is-trunc-function-type k tA)

matrix-Set : {l : Level} → Set l → ℕ → ℕ → Set l
matrix-Set (A , is-set-A) m n =
  ( matrix A m n ,
    is-trunc-matrix zero-𝕋 m n is-set-A)
```

## See also

- [Grids](linear-algebra.grids.md), the analogous concept but with
  [tuples](lists.tuples.md) in the role of
  [finite sequences](lists.finite-sequences.md)
- [Square matrices](linear-algebra.square-matrices.md)
- [Matrices on rings](linear-algebra.matrices-on-rings.md)
