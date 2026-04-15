# Matrices

```agda
module linear-algebra.matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

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
  top-row-matrix M = M (neg-one-Fin m)
```

### The vertical tail of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  vertical-tail-matrix : matrix A (succ-ℕ m) n → matrix A m n
  vertical-tail-matrix M i = M (inl-Fin m i)
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
  first-column-matrix M i = M i (neg-one-Fin n)
```

### The horizontal tail of a matrix

```agda
module _
  {l : Level}
  {A : UU l}
  (m n : ℕ)
  where

  horizontal-tail-matrix : matrix A m (succ-ℕ n) → matrix A m n
  horizontal-tail-matrix M i j = M i (inl-Fin n j)
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

## See also

- [Grids](linear-algebra.grids.md), the analogous concept but with
  [tuples](lists.tuples.md) in the role of
  [finite sequences](lists.finite-sequences.md)
