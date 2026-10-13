# Transposition of matrices

```agda
module linear-algebra.transposition-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.involutions
open import foundation.universe-levels

open import linear-algebra.matrices
open import linear-algebra.square-matrices
```

</details>

## Idea

The
{{#concept "transpose" WDID=Q77961711 WD="matrix transposition" Agda=transpose-matrix}}
of a [matrix](linear-algebra.matrices.md) `M` is the matrix `Mᵀᵢⱼ ≔ Mⱼᵢ`.

## Definition

```agda
transpose-matrix :
  {l : Level} {A : UU l} (m n : ℕ) → matrix A m n → matrix A n m
transpose-matrix m n M i j = M j i

transpose-square-matrix :
  {l : Level} {A : UU l} (n : ℕ) → square-matrix A n → square-matrix A n
transpose-square-matrix n = transpose-matrix n n
```
