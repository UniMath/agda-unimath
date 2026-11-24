# Permutation of matrices

```agda
module linear-algebra.permutation-of-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.equivalences
open import foundation.function-types
open import foundation.universe-levels

open import linear-algebra.matrices
```

</details>

## Idea

The rows and columns of a [matrix](linear-algebra.matrices.md) can be permuted.

## Definition

### Permuting the rows of a matrix

```agda
permute-rows-matrix :
  {l : Level} {A : UU l} (m n : ℕ) → Permutation m → matrix A m n → matrix A m n
permute-rows-matrix _ _ σ M = M ∘ map-equiv σ
```

### Permuting the columns of a matrix

```agda
permute-columns-matrix :
  {l : Level} {A : UU l} (m n : ℕ) → Permutation n → matrix A m n → matrix A m n
permute-columns-matrix _ _ σ M i = M i ∘ map-equiv σ
```

## See also

- [Permutation matrices on rings](linear-algebra.permutation-matrices-rings.md)
