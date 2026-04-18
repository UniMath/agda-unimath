# Diagonals of square matrices

```agda
module linear-algebra.diagonals-of-square-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.square-matrices

open import lists.finite-sequences
```

</details>

## Idea

The
{{#concept "diagonal" Disambiguation="of a square matrix" WD="diagonal of a matrix" WDID=Q77966258 Agda=diagonal-square-matrix}}
of an `n × n` [square matrix](linear-algebra.square-matrices.md) `A` is the
[finite sequence](lists.finite-sequences.md) of length `n` defined by
`dᵢ = Aᵢᵢ`.

## Definition

```agda
diagonal-square-matrix :
  {l : Level} {A : UU l} (n : ℕ) → square-matrix A n → fin-sequence A n
diagonal-square-matrix n A i = A i i
```
