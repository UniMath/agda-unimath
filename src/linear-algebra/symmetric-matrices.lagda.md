# Symmetric matrices

```agda
module linear-algebra.symmetric-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.square-matrices
open import linear-algebra.transposition-matrices
```

</details>

## Idea

A
{{#concept "symmetric matrix" WDID=Q339011 WD="symmetric matrix" Agda=is-symmetric-square-matrix}}
is a [square matrix](linear-algebra.square-matrices.md) `M` with `Mᵢⱼ = Mⱼᵢ` for
all `i` and `j`.

## Definition

```agda
is-symmetric-square-matrix :
  {l : Level} {A : UU l} (n : ℕ) → square-matrix A n → UU l
is-symmetric-square-matrix n M =
  binary-htpy (transpose-square-matrix n M) M
```
