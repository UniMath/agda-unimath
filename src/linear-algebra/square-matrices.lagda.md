# Square matrices

```agda
module linear-algebra.square-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.matrices
```

</details>

## Idea

A
{{#concept "square matrix" WD="square matrix" WDID=Q2739329 Agda=square-matrix}}
is a [matrix](linear-algebra.matrices.md) that is `n × n` for some `n`.

## Definition

```agda
square-matrix : {l : Level} → UU l → ℕ → UU l
square-matrix A n = matrix A n n
```
