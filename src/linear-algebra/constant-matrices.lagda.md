# Constant matrices

```agda
module linear-algebra.constant-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-tuples
open import linear-algebra.matrices
```

</details>

## Idea

Constant matrices are [matrices](linear-algebra.matrices.md) in which all
elements are the same.

## Definition

```agda
constant-matrix : {l : Level} {A : UU l} {m n : ℕ} → A → matrix A m n
constant-matrix a = constant-tuple (constant-tuple a)
```
