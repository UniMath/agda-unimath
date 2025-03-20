# Constant matrices

```agda
open import foundation.function-extensionality-axiom

module
  linear-algebra.constant-matrices
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-vectors funext
open import linear-algebra.matrices funext
```

</details>

## Idea

Constant matrices are matrices in which all elements are the same.

## Definition

```agda
constant-matrix : {l : Level} {A : UU l} {m n : ℕ} → A → matrix A m n
constant-matrix a = constant-vec (constant-vec a)
```
