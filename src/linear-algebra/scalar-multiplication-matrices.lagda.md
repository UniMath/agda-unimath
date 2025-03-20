# Scalar multiplication on matrices

```agda
open import foundation.function-extensionality-axiom

module
  linear-algebra.scalar-multiplication-matrices
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.matrices funext
open import linear-algebra.scalar-multiplication-vectors funext
```

</details>

```agda
scalar-mul-matrix :
  {l1 l2 : Level} {B : UU l1} {A : UU l2} {m n : ℕ} →
  (B → A → A) → B → matrix A m n → matrix A m n
scalar-mul-matrix μ = scalar-mul-vec (scalar-mul-vec μ)
```
