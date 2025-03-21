# Scalar multiplication on matrices

```agda
module linear-algebra.scalar-multiplication-matrices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.matrices
open import linear-algebra.scalar-multiplication-vectors
```

</details>

```agda
scalar-mul-matrix :
  {l1 l2 : Level} {B : UU l1} {A : UU l2} {m n : ℕ} →
  (B → A → A) → B → matrix A m n → matrix A m n
scalar-mul-matrix μ = scalar-mul-vec (scalar-mul-vec μ)
```
