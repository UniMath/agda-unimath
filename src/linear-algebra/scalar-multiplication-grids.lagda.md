# Scalar multiplication on grids

```agda
module linear-algebra.scalar-multiplication-grids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.grids
open import linear-algebra.scalar-multiplication-tuples
```

</details>

```agda
scalar-mul-grid :
  {l1 l2 : Level} {B : UU l1} {A : UU l2} {m n : ℕ} →
  (B → A → A) → B → grid A m n → grid A m n
scalar-mul-grid μ = scalar-mul-tuple (scalar-mul-tuple μ)
```
