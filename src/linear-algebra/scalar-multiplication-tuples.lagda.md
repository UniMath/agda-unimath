# Scalar multiplication of tuples

```agda
module linear-algebra.scalar-multiplication-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.functoriality-tuples
open import linear-algebra.tuples
```

</details>

## Idea

Any operation `B → A → A` for some type `B` of formal scalars induces an
operation `B → tuple n A → tuple n A`.

## Definition

```agda
scalar-mul-tuple :
  {l1 l2 : Level} {B : UU l1} {A : UU l2} {n : ℕ} →
  (B → A → A) → B → tuple A n → tuple A n
scalar-mul-tuple μ x = map-tuple (μ x)
```
