# Real vector spaces

```agda
module linear-algebra.real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import linear-algebra.vector-spaces

open import real-numbers.local-ring-of-real-numbers
```

</details>

## Idea

```agda
ℝ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℝ-Vector-Space l1 l2 = Vector-Space l2 (local-commutative-ring-ℝ l1)
```
