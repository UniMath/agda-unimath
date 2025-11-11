# Complex vector spaces

```agda
module linear-algebra.complex-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.local-ring-of-complex-numbers

open import foundation.universe-levels

open import linear-algebra.vector-spaces
```

</details>

## Idea

```agda
ℂ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℂ-Vector-Space l1 l2 = Vector-Space l2 (local-commutative-ring-ℂ l1)
```
