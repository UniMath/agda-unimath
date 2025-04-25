# Diagonal tuples

```agda
module linear-algebra.constant-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import lists.tuples
```

</details>

## Idea

Diagonal tuples are [tuples](lists.tuples.md) on the diagonal, i.e., they are
tuples of which all coefficients are equal.

## Definition

```agda
constant-tuple : {l : Level} {A : UU l} {n : ℕ} → A → tuple A n
constant-tuple {n = zero-ℕ} _ = empty-tuple
constant-tuple {n = succ-ℕ n} x = x ∷ (constant-tuple x)
```
