# Diagonal vectors

```agda
module linear-algebra.constant-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.vectors
```

</details>

## Idea

Diagonal vectors are vectors on the diagonal, i.e., they are vectors of which all coefficients are equal.

## Definition

```agda
constant-vec : {l : Level} {A : UU l} {n : ℕ} → A → vec A n
constant-vec {n = zero-ℕ} _ = empty-vec
constant-vec {n = succ-ℕ n} x = x ∷ (constant-vec x)
```
