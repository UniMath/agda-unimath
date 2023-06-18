# Stirling numbers of the second kind

```agda
module elementary-number-theory.stirling-numbers-of-the-second-kind where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The stirling number of the second kind `{n m}` is the number of surjective maps
from the standard `n`-element set to the standard `m`-element set

## Definition

```agda
stirling-number-second-kind : ℕ → ℕ → ℕ
stirling-number-second-kind zero-ℕ zero-ℕ = 1
stirling-number-second-kind zero-ℕ (succ-ℕ n) = 0
stirling-number-second-kind (succ-ℕ m) zero-ℕ = 0
stirling-number-second-kind (succ-ℕ m) (succ-ℕ n) =
  ( (succ-ℕ n) *ℕ (stirling-number-second-kind m (succ-ℕ n))) +ℕ
  ( stirling-number-second-kind m n)
```
