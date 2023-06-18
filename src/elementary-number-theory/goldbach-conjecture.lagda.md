# The Goldbach conjecture

```agda
module elementary-number-theory.goldbach-conjecture where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Conjecture

```agda
Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (le-ℕ 2 n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime-ℕ p) × (Σ ℕ (λ q → (is-prime-ℕ q) × (p +ℕ q ＝ n))))
```
