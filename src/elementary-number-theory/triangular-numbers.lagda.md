# The triangular numbers

```agda
module elementary-number-theory.triangular-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types

open import ring-theory.series-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Definition

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ 0 = 0
triangular-number-ℕ (succ-ℕ n) = (triangular-number-ℕ n) +ℕ (succ-ℕ n)
```

## Properties

### The nth triangular number is the sum `Σ (k ≤ n) k`

```agda
htpy-sum-fin-triangular-number-ℕ :
  (n : ℕ) →
  seq-sum-sequence-Semiring
    ( ℕ-Semiring)
    ( λ k → k)
    ( n) ＝
  triangular-number-ℕ n
htpy-sum-fin-triangular-number-ℕ zero-ℕ = refl
htpy-sum-fin-triangular-number-ℕ (succ-ℕ n) =
  ap
    ( add-ℕ' (succ-ℕ n))
    ( htpy-sum-fin-triangular-number-ℕ n)
```
