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
open import foundation.homotopies
open import foundation.identity-types

open import ring-theory.partial-sums-sequences-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Idea

{{#concept "Triangular nuumbers" Agda=triangular-number-ℕ WD="triangular number" WDID=Q245102}}
are the sequence of
[natural numbers](elementary-number-theory.natural-numbers.md) `Tₙ` defined by :

- `T₀ = 0`;
- `Tₙ₊₁ = Tₙ + n + 1`.

I.e., `Tₙ = Σ (k ≤ n) k`.

## Definition

### Triangular numbers

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ 0 = 0
triangular-number-ℕ (succ-ℕ n) = (triangular-number-ℕ n) +ℕ (succ-ℕ n)
```

### The sums `Σ (k ≤ n) k`

```agda
sum-leq-ℕ : ℕ → ℕ
sum-leq-ℕ = seq-sum-sequence-Semiring ℕ-Semiring (λ k → k)
```

## Properties

### The nth triangular number is the sum `Σ (k ≤ n) k`

```agda
htpy-sum-leq-triangular-ℕ : triangular-number-ℕ ~ sum-leq-ℕ
htpy-sum-leq-triangular-ℕ zero-ℕ = refl
htpy-sum-leq-triangular-ℕ (succ-ℕ n) =
  ap (add-ℕ' (succ-ℕ n)) (htpy-sum-leq-triangular-ℕ n)
```

## External references

- [Triangular number](https://en.wikipedia.org/wiki/Triangular_number) at
  Wikipedia.
