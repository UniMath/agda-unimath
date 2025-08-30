# The triangular numbers

```agda
module elementary-number-theory.triangular-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications

open import ring-theory.partial-sums-sequences-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings
```

</details>

## Idea

{{#concept "Triangular numbers" WD="triangular number" WDID=Q245102 OEIS=A000217 Agda=triangular-number-ℕ}}
are the sequence of
[natural numbers](elementary-number-theory.natural-numbers.md) `Tₙ` defined by:

- `T₀ = 0`;
- `Tₙ₊₁ = Tₙ + n + 1`.

I.e., `Tₙ = Σ (k ≤ n) k`. The nth triangular number is equal to `n(n+1)/2`.

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

### Twice the nth triangular number is `n(n+1)`

```agda
compute-twice-triangular-number-ℕ :
  (n : ℕ) → (triangular-number-ℕ n) +ℕ (triangular-number-ℕ n) ＝ n *ℕ succ-ℕ n
compute-twice-triangular-number-ℕ zero-ℕ = refl
compute-twice-triangular-number-ℕ (succ-ℕ n) =
  ( interchange-law-add-add-ℕ
    ( triangular-number-ℕ n)
    ( succ-ℕ n)
    ( triangular-number-ℕ n)
    ( succ-ℕ n)) ∙
  ( ap-add-ℕ
    ( compute-twice-triangular-number-ℕ n)
    ( inv (left-two-law-mul-ℕ (succ-ℕ n)))) ∙
  ( inv (right-distributive-mul-add-ℕ n 2 (succ-ℕ n))) ∙
  ( commutative-mul-ℕ (n +ℕ 2) (succ-ℕ n))
```

### The nth triangular number is `n(n+1)/2`

```agda
module _
  (n : ℕ)
  where

  compute-triangular-number-ℕ :
    Σ ( div-ℕ 2 (n *ℕ succ-ℕ n))
      ( λ H → quotient-div-ℕ 2 (n *ℕ succ-ℕ n) H ＝ triangular-number-ℕ n)
  pr1 (pr1 compute-triangular-number-ℕ) = triangular-number-ℕ n
  pr2 (pr1 compute-triangular-number-ℕ) =
    ( right-two-law-mul-ℕ (triangular-number-ℕ n)) ∙
    ( compute-twice-triangular-number-ℕ n)
  pr2 compute-triangular-number-ℕ = refl
```

## External references

- [Triangular number](https://en.wikipedia.org/wiki/Triangular_number) at
  Wikipedia.
- [A000217](https://oeis.org/A000217) in the OEIS
