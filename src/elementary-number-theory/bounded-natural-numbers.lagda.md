# Bounded natural numbers

```agda
module elementary-number-theory.bounded-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of {{#concept "bounded natural numbers" Agda=bounded-ℕ}} with upper bound $n$ is the type

$$
  \mathbb{N}_{\leq n} := \{k : ℕ \mid k \leq n\}.
$$

The type $\mathbb{N}_{\leq n}$ is [equivalent](foundation-core.equivalences.md) to the [standard finite type](univalent-combinatorics.standard-finite-types.md) $\mathsf{Fin}(n+1)$.

## Definition

### The bounded natural numbers

```agda
bounded-ℕ : ℕ → UU lzero
bounded-ℕ n = Σ ℕ (λ k → k ≤-ℕ n)
```

## Properties

### The type $\mathbb{N}_{\leq b}$ is equivalent to the standard finite type $\mathsf{Fin}(n+1)$

```agda
equiv-count-bounded-ℕ :
  (n : ℕ) → Fin (succ-ℕ n) ≃ bounded-ℕ n
equiv-count-bounded-ℕ n = {!!}

count-bounded-ℕ :
  (n : ℕ) → count (bounded-ℕ n)
pr1 (count-bounded-ℕ n) = succ-ℕ n
pr2 (count-bounded-ℕ n) = equiv-count-bounded-ℕ n
```

## See also

- [The strictly bounded natural numbers](elementary-number-theory.strictly-bounded-natural-numbers.md)
