# Strictly bounded natural numbers

```agda
module elementary-number-theory.strictly-bounded-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of {{#concept "strictly bounded natural numbers" Agda=strictly-bounded-ℕ}} with strict upper bound $n$ is the type

$$
  \mathbb{N}_{< n} := \{k : ℕ \mid k < n\}.
$$

The type $\mathbb{N}_{\leq n}$ is [equivalent](foundation-core.equivalences.md) to the [standard finite type](univalent-combinatorics.standard-finite-types.md) $\mathsf{Fin}(n+1)$.

## Definition

### The strictly bounded natural numbers

```agda
strictly-bounded-ℕ : ℕ → UU lzero
strictly-bounded-ℕ n = Σ ℕ (λ k → k <-ℕ n)
```

## Properties

### The type $\mathbb{N}_{\leq b}$ is equivalent to the standard finite type $\mathsf{Fin}(n+1)$

```agda
equiv-count-strictly-bounded-ℕ :
  (n : ℕ) → Fin n ≃ strictly-bounded-ℕ n
equiv-count-strictly-bounded-ℕ n = {!!}

count-strictly-bounded-ℕ :
  (n : ℕ) → count (strictly-bounded-ℕ n)
pr1 (count-strictly-bounded-ℕ n) = n
pr2 (count-strictly-bounded-ℕ n) = equiv-count-strictly-bounded-ℕ n
```

## See also

- [The bounded natural numbers](elementary-number-theory.bounded-natural-numbers.md)
