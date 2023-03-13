# Nonzero natural numbers

```agda
module elementary-number-theory.nonzero-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

The type of nonzero natural numbers consists of natural numbers equipped with a
proof that they are nonzero.

## Definitions

### The type of nonzero natural numbers

```agda
nonzero-ℕ : UU lzero
nonzero-ℕ = Σ ℕ is-nonzero-ℕ

nat-nonzero-ℕ : nonzero-ℕ → ℕ
nat-nonzero-ℕ = pr1

is-nonzero-nat-nonzero-ℕ : (n : nonzero-ℕ) → is-nonzero-ℕ (nat-nonzero-ℕ n)
is-nonzero-nat-nonzero-ℕ = pr2

one-nonzero-ℕ : nonzero-ℕ
pr1 one-nonzero-ℕ = 1
pr2 one-nonzero-ℕ = is-nonzero-one-ℕ

succ-nonzero-ℕ : nonzero-ℕ → nonzero-ℕ
pr1 (succ-nonzero-ℕ (pair x _)) = succ-ℕ x
pr2 (succ-nonzero-ℕ (pair x _)) = is-nonzero-succ-ℕ x

succ-nonzero-ℕ' : ℕ → nonzero-ℕ
pr1 (succ-nonzero-ℕ' n) = succ-ℕ n
pr2 (succ-nonzero-ℕ' n) = is-nonzero-succ-ℕ n
```

```agda
quotient-div-nonzero-ℕ :
  (d : ℕ) (x : nonzero-ℕ) (H : div-ℕ d (pr1 x)) → nonzero-ℕ
pr1 (quotient-div-nonzero-ℕ d (pair x K) H) = quotient-div-ℕ d x H
pr2 (quotient-div-nonzero-ℕ d (pair x K) H) = is-nonzero-quotient-div-ℕ H K
```
