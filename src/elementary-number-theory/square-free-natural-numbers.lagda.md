# Square-free natural numbers

```agda
module elementary-number-theory.square-free-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
```

</details>

## Idea

A natural number `n` is said to be square-free if `x² | n ⇒ x = 1` for any
natural number `x`.

## Definition

```agda
is-square-free-ℕ : ℕ → UU lzero
is-square-free-ℕ n = (x : ℕ) → div-ℕ (square-ℕ x) n → is-one-ℕ x
```
