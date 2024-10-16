# Telephone numbers

```agda
module elementary-number-theory.telephone-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The
{{#concept "telephone numbers" WD="Telephone number" WDID=Q7696507 Agda=telephone-number}}
are a sequence of natural numbers that count the way `n` telephone lines can be
connected to each other, where each line can be connected to at most one other
line. They also occur in several other combinatorics problems.

## Definitions

```agda
telephone-number : ℕ → ℕ
telephone-number zero-ℕ = succ-ℕ zero-ℕ
telephone-number (succ-ℕ zero-ℕ) = succ-ℕ zero-ℕ
telephone-number (succ-ℕ (succ-ℕ n)) =
  (telephone-number (succ-ℕ n)) +ℕ ((succ-ℕ n) *ℕ (telephone-number n))
```
