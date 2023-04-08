# Sums of natural numbers

```agda
module elementary-number-theory.sums-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import lists.lists
```

</details>

## Idea

We define the sum of a list of natural numbers.

## Definition

```agda
sum-list-ℕ : list ℕ → ℕ
sum-list-ℕ = fold-list 0 add-ℕ
```

## Properties
