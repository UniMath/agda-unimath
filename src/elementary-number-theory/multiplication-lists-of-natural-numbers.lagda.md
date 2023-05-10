# Product of the element of a list of natural numbers

```agda
module elementary-number-theory.multiplication-lists-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import lists.lists
```

</details>

## Idea

Given a list of natural number `l`, we define the product of the element of the
list.

## Definition

```agda
mul-list-ℕ :
  list ℕ → ℕ
mul-list-ℕ = fold-list 1 mul-ℕ
```
