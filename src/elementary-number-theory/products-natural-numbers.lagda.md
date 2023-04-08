# Products of natural numbers

```agda
module elementary-number-theory.products-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import lists.lists
```

</details>

## Idea

The product of a list of natural numbers is defined by iterated multiplication.

## Definitions

### Products of lists of natural numbers

```agda
product-list-ℕ : list ℕ → ℕ
product-list-ℕ = fold-list 1 mul-ℕ
```

### Product of families of natural numbers indexed by a standard finite type

## Properties
