# Products of natural numbers

```agda
module elementary-number-theory.products-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.unit-type

open import lists.lists

open import univalent-combinatorics.standard-finite-types
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

### Products of families of natural numbers indexed by standard finite types

```agda
Π-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
Π-ℕ zero-ℕ x = 1
Π-ℕ (succ-ℕ k) x = (Π-ℕ k (λ i → x (inl i))) *ℕ (x (inr star))
```
