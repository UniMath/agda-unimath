# Products of natural numbers

```agda
module elementary-number-theory.products-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.coproduct-types
open import foundation.function-types
open import foundation.identity-types
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

## Properties

### The product of one natural number is that natural number itself

```agda
unit-law-Π-ℕ : (f : Fin 1 → ℕ) (x : Fin 1) → Π-ℕ 1 f ＝ f x
unit-law-Π-ℕ f (inr star) = left-unit-law-mul-ℕ _
```

### Any nonempty product of natural numbers greater than 1 is greater than 1

```agda
le-one-Π-ℕ :
  (k : ℕ) (f : Fin k → ℕ) →
  0 <-ℕ k → ((i : Fin k) → 1 <-ℕ f i) → 1 <-ℕ Π-ℕ k f
le-one-Π-ℕ (succ-ℕ zero-ℕ) f H K =
  concatenate-le-eq-ℕ (K (inr star)) (inv (unit-law-Π-ℕ f (inr star)))
le-one-Π-ℕ (succ-ℕ (succ-ℕ k)) f H K =
  le-one-mul-ℕ
    ( Π-ℕ (succ-ℕ k) (f ∘ inl))
    ( f (inr star))
    ( le-one-Π-ℕ (succ-ℕ k) (f ∘ inl) star (K ∘ inl))
    ( K (inr star))
```
