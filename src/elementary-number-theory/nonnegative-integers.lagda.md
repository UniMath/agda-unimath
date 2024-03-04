# The nonnegative integers

```agda
module elementary-number-theory.nonnegative-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The nonnegative integers are `zero-ℤ` and its successors.

## Definitions

### Nonnegative integers

```agda
subtype-nonnegative-ℤ : subtype lzero ℤ
subtype-nonnegative-ℤ (inl x) = empty-Prop
subtype-nonnegative-ℤ (inr x) = unit-Prop

*is-nonnegative-ℤ : ℤ → UU lzero
*is-nonnegative-ℤ = is-in-subtype subtype-nonnegative-ℤ

*nonnegative-ℤ : UU lzero
*nonnegative-ℤ = type-subtype subtype-nonnegative-ℤ

module _
  (p : *nonnegative-ℤ)
  where

  *int-nonnegative-ℤ : ℤ
  *int-nonnegative-ℤ = pr1 p

  *is-nonnegative-int-nonnegative-ℤ : *is-nonnegative-ℤ *int-nonnegative-ℤ
  *is-nonnegative-int-nonnegative-ℤ = pr2 p
```

### Nonnegative integer constants

```agda
zero-nonnegative-ℤ : *nonnegative-ℤ
zero-nonnegative-ℤ = zero-ℤ , star

one-nonnegative-ℤ : *nonnegative-ℤ
one-nonnegative-ℤ = one-ℤ , star
```

## Properties

### The successor of a nonnegative integer is nonnegative

```agda
is-nonnegative-succ-nonnegative-ℤ :
  (x : ℤ) → *is-nonnegative-ℤ x → *is-nonnegative-ℤ (succ-ℤ x)
is-nonnegative-succ-nonnegative-ℤ (inr (inl x)) H = H
is-nonnegative-succ-nonnegative-ℤ (inr (inr x)) H = H

succ-nonnegative-ℤ : *nonnegative-ℤ → *nonnegative-ℤ
succ-nonnegative-ℤ (x , H) = succ-ℤ x , is-nonnegative-succ-nonnegative-ℤ x H
```

### The integer image of a natural number is nonnegative

```agda
*is-nonnegative-int-ℕ : (n : ℕ) → *is-nonnegative-ℤ (int-ℕ n)
*is-nonnegative-int-ℕ zero-ℕ = star
*is-nonnegative-int-ℕ (succ-ℕ n) = star
```

### The canonical equivalence between natural numbers and nonnegative integers

```agda
*nonnegative-int-ℕ : ℕ → *nonnegative-ℤ
*nonnegative-int-ℕ n = int-ℕ n , *is-nonnegative-int-ℕ n

*nat-nonnegative-ℤ : *nonnegative-ℤ → ℕ
*nat-nonnegative-ℤ (inr (inl x) , H) = zero-ℕ
*nat-nonnegative-ℤ (inr (inr x) , H) = succ-ℕ x
```

-- TODO
