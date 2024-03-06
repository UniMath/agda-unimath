# The negative integers

```agda
module elementary-number-theory.negative-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
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

The negative integers are `neg-one-ℤ` and its predecessors.

## Defintions

### Negative integers

```agda
is-negative-ℤ : ℤ → UU lzero
is-negative-ℤ (inl k) = unit
is-negative-ℤ (inr k) = empty

is-prop-is-negative-ℤ : (x : ℤ) → is-prop (is-negative-ℤ x)
is-prop-is-negative-ℤ (inl x) = is-prop-unit
is-prop-is-negative-ℤ (inr x) = is-prop-empty

subtype-negative-ℤ : subtype lzero ℤ
subtype-negative-ℤ x = is-negative-ℤ x , is-prop-is-negative-ℤ x

negative-ℤ : UU lzero
negative-ℤ = type-subtype subtype-negative-ℤ

module _
  (p : negative-ℤ)
  where

  int-negative-ℤ : ℤ
  int-negative-ℤ = pr1 p

  is-negative-int-negative-ℤ : is-negative-ℤ int-negative-ℤ
  is-negative-int-negative-ℤ = pr2 p
```

### Negative constants

```agda
neg-one-negative-ℤ : negative-ℤ
neg-one-negative-ℤ = neg-one-ℤ , star
```

## Properties

### Negativity is decidable

```agda
is-decidable-is-negative-ℤ : is-decidable-fam is-negative-ℤ
is-decidable-is-negative-ℤ (inl x) = inl star
is-decidable-is-negative-ℤ (inr x) = inr id
```

### The negative integers are a `Set`

```agda
is-set-negative-ℤ : is-set negative-ℤ
is-set-negative-ℤ =
  is-set-emb
    ( emb-subtype subtype-negative-ℤ)
    ( is-set-ℤ)
```

### The predecessor of a negative integer is negative

```agda
is-negative-pred-is-negative-ℤ :
  (x : ℤ) → is-negative-ℤ x → is-negative-ℤ (pred-ℤ x)
is-negative-pred-is-negative-ℤ (inl x) H = H

pred-negative-ℤ : negative-ℤ → negative-ℤ
pred-negative-ℤ (x , H) = pred-ℤ x , is-negative-pred-is-negative-ℤ x H
```

### The canonical equivalence between natural numbers and negative integers

```agda
negative-int-ℕ : ℕ → negative-ℤ
negative-int-ℕ = rec-ℕ neg-one-negative-ℤ (λ _ → pred-negative-ℤ)

nat-negative-ℤ : negative-ℤ → ℕ
nat-negative-ℤ (inl x , H) = x
```

TODO
