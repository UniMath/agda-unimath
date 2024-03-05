# The positive integers

```agda
module elementary-number-theory.positive-integers where
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

The positive integers are `one-ℤ` and its successors.

## Defintions

### Positive integers

```agda
subtype-positive-ℤ : subtype lzero ℤ
subtype-positive-ℤ (inl x) = empty-Prop
subtype-positive-ℤ (inr (inl x)) = empty-Prop
subtype-positive-ℤ (inr (inr x)) = unit-Prop

is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ = is-in-subtype subtype-positive-ℤ

positive-ℤ : UU lzero
positive-ℤ = type-subtype subtype-positive-ℤ

is-positive-eq-ℤ : {x y : ℤ} → x ＝ y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ {x} refl = id

module _
  (p : positive-ℤ)
  where

  int-positive-ℤ : ℤ
  int-positive-ℤ = pr1 p

  is-positive-int-positive-ℤ : is-positive-ℤ int-positive-ℤ
  is-positive-int-positive-ℤ = pr2 p
```

### Positive constants

```agda
one-positive-ℤ : positive-ℤ
one-positive-ℤ = one-ℤ , star
```

## Properties

### The positive integers are a `Set`

```agda
is-set-positive-ℤ : is-set positive-ℤ
is-set-positive-ℤ =
  is-set-emb
    ( emb-subtype subtype-positive-ℤ)
    ( is-set-ℤ)
```

### The successor of a positive integer is positive

```agda
is-positive-succ-is-positive-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-positive-ℤ (succ-ℤ x)
is-positive-succ-is-positive-ℤ (inr (inr x)) H = H

succ-positive-ℤ : positive-ℤ → positive-ℤ
succ-positive-ℤ (x , H) = succ-ℤ x , is-positive-succ-is-positive-ℤ x H
```

### The integer image of a nonzero natural number is positive

```agda
is-positive-int-is-nonzero-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
is-positive-int-is-nonzero-ℕ zero-ℕ H = ex-falso (H refl)
is-positive-int-is-nonzero-ℕ (succ-ℕ x) H = star
```

### The canonical equivalence between natural numbers and positive integers

```agda
positive-int-ℕ : ℕ → positive-ℤ
positive-int-ℕ = rec-ℕ one-positive-ℤ (λ _ → succ-positive-ℤ)

nat-positive-ℤ : positive-ℤ → ℕ
nat-positive-ℤ (inr (inr x) , H) = x
```

TODO
