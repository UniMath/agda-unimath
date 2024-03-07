# The nonpositive integers

```agda
module elementary-number-theory.nonpositive-integers where
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

The nonpositive integers are `zero-ℤ` and its predecessors.

## Defintions

### Nonnpositive integers

```agda
is-nonpositive-ℤ : ℤ → UU lzero
is-nonpositive-ℤ (inl k) = unit
is-nonpositive-ℤ (inr (inl x)) = unit
is-nonpositive-ℤ (inr (inr x)) = empty

is-prop-is-nonpositive-ℤ : (x : ℤ) → is-prop (is-nonpositive-ℤ x)
is-prop-is-nonpositive-ℤ (inl x) = is-prop-unit
is-prop-is-nonpositive-ℤ (inr (inl x)) = is-prop-unit
is-prop-is-nonpositive-ℤ (inr (inr x)) = is-prop-empty

subtype-nonpositive-ℤ : subtype lzero ℤ
subtype-nonpositive-ℤ x = is-nonpositive-ℤ x , is-prop-is-nonpositive-ℤ x

nonpositive-ℤ : UU lzero
nonpositive-ℤ = type-subtype subtype-nonpositive-ℤ

is-nonpositive-eq-ℤ :
  {x y : ℤ} → x ＝ y → is-nonpositive-ℤ x → is-nonpositive-ℤ y
is-nonpositive-eq-ℤ {x} refl = id

module _
  (p : nonpositive-ℤ)
  where

  int-nonpositive-ℤ : ℤ
  int-nonpositive-ℤ = pr1 p

  is-nonpositive-int-nonpositive-ℤ : is-nonpositive-ℤ int-nonpositive-ℤ
  is-nonpositive-int-nonpositive-ℤ = pr2 p
```

### Nonpositive constants

```agda
zero-nonpositive-ℤ : nonpositive-ℤ
zero-nonpositive-ℤ = zero-ℤ , star

neg-one-nonpositive-ℤ : nonpositive-ℤ
neg-one-nonpositive-ℤ = neg-one-ℤ , star
```

## Properties

### Nonpositivity is decidable

```agda
is-decidable-is-nonpositive-ℤ : is-decidable-fam is-nonpositive-ℤ
is-decidable-is-nonpositive-ℤ (inl x) = inl star
is-decidable-is-nonpositive-ℤ (inr (inl x)) = inl star
is-decidable-is-nonpositive-ℤ (inr (inr x)) = inr id
```

### The nonpositive integers are a `Set`

```agda
is-set-nonpositive-ℤ : is-set nonpositive-ℤ
is-set-nonpositive-ℤ =
  is-set-emb
    ( emb-subtype subtype-nonpositive-ℤ)
    ( is-set-ℤ)
```

### The only nonpositive integer with a nonpositive negative is zero-ℤ

```agda
is-zero-is-nonpositive-neg-is-nonpositive-ℤ :
  {x : ℤ} → is-nonpositive-ℤ x → is-nonpositive-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-nonpositive-neg-is-nonpositive-ℤ {inr (inl star)} nonneg nonpos =
  refl
```

### The predecessor of a nonpositive integer is nonpositive

```agda
is-nonpositive-pred-is-nonpositive-ℤ :
  (x : ℤ) → is-nonpositive-ℤ x → is-nonpositive-ℤ (pred-ℤ x)
is-nonpositive-pred-is-nonpositive-ℤ (inl x) H = H
is-nonpositive-pred-is-nonpositive-ℤ (inr (inl x)) H = H

pred-nonpositive-ℤ : nonpositive-ℤ → nonpositive-ℤ
pred-nonpositive-ℤ (x , H) = pred-ℤ x , is-nonpositive-pred-is-nonpositive-ℤ x H
```

### The canonical equivalence between natural numbers and positive integers

```agda
nonpositive-int-ℕ : ℕ → nonpositive-ℤ
nonpositive-int-ℕ = rec-ℕ zero-nonpositive-ℤ (λ _ → pred-nonpositive-ℤ)

nat-nonpositive-ℤ : nonpositive-ℤ → ℕ
nat-nonpositive-ℤ (inl x , H) = succ-ℕ x
nat-nonpositive-ℤ (inr x , H) = zero-ℕ
```

TODO
