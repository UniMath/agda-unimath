# Positive conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module elementary-number-theory.positive-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers
open import elementary-number-theory.zero-conatural-numbers

open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.maybe
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.identity-types
```

</details>

## Idea

A [conatural number](elementary-number-theory.conatural-numbers.md) `x` is
{{#concept "positive" Disambiguation="conatural number" Agda=is-infinite-ℕ∞}} if
it has a predecessor. In other words, if it is not
[zero](elementary-number-theory.zero-conatural-numbers.md).

## Definitions

### The predicate on conatural numbers of being positive

```agda
is-positive-ℕ∞ : ℕ∞ → UU lzero
is-positive-ℕ∞ x = is-value-Maybe (decons-ℕ∞ x)
```

## Properties

### Zero is not positive

```agda
is-not-positive-zero-ℕ∞ : ¬ (is-positive-ℕ∞ zero-ℕ∞)
is-not-positive-zero-ℕ∞ ()
```

### Successors are positive

```agda
is-positive-succ-ℕ∞ : (x : ℕ∞) → is-positive-ℕ∞ (succ-ℕ∞ x)
is-positive-succ-ℕ∞ x = x , refl
```

### The point at infinity is positive

```agda
is-positive-infinity-ℕ∞ : is-positive-ℕ∞ infinity-ℕ∞
is-positive-infinity-ℕ∞ = is-positive-succ-ℕ∞ infinity-ℕ∞
```

### Positivity is decidable

```agda
is-decidable-is-positive-ℕ∞ : (x : ℕ∞) → is-decidable (is-positive-ℕ∞ x)
is-decidable-is-positive-ℕ∞ x with (decons-ℕ∞ x)
is-decidable-is-positive-ℕ∞ x | (inl y) = inl (is-positive-succ-ℕ∞ y)
is-decidable-is-positive-ℕ∞ x | (inr _) = inr is-not-positive-zero-ℕ∞
```

### A conatural number is positive if and only if it is nonzero

```agda
is-positive-is-not-zero-ℕ∞ : (x : ℕ∞) → ¬ (is-zero-ℕ∞ x) → is-positive-ℕ∞ x
is-positive-is-not-zero-ℕ∞ x H with (decons-ℕ∞ x)
is-positive-is-not-zero-ℕ∞ x H | (inl y) = y , refl
is-positive-is-not-zero-ℕ∞ x H | (inr *) = ex-falso (H refl)

is-not-zero-is-positive-ℕ∞ : (x : ℕ∞) → is-positive-ℕ∞ x → ¬ (is-zero-ℕ∞ x)
is-not-zero-is-positive-ℕ∞ x = is-not-exception-is-value-Maybe (decons-ℕ∞ x)
```

## See also

- [Infinite conatural numbers](elementary-number-theory.infinite-conatural-numbers.md)
