# The zero conatural number

```agda
{-# OPTIONS --guardedness #-}

open import foundation.function-extensionality-axiom

module
  elementary-number-theory.zero-conatural-numbers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers funext

open import foundation.coproduct-types funext
open import foundation.decidable-types funext
open import foundation.function-types funext
open import foundation.negation funext
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.maybe
open import foundation-core.propositions
```

</details>

## Idea

A [conatural number](elementary-number-theory.conatural-numbers.md) `x` is
{{#concept "zero" Disambiguation="conatural number" Agda=is-zero-ℕ∞}} if it does
not have a predecessor.

## Definitions

### The predicate on conatural numbers of being zero

```agda
is-zero-ℕ∞ : ℕ∞ → UU lzero
is-zero-ℕ∞ x = is-exception-Maybe (decons-ℕ∞ x)
```

## Properties

### Zero is zero

```agda
is-zero-zero-ℕ∞ : is-zero-ℕ∞ zero-ℕ∞
is-zero-zero-ℕ∞ = refl
```

### Successors are not zero

```agda
is-not-zero-succ-ℕ∞ : (x : ℕ∞) → ¬ (is-zero-ℕ∞ (succ-ℕ∞ x))
is-not-zero-succ-ℕ∞ x ()
```

### The point at infinity is not zero

```agda
is-not-zero-infinity-ℕ∞ : ¬ (is-zero-ℕ∞ infinity-ℕ∞)
is-not-zero-infinity-ℕ∞ = is-not-zero-succ-ℕ∞ infinity-ℕ∞
```

### Being zero is decidable

```agda
is-decidable-is-zero-ℕ∞ : (x : ℕ∞) → is-decidable (is-zero-ℕ∞ x)
is-decidable-is-zero-ℕ∞ x with decons-ℕ∞ x
is-decidable-is-zero-ℕ∞ x | inl y = inr (is-not-zero-succ-ℕ∞ y)
is-decidable-is-zero-ℕ∞ x | inr * = inl is-zero-zero-ℕ∞
```

### Being zero is a property

```agda
is-prop-is-zero-ℕ∞ : (x : ℕ∞) → is-prop (is-zero-ℕ∞ x)
is-prop-is-zero-ℕ∞ = is-prop-is-exception-Maybe ∘ decons-ℕ∞
```

## See also

- [Positive conatural numbers](elementary-number-theory.positive-conatural-numbers.md)
- [Infinite conatural numbers](elementary-number-theory.infinite-conatural-numbers.md)
