# Minimum on the rational numbers

```agda
module elementary-number-theory.minimum-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.function-types
```

</details>

## Idea

We define the operation of minimum (greatest lower bound) for the rational
numbers.

## Definition

```agda
min-ℚ : ℚ → ℚ → ℚ
min-ℚ p q =
  rec-coproduct
    (λ _ → p)
    (λ _ → q)
    (linear-leq-ℚ p q)
```

## Properties

### The minimum of two rational numbers is less than or equal to both of them

```agda
module _
  (p q : ℚ)
  where

  leq-left-min-ℚ : leq-ℚ (min-ℚ p q) p
  leq-left-min-ℚ with linear-leq-ℚ p q
  ... | inl p≤q = refl-leq-ℚ p
  ... | inr q≤p = q≤p

  leq-right-min-ℚ : leq-ℚ (min-ℚ p q) q
  leq-right-min-ℚ with linear-leq-ℚ p q
  ... | inl p≤q = p≤q
  ... | inr q≤p = refl-leq-ℚ q
```

### A value less than two rational numbers is less than their minimum

```agda
module _
  (p q r : ℚ)
  where

  le-both-le-min-ℚ : le-ℚ r p → le-ℚ r q → le-ℚ r (min-ℚ p q)
  le-both-le-min-ℚ r<p r<q with linear-leq-ℚ p q
  ... | inl p≤q = r<p
  ... | inr q≤p = r<q
```
