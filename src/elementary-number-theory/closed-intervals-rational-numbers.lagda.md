# Closed intervals of rational numbers

```agda
module elementary-number-theory.closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.propositions
open import foundation.conjunction
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import foundation.universe-levels
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
```

</details>

## Idea

## Definition

```agda
module _
  (a b : ℚ)
  where

  closed-interval-ℚ : subtype lzero ℚ
  closed-interval-ℚ q = leq-ℚ-Prop a q ∧ leq-ℚ-Prop q b

  is-in-closed-interval-ℚ : ℚ → UU lzero
  is-in-closed-interval-ℚ q = type-Prop (closed-interval-ℚ q)

module _
  (a b : ℚ)
  where

  unordered-closed-interval-ℚ : subtype lzero ℚ
  unordered-closed-interval-ℚ = closed-interval-ℚ (min-ℚ a b) (max-ℚ a b)

  is-in-unordered-closed-interval-ℚ : ℚ → UU lzero
  is-in-unordered-closed-interval-ℚ q =
    type-Prop (unordered-closed-interval-ℚ q)
```

## Properties

```agda
right-mul-closed-interval-ℚ :
  (a b p q : ℚ) → is-in-closed-interval-ℚ a b p →
  is-in-unordered-closed-interval-ℚ (a *ℚ q) (b *ℚ q) (p *ℚ q)
right-mul-closed-interval-ℚ a b p q (a≤p , p≤b) =
  trichotomy-le-ℚ
    q
    zero-ℚ
    {!   !}
    ( λ q=0 → {!   !})
    {!   !}
```
