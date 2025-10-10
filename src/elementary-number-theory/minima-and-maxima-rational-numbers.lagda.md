# Minima and maxima on the rational numbers

```agda
module elementary-number-theory.minima-and-maxima-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.identity-types
```

</details>

## Idea

On this page, we outline basic relations between
[minima](elementary-number-theory.minimum-rational-numbers.md) and
[maxima](elementary-number-theory.maximum-rational-numbers.md) of
[rational numbers](elementary-number-theory.rational-numbers.md).

## Lemmas

### The negation of the minimum of rational numbers is the maximum of the negations

```agda
module _
  (p q : ℚ)
  where

  abstract
    neg-min-ℚ : neg-ℚ (min-ℚ p q) ＝ max-ℚ (neg-ℚ p) (neg-ℚ q)
    neg-min-ℚ =
      rec-coproduct
        ( λ p≤q →
          ( ap neg-ℚ (left-leq-right-min-ℚ p q p≤q)) ∙
          ( inv (right-leq-left-max-ℚ _ _ (neg-leq-ℚ p≤q))))
        ( λ q≤p →
          ( ap neg-ℚ (right-leq-left-min-ℚ p q q≤p)) ∙
          ( inv (left-leq-right-max-ℚ _ _ (neg-leq-ℚ q≤p))))
        ( linear-leq-ℚ p q)
```

### The negation of the maximum of rational numbers is the minimum of the negations

```agda
module _
  (p q : ℚ)
  where

  abstract
    neg-max-ℚ : neg-ℚ (max-ℚ p q) ＝ min-ℚ (neg-ℚ p) (neg-ℚ q)
    neg-max-ℚ =
      rec-coproduct
        ( λ p≤q →
          ( ap neg-ℚ (left-leq-right-max-ℚ _ _ p≤q)) ∙
          ( inv (right-leq-left-min-ℚ _ _ (neg-leq-ℚ p≤q))))
        ( λ q≤p →
          ( ap neg-ℚ (right-leq-left-max-ℚ _ _ q≤p)) ∙
          ( inv (left-leq-right-min-ℚ _ _ (neg-leq-ℚ q≤p))))
        ( linear-leq-ℚ p q)
```
