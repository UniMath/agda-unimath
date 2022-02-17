# Retracts of the type of natural numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.retracts-of-natural-numbers where

open import elementary-number-theory.equality-natural-numbers using
  ( has-decidable-equality-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.decidable-maps using
  ( is-decidable-map; is-decidable-map-retr)
open import foundation.retractions using (retr)
open import foundation.universe-levels using (Level; UU)
```

## Idea

If `i : A → ℕ` has a retraction, then `i` is a decidable map.

```agda
is-decidable-map-retr-ℕ :
  {l1 : Level} {A : UU l1} (i : A → ℕ) → retr i → is-decidable-map i
is-decidable-map-retr-ℕ =
  is-decidable-map-retr has-decidable-equality-ℕ
```
