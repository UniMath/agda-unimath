# Retracts of the standard finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.retracts-of-standard-finite-types where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.decidable-maps using
  ( is-decidable-map; is-decidable-map-retr)
open import foundation.retractions using (retr)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

If a map `i : A → Fin k` has a retraction, then it is a decidable map

```agda
is-decidable-map-retr-Fin :
  {l1 : Level} {k : ℕ} {A : UU l1} (i : A → Fin k) → retr i → is-decidable-map i
is-decidable-map-retr-Fin =
  is-decidable-map-retr has-decidable-equality-Fin
```
