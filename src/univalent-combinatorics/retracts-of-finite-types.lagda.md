# Retracts of finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.retracts-of-finite-types where

open import foundation.decidable-maps using
  ( is-decidable-map; is-decidable-map-retr)
open import foundation.retractions using (retr)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; has-decidable-equality-count)
open import univalent-combinatorics.equality-finite-types using
  ( has-decidable-equality-is-finite)
open import univalent-combinatorics.finite-types using
  ( is-finite)
```

## Idea

If a map `i : A → B` into a finite type `B` has a retraction, then `i` is decidable.

```agda
is-decidable-map-retr-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) → retr i →
  is-decidable-map i
is-decidable-map-retr-count e =
  is-decidable-map-retr (has-decidable-equality-count e)

is-decidable-map-retr-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite B) (i : A → B) →
  retr i → is-decidable-map i
is-decidable-map-retr-is-finite H =
  is-decidable-map-retr (has-decidable-equality-is-finite H)
```
