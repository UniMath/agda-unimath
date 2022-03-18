# Counting the elements in Maybe

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-maybe where

open import elementary-number-theory.natural-numbers using
  ( is-nonzero-ℕ; is-successor-ℕ; is-successor-is-nonzero-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences-maybe using (equiv-equiv-Maybe)
open import foundation.identity-types using (refl)
open import foundation.maybe using (Maybe; exception-Maybe)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; count-unit; number-of-elements-count;
    is-empty-is-zero-number-of-elements-count)
open import univalent-combinatorics.coproduct-types using
  ( count-coprod)
```

## Idea

The elements of a type `X` can be counted if and only if the elements of `Maybe X` can be counted.

```agda
count-Maybe : {l : Level} {X : UU l} → count X → count (Maybe X)
count-Maybe {l} {X} e = count-coprod e count-unit

abstract
  is-nonzero-number-of-elements-count-Maybe :
    {l : Level} {X : UU l} (e : count (Maybe X)) →
    is-nonzero-ℕ (number-of-elements-count e)
  is-nonzero-number-of-elements-count-Maybe e p =
    is-empty-is-zero-number-of-elements-count e p exception-Maybe

is-successor-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-successor-ℕ (number-of-elements-count e)
is-successor-number-of-elements-count-Maybe e =
  is-successor-is-nonzero-ℕ (is-nonzero-number-of-elements-count-Maybe e)

count-count-Maybe :
  {l : Level} {X : UU l} → count (Maybe X) → count X
count-count-Maybe (pair k e) with
  is-successor-number-of-elements-count-Maybe (pair k e)
... | pair l refl = pair l (equiv-equiv-Maybe e)
```
