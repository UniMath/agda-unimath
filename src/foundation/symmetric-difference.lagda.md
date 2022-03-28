# Symmetric difference of subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.symmetric-difference where

open import foundation.decidable-subtypes using (decidable-subtype)
open import foundation.subtypes using (subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.xor using (xor-Prop; xor-decidable-Prop)
```

## Idea

The symmetric difference of two subtypes `A` and `B` is the subtypes that contains the elements that are either in `A` or in `B` but not in both.

## Definition

```agda
module _
  {l l1 l2 : Level} (X : UU l)
  where

  symmetric-difference-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  symmetric-difference-subtype P Q x = xor-Prop (P x) (Q x)

  symmetric-difference-decidable-subtype : decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  symmetric-difference-decidable-subtype P Q x = xor-decidable-Prop (P x) (Q x)
```
