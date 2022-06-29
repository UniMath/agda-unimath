---
title: Intersection of subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.intersection where

open import foundation.conjunction using (conj-Prop; conj-decidable-Prop)
open import foundation.decidable-subtypes using (decidable-subtype)
open import foundation.subtypes using (subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The intersection of two subtypes `A` and `B` is the subtype that contains the elements that are in `A` and in `B`.

## Definition

```agda
module _
  {l l1 l2 : Level} (X : UU l)
  where

  intersection-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  intersection-subtype P Q x = conj-Prop (P x) (Q x)

  intersection-decidable-subtype : decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  intersection-decidable-subtype P Q x = conj-decidable-Prop (P x) (Q x)
```
