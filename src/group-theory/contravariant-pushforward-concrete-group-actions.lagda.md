---
title: Contravariant pushforwards of concrete group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.contravariant-pushforward-concrete-group-actions where

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-group-actions
open import group-theory.substitution-functor-concrete-group-actions
```

## Idea

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

{-
  contravariant-pushforward-action-Concrete-Group :
    {l : Level} → action-Concrete-Group l G → action-Concrete-Group {!!} H
  contravariant-pushforward-action-Concrete-Group X y = {!!}
  
    -- The following should be constructed as a set
    hom-action-Concrete-Group G X
      ( subst-action-Concrete-Group G H f (λ y → Id (shape-Concrete-Group H) y))
      -}
```
