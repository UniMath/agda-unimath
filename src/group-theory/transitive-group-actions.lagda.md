---
title: Transitive group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.transitive-group-actions where

open import foundation.existential-quantification using (∃-Prop)
open import foundation.identity-types using (Id)
open import foundation.propositions using (UU-Prop; Π-Prop)
open import foundation.universe-levels using (Level; _⊔_)

open import group-theory.group-actions using
  ( Abstract-Group-Action; type-Abstract-Group-Action;
    mul-Abstract-Group-Action)
open import group-theory.groups using (Group; type-Group)
```

## Idea

A group `G` is said to act transitively on a set `X` if for every `x` and `y` in `X` there is a group element `g` such that `gx = y`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  is-transitive-Abstract-Group-Action : UU-Prop (l1 ⊔ l2)
  is-transitive-Abstract-Group-Action =
    Π-Prop
      ( type-Abstract-Group-Action G X)
      ( λ x →
        Π-Prop
          ( type-Abstract-Group-Action G X)
          ( λ y → ∃-Prop (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) y)))
```
