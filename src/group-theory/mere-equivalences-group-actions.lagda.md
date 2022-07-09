---
title: Mere equivalences of group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.mere-equivalences-group-actions where

open import foundation.propositional-truncations using (trunc-Prop)
open import foundation.propositions using (UU-Prop; type-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.equivalences-group-actions using
  ( equiv-Abstract-Group-Action)
open import group-theory.group-actions using (Abstract-Group-Action)
open import group-theory.groups using (Group)
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  mere-equiv-Abstract-Group-Action-Prop : UU-Prop (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action-Prop =
    trunc-Prop (equiv-Abstract-Group-Action G X Y)

  mere-equiv-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action =
    type-Prop mere-equiv-Abstract-Group-Action-Prop
```
