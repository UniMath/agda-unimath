---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.abstract-group-torsors where

open import groups.abstract-group-actions public

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  is-torsor-Abstract-Group-Prop : UU-Prop (l1 ⊔ l2)
  is-torsor-Abstract-Group-Prop =
    mere-equiv-Abstract-Group-Action-Prop G
      ( principal-Abstract-Group-Action G)
      ( X)

  is-torsor-Abstract-Group : UU (l1 ⊔ l2)
  is-torsor-Abstract-Group = type-Prop is-torsor-Abstract-Group-Prop

module _
  {l1 : Level} (G : Group l1)
  where
  
  Torsor-Abstract-Group : (l : Level) → UU (l1 ⊔ lsuc l)
  Torsor-Abstract-Group l =
    Σ ( Abstract-Group-Action G l)
      ( is-torsor-Abstract-Group G)


```
