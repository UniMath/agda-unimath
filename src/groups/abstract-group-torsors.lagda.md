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

  is-prop-is-torsor-Abstract-Group : is-prop is-torsor-Abstract-Group
  is-prop-is-torsor-Abstract-Group =
    is-prop-type-Prop is-torsor-Abstract-Group-Prop

module _
  {l1 : Level} (G : Group l1)
  where
  
  Torsor-Abstract-Group : (l : Level) → UU (l1 ⊔ lsuc l)
  Torsor-Abstract-Group l =
    Σ ( Abstract-Group-Action G l)
      ( is-torsor-Abstract-Group G)

  action-Torsor-Abstract-Group :
    {l : Level} → Torsor-Abstract-Group l → Abstract-Group-Action G l
  action-Torsor-Abstract-Group = pr1

  is-torsor-action-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    is-torsor-Abstract-Group G (action-Torsor-Abstract-Group X)
  is-torsor-action-Torsor-Abstract-Group = pr2

  principal-Torsor-Abstract-Group : Torsor-Abstract-Group l1
  pr1 principal-Torsor-Abstract-Group = principal-Abstract-Group-Action G
  pr2 principal-Torsor-Abstract-Group =
    unit-trunc-Prop
      ( equiv-id-Abstract-Group-Action G (principal-Abstract-Group-Action G))

module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  where

  equiv-Torsor-Abstract-Group :
    {l3 : Level} (Y : Torsor-Abstract-Group G l3) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-Torsor-Abstract-Group Y =
    equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)

  equiv-id-Torsor-Abstract-Group : equiv-Torsor-Abstract-Group X
  equiv-id-Torsor-Abstract-Group =
    equiv-id-Abstract-Group-Action G (action-Torsor-Abstract-Group G X)

  equiv-eq-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → Id X Y → equiv-Torsor-Abstract-Group Y
  equiv-eq-Torsor-Abstract-Group .X refl =
    equiv-id-Torsor-Abstract-Group

  is-contr-total-equiv-Torsor-Abstract-Group :
    is-contr (Σ (Torsor-Abstract-Group G l2) (equiv-Torsor-Abstract-Group))
  is-contr-total-equiv-Torsor-Abstract-Group =
    is-contr-total-Eq-substructure
      ( is-contr-total-equiv-Abstract-Group-Action G
        ( action-Torsor-Abstract-Group G X))
      ( is-prop-is-torsor-Abstract-Group G)
      ( action-Torsor-Abstract-Group G X)
      ( equiv-id-Torsor-Abstract-Group)
      ( is-torsor-action-Torsor-Abstract-Group G X)

  is-equiv-equiv-eq-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) →
    is-equiv (equiv-eq-Torsor-Abstract-Group Y)
  is-equiv-equiv-eq-Torsor-Abstract-Group =
    fundamental-theorem-id X
      equiv-id-Torsor-Abstract-Group
      is-contr-total-equiv-Torsor-Abstract-Group
      equiv-eq-Torsor-Abstract-Group

  eq-equiv-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → equiv-Torsor-Abstract-Group Y → Id X Y
  eq-equiv-Torsor-Abstract-Group Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Torsor-Abstract-Group Y)

  extensionality-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → Id X Y ≃ equiv-Torsor-Abstract-Group Y
  pr1 (extensionality-Torsor-Abstract-Group Y) =
    equiv-eq-Torsor-Abstract-Group Y
  pr2 (extensionality-Torsor-Abstract-Group Y) =
    is-equiv-equiv-eq-Torsor-Abstract-Group Y

module _
  {l1 : Level} (G : Group l1)
  where


```
