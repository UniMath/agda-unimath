---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.abstract-group-torsors where

open import groups.abstract-group-actions public
open import groups.concrete-groups public

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

  set-Torsor-Abstract-Group :
    {l : Level} → Torsor-Abstract-Group l → UU-Set l
  set-Torsor-Abstract-Group X =
    set-Abstract-Group-Action G (action-Torsor-Abstract-Group X)

  type-Torsor-Abstract-Group :
    {l : Level} → Torsor-Abstract-Group l → UU l
  type-Torsor-Abstract-Group X =
    type-Set (set-Torsor-Abstract-Group X)

  is-set-type-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    is-set (type-Torsor-Abstract-Group X)
  is-set-type-Torsor-Abstract-Group X =
    is-set-type-Set (set-Torsor-Abstract-Group X)

  mul-hom-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    hom-Group G (symmetric-Group (set-Torsor-Abstract-Group X))
  mul-hom-Torsor-Abstract-Group X = pr2 (action-Torsor-Abstract-Group X)

  equiv-mul-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    type-Group G → (type-Torsor-Abstract-Group X ≃ type-Torsor-Abstract-Group X)
  equiv-mul-Torsor-Abstract-Group X =
    equiv-mul-Abstract-Group-Action G (action-Torsor-Abstract-Group X)

  mul-Torsor-Abstract-Group :
    {l : Level} (X : Torsor-Abstract-Group l) →
    type-Group G → type-Torsor-Abstract-Group X → type-Torsor-Abstract-Group X
  mul-Torsor-Abstract-Group X =
    mul-Abstract-Group-Action G (action-Torsor-Abstract-Group X)

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
  {l1 l2 l3 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  (Y : Torsor-Abstract-Group G l3) (e : equiv-Torsor-Abstract-Group G X Y)
  where

  htpy-equiv-Torsor-Abstract-Group :
    equiv-Torsor-Abstract-Group G X Y → UU (l2 ⊔ l3)
  htpy-equiv-Torsor-Abstract-Group =
    htpy-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( e)

  refl-htpy-equiv-Torsor-Abstract-Group : htpy-equiv-Torsor-Abstract-Group e
  refl-htpy-equiv-Torsor-Abstract-Group =
    refl-htpy-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( e)

  htpy-eq-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    Id e f → htpy-equiv-Torsor-Abstract-Group f
  htpy-eq-equiv-Torsor-Abstract-Group .e refl =
    refl-htpy-equiv-Torsor-Abstract-Group

  is-contr-total-htpy-equiv-Torsor-Abstract-Group :
    is-contr ( Σ ( equiv-Torsor-Abstract-Group G X Y)
                 ( htpy-equiv-Torsor-Abstract-Group))
  is-contr-total-htpy-equiv-Torsor-Abstract-Group =
    is-contr-total-htpy-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( e)

  is-equiv-htpy-eq-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    is-equiv (htpy-eq-equiv-Torsor-Abstract-Group f)
  is-equiv-htpy-eq-equiv-Torsor-Abstract-Group =
    fundamental-theorem-id e
      refl-htpy-equiv-Torsor-Abstract-Group
      is-contr-total-htpy-equiv-Torsor-Abstract-Group
      htpy-eq-equiv-Torsor-Abstract-Group

  eq-htpy-equiv-Torsor-Abstract-Group :
    (f : equiv-Torsor-Abstract-Group G X Y) →
    htpy-equiv-Torsor-Abstract-Group f → Id e f
  eq-htpy-equiv-Torsor-Abstract-Group f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Torsor-Abstract-Group f)
  
module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : Torsor-Abstract-Group G l2) (Y : Torsor-Abstract-Group G l3)
  (Z : Torsor-Abstract-Group G l4)
  where
  
  comp-equiv-Torsor-Abstract-Group :
    equiv-Torsor-Abstract-Group G Y Z → equiv-Torsor-Abstract-Group G X Y →
    equiv-Torsor-Abstract-Group G X Z
  comp-equiv-Torsor-Abstract-Group =
    comp-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)
      ( action-Torsor-Abstract-Group G Z)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Abstract-Group G l2) (Y : Torsor-Abstract-Group G l3)
  where

  inv-equiv-Torsor-Abstract-Group :
    equiv-Torsor-Abstract-Group G X Y → equiv-Torsor-Abstract-Group G Y X
  inv-equiv-Torsor-Abstract-Group =
    inv-equiv-Abstract-Group-Action G
      ( action-Torsor-Abstract-Group G X)
      ( action-Torsor-Abstract-Group G Y)

module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Abstract-Group G l2)
  where

  mere-eq-Torsor-Abstract-Group :
    (Y : Torsor-Abstract-Group G l2) → mere-eq X Y
  mere-eq-Torsor-Abstract-Group Y =
    apply-universal-property-trunc-Prop
      ( pr2 X)
      ( mere-eq-Prop X Y)
      ( λ e →
        apply-universal-property-trunc-Prop
          ( pr2 Y)
          ( mere-eq-Prop X Y)
          ( λ f →
            unit-trunc-Prop
              ( eq-equiv-Torsor-Abstract-Group G X Y
                ( comp-equiv-Torsor-Abstract-Group G
                  ( X)
                  ( principal-Torsor-Abstract-Group G)
                  ( Y)
                  ( f)
                  ( inv-equiv-Torsor-Abstract-Group G
                    ( principal-Torsor-Abstract-Group G)
                    ( X)
                    ( e))))))

module _
  {l1 : Level} (G : Group l1)
  where

  is-path-connected-Torsor-Abstract-Group :
    is-path-connected (Torsor-Abstract-Group G l1)
  is-path-connected-Torsor-Abstract-Group =
    is-path-connected-mere-eq
      ( principal-Torsor-Abstract-Group G)
      ( mere-eq-Torsor-Abstract-Group G (principal-Torsor-Abstract-Group G))

module _
  {l1 : Level} (G : Group l1)
  where

  Eq-Torsor-Abstract-Group :
    (X : Torsor-Abstract-Group G l1) → UU l1
  Eq-Torsor-Abstract-Group X = type-Torsor-Abstract-Group G X

  refl-Eq-Torsor-Abstract-Group :
    Eq-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G)
  refl-Eq-Torsor-Abstract-Group = unit-Group G

  Eq-equiv-Torsor-Abstract-Group :
    (X : Torsor-Abstract-Group G l1) →
    equiv-Torsor-Abstract-Group G (principal-Torsor-Abstract-Group G) X →
    Eq-Torsor-Abstract-Group X
  Eq-equiv-Torsor-Abstract-Group X (pair e H) = map-equiv e (unit-Group G)

  equiv-Eq-Torsor-Abstract-Group :
    Eq-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G) →
    equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
  pr1 (equiv-Eq-Torsor-Abstract-Group u) = equiv-mul-Group' G u
  pr2 (equiv-Eq-Torsor-Abstract-Group u) g x = is-associative-mul-Group G g x u

  issec-equiv-Eq-Torsor-Abstract-Group :
    ( Eq-equiv-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G) ∘
      equiv-Eq-Torsor-Abstract-Group) ~
    ( id)
  issec-equiv-Eq-Torsor-Abstract-Group u = left-unit-law-Group G u

  isretr-equiv-Eq-Torsor-Abstract-Group :
    ( equiv-Eq-Torsor-Abstract-Group ∘
      Eq-equiv-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G)) ~
    ( id)
  isretr-equiv-Eq-Torsor-Abstract-Group e =
    eq-htpy-equiv-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( principal-Torsor-Abstract-Group G)
      ( equiv-Eq-Torsor-Abstract-Group
        ( Eq-equiv-Torsor-Abstract-Group (principal-Torsor-Abstract-Group G) e))
      ( e)
      ( λ g →
        ( inv (pr2 e g (unit-Group G))) ∙
        ( ap (map-equiv (pr1 e)) (right-unit-law-Group G g)))
  
  abstract
    is-equiv-Eq-equiv-Torsor-Abstract-Group :
      (X : Torsor-Abstract-Group G l1) →
      is-equiv (Eq-equiv-Torsor-Abstract-Group X)
    is-equiv-Eq-equiv-Torsor-Abstract-Group X =
      apply-universal-property-trunc-Prop
        ( is-torsor-action-Torsor-Abstract-Group G X)
        ( is-equiv-Prop (Eq-equiv-Torsor-Abstract-Group X))
        ( λ e →
          tr ( λ Y → is-equiv (Eq-equiv-Torsor-Abstract-Group Y))
             ( eq-equiv-Torsor-Abstract-Group G
               ( principal-Torsor-Abstract-Group G)
               ( X)
               ( e))
             ( is-equiv-has-inverse
                 equiv-Eq-Torsor-Abstract-Group
                 issec-equiv-Eq-Torsor-Abstract-Group
                 isretr-equiv-Eq-Torsor-Abstract-Group))

  equiv-Eq-equiv-Torsor-Abstract-Group :
    (X : Torsor-Abstract-Group G l1) →
    Id (principal-Torsor-Abstract-Group G) X ≃ Eq-Torsor-Abstract-Group X
  equiv-Eq-equiv-Torsor-Abstract-Group X =
    ( pair
      ( Eq-equiv-Torsor-Abstract-Group X)
      ( is-equiv-Eq-equiv-Torsor-Abstract-Group X)) ∘e
    ( extensionality-Torsor-Abstract-Group G
      ( principal-Torsor-Abstract-Group G)
      ( X))

  ∞-group-Group : ∞-Group (lsuc l1)
  pr1 (pr1 ∞-group-Group) = Torsor-Abstract-Group G l1
  pr2 (pr1 ∞-group-Group) = principal-Torsor-Abstract-Group G
  pr2 ∞-group-Group = is-path-connected-Torsor-Abstract-Group G

  concrete-group-Group : Concrete-Group (lsuc l1)
  pr1 concrete-group-Group = ∞-group-Group
  pr2 concrete-group-Group =
    is-set-equiv
      ( type-Group G)
      ( equiv-Eq-equiv-Torsor-Abstract-Group
        ( principal-Torsor-Abstract-Group G))
      ( is-set-type-Group G)
```
