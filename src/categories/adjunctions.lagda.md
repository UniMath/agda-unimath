---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module categories.adjunctions where

open import categories.large-categories public

module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  (F : functor-Large-Precat C D γF) (G : functor-Large-Precat D C γG)
  where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D

  record is-adjoint-pair-Large-Precat : Setω
    where
    field
      equiv-is-adjoint-pair-Large-Precat :
        {l1 l2 : Level} (X : obj-Large-Precat C l1)
        (Y : obj-Large-Precat D l2) →
        ( type-hom-Large-Precat X (obj-functor-Large-Precat G Y)) ≃
        ( type-hom-Large-Precat (obj-functor-Large-Precat F X) Y)
      naturality-equiv-is-adjoint-pair-Large-Precat :
        {l1 l2 l3 l4 : Level} {X1 : obj-Large-Precat C l1}
        {X2 : obj-Large-Precat C l2} {Y1 : obj-Large-Precat D l3}
        {Y2 : obj-Large-Precat D l4} (f : type-hom-Large-Precat X2 X1)
        (g : type-hom-Large-Precat Y1 Y2) →
        coherence-square
          ( map-equiv (equiv-is-adjoint-pair-Large-Precat X1 Y1))
          ( λ h →
            comp-hom-Large-Precat C
              ( comp-hom-Large-Precat C (hom-functor-Large-Precat G g) h)
              ( f))
          ( λ h →
            comp-hom-Large-Precat D
              ( comp-hom-Large-Precat D g h)
              ( hom-functor-Large-Precat F f))
          ( map-equiv (equiv-is-adjoint-pair-Large-Precat X2 Y2))

  open is-adjoint-pair-Large-Precat public

  map-equiv-is-adjoint-pair-Large-Precat :
    (H : is-adjoint-pair-Large-Precat) {l1 l2 : Level}
    (X : obj-Large-Precat C l1) (Y : obj-Large-Precat D l2) →
    ( type-hom-Large-Precat X (obj-functor-Large-Precat G Y)) →
    ( type-hom-Large-Precat (obj-functor-Large-Precat F X) Y)
  map-equiv-is-adjoint-pair-Large-Precat H X Y =
    map-equiv (equiv-is-adjoint-pair-Large-Precat H X Y)

  inv-equiv-is-adjoint-pair-Large-Precat :
    (H : is-adjoint-pair-Large-Precat) {l1 l2 : Level}
    (X : obj-Large-Precat C l1) (Y : obj-Large-Precat D l2) →
    ( type-hom-Large-Precat (obj-functor-Large-Precat F X) Y) ≃
    ( type-hom-Large-Precat X (obj-functor-Large-Precat G Y))
  inv-equiv-is-adjoint-pair-Large-Precat H X Y =
    inv-equiv (equiv-is-adjoint-pair-Large-Precat H X Y)

  map-inv-equiv-is-adjoint-pair-Large-Precat :
    (H : is-adjoint-pair-Large-Precat) {l1 l2 : Level}
    (X : obj-Large-Precat C l1) (Y : obj-Large-Precat D l2) →
    ( type-hom-Large-Precat (obj-functor-Large-Precat F X) Y) →
    ( type-hom-Large-Precat X (obj-functor-Large-Precat G Y))
  map-inv-equiv-is-adjoint-pair-Large-Precat H X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Large-Precat H X Y)

  naturality-inv-equiv-is-adjoint-pair-Large-Precat :
    (H : is-adjoint-pair-Large-Precat)
    {l1 l2 l3 l4 : Level} {X1 : obj-Large-Precat C l1}
    {X2 : obj-Large-Precat C l2} {Y1 : obj-Large-Precat D l3}
    {Y2 : obj-Large-Precat D l4} (f : type-hom-Large-Precat X2 X1)
    (g : type-hom-Large-Precat Y1 Y2) →
    coherence-square
      ( map-inv-equiv-is-adjoint-pair-Large-Precat H X1 Y1)
      ( λ h →
        comp-hom-Large-Precat D
          ( comp-hom-Large-Precat D g h)
          ( hom-functor-Large-Precat F f))
      ( λ h →
        comp-hom-Large-Precat C
          ( comp-hom-Large-Precat C (hom-functor-Large-Precat G g) h)
          ( f))
      ( map-inv-equiv-is-adjoint-pair-Large-Precat H X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Large-Precat
    H {X1 = X1} {X2} {Y1} {Y2} f g =
    coherence-square-inv-horizontal
      ( equiv-is-adjoint-pair-Large-Precat H X1 Y1)
      ( λ h →
        comp-hom-Large-Precat C
          ( comp-hom-Large-Precat C (hom-functor-Large-Precat G g) h)
          ( f))
      ( λ h →
        comp-hom-Large-Precat D
          ( comp-hom-Large-Precat D g h)
          ( hom-functor-Large-Precat F f))
      ( equiv-is-adjoint-pair-Large-Precat H X2 Y2)
      ( naturality-equiv-is-adjoint-pair-Large-Precat H f g)

module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  (G : functor-Large-Precat D C γG) (F : functor-Large-Precat C D γF)
  where

  is-left-adjoint-functor-Large-Precat : Setω
  is-left-adjoint-functor-Large-Precat =
    is-adjoint-pair-Large-Precat F G


module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  where

  private
    instance
      ⦃C⦄ = C
      ⦃D⦄ = D

  record Adjunction : Setω
    where
    field
      level-left-adjoint-Adjunction :
        Level → Level
      left-adjoint-Adjunction :
        functor-Large-Precat C D level-left-adjoint-Adjunction
      level-right-adjoint-Adjunction :
        Level → Level
      right-adjoint-Adjunction :
        functor-Large-Precat D C level-right-adjoint-Adjunction
      is-adjoint-pair-Adjunction :
        is-adjoint-pair-Large-Precat
          left-adjoint-Adjunction
          right-adjoint-Adjunction

  open Adjunction public

  obj-left-adjoint-Adjunction :
    (FG : Adjunction) {l : Level} →
    obj-Large-Precat C l →
    obj-Large-Precat D (level-left-adjoint-Adjunction FG l)
  obj-left-adjoint-Adjunction FG =
    obj-functor-Large-Precat (left-adjoint-Adjunction FG)

  hom-left-adjoint-Adjunction :
    (FG : Adjunction) {l1 l2 : Level}
    {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2} →
    type-hom-Large-Precat X Y →
    type-hom-Large-Precat
      ( obj-left-adjoint-Adjunction FG X)
      ( obj-left-adjoint-Adjunction FG Y)
  hom-left-adjoint-Adjunction FG =
    hom-functor-Large-Precat (left-adjoint-Adjunction FG)

  preserves-id-left-adjoint-Adjunction :
    (FG : Adjunction) {l1 : Level} (X : obj-Large-Precat C l1) →
    Id ( hom-left-adjoint-Adjunction FG (id-hom-Large-Precat C {X = X}))
       ( id-hom-Large-Precat D)
  preserves-id-left-adjoint-Adjunction FG X =
    preserves-id-functor-Large-Precat (left-adjoint-Adjunction FG)

  obj-right-adjoint-Adjunction :
    (FG : Adjunction) {l1 : Level} →
    obj-Large-Precat D l1 →
    obj-Large-Precat C (level-right-adjoint-Adjunction FG l1)
  obj-right-adjoint-Adjunction FG =
    obj-functor-Large-Precat (right-adjoint-Adjunction FG)

  hom-right-adjoint-Adjunction :
    (FG : Adjunction) {l1 l2 : Level} {X : obj-Large-Precat D l1}
    {Y : obj-Large-Precat D l2} →
    type-hom-Large-Precat X Y →
    type-hom-Large-Precat
      ( obj-right-adjoint-Adjunction FG X)
      ( obj-right-adjoint-Adjunction FG Y)
  hom-right-adjoint-Adjunction FG =
    hom-functor-Large-Precat (right-adjoint-Adjunction FG)

  preserves-id-right-adjoint-Adjunction :
    (FG : Adjunction) {l : Level} (Y : obj-Large-Precat D l) →
    Id ( hom-right-adjoint-Adjunction FG (id-hom-Large-Precat D {X = Y}))
       ( id-hom-Large-Precat C)
  preserves-id-right-adjoint-Adjunction FG Y =
    preserves-id-functor-Large-Precat (right-adjoint-Adjunction FG)

  equiv-is-adjoint-pair-Adjunction :
    (FG : Adjunction) {l1 l2 : Level} (X : obj-Large-Precat C l1)
    (Y : obj-Large-Precat D l2) →
    type-hom-Large-Precat X (obj-right-adjoint-Adjunction FG Y) ≃
    type-hom-Large-Precat (obj-left-adjoint-Adjunction FG X) Y
  equiv-is-adjoint-pair-Adjunction FG =
    equiv-is-adjoint-pair-Large-Precat (is-adjoint-pair-Adjunction FG)

  map-equiv-is-adjoint-pair-Adjunction :
    (FG : Adjunction) {l1 l2 : Level} (X : obj-Large-Precat C l1)
    (Y : obj-Large-Precat D l2) →
    type-hom-Large-Precat X (obj-right-adjoint-Adjunction FG Y) →
    type-hom-Large-Precat (obj-left-adjoint-Adjunction FG X) Y
  map-equiv-is-adjoint-pair-Adjunction FG =
    map-equiv-is-adjoint-pair-Large-Precat
      ( left-adjoint-Adjunction FG)
      ( right-adjoint-Adjunction FG)
      ( is-adjoint-pair-Adjunction FG)

  naturality-equiv-is-adjoint-pair-Adjunction :
    (FG : Adjunction) {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Precat C l1} {X2 : obj-Large-Precat C l2}
    {Y1 : obj-Large-Precat D l3} {Y2 : obj-Large-Precat D l4}
    (f : type-hom-Large-Precat X2 X1) (g : type-hom-Large-Precat Y1 Y2) →
    coherence-square
      ( map-equiv-is-adjoint-pair-Adjunction FG X1 Y1)
      ( λ h →
        comp-hom-Large-Precat C
          ( comp-hom-Large-Precat C (hom-right-adjoint-Adjunction FG g) h)
          ( f))
      ( λ h →
        comp-hom-Large-Precat D
          ( comp-hom-Large-Precat D g h)
          ( hom-left-adjoint-Adjunction FG f))
      ( map-equiv-is-adjoint-pair-Adjunction FG X2 Y2)
  naturality-equiv-is-adjoint-pair-Adjunction FG =
    naturality-equiv-is-adjoint-pair-Large-Precat
      ( is-adjoint-pair-Adjunction FG)

  inv-equiv-is-adjoint-pair-Adjunction :
    (FG : Adjunction) {l1 l2 : Level} (X : obj-Large-Precat C l1)
    (Y : obj-Large-Precat D l2) →
    type-hom-Large-Precat (obj-left-adjoint-Adjunction FG X) Y ≃
    type-hom-Large-Precat X (obj-right-adjoint-Adjunction FG Y)
  inv-equiv-is-adjoint-pair-Adjunction FG X Y =
    inv-equiv (equiv-is-adjoint-pair-Adjunction FG X Y)

  map-inv-equiv-is-adjoint-pair-Adjunction :
    (FG : Adjunction) {l1 l2 : Level} (X : obj-Large-Precat C l1)
    (Y : obj-Large-Precat D l2) →
    type-hom-Large-Precat (obj-left-adjoint-Adjunction FG X) Y →
    type-hom-Large-Precat X (obj-right-adjoint-Adjunction FG Y)
  map-inv-equiv-is-adjoint-pair-Adjunction FG X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Adjunction FG X Y)
    
  naturality-inv-equiv-is-adjoint-pair-Adjunction :
    (FG : Adjunction) {l1 l2 l3 l4 : Level}
    {X1 : obj-Large-Precat C l1} {X2 : obj-Large-Precat C l2}
    {Y1 : obj-Large-Precat D l3} {Y2 : obj-Large-Precat D l4}
    (f : type-hom-Large-Precat X2 X1) (g : type-hom-Large-Precat Y1 Y2) →
    coherence-square
      ( map-inv-equiv-is-adjoint-pair-Adjunction FG X1 Y1)
      ( λ h →
        comp-hom-Large-Precat D
          ( comp-hom-Large-Precat D g h)
          ( hom-left-adjoint-Adjunction FG f))
      ( λ h →
        comp-hom-Large-Precat C
          ( comp-hom-Large-Precat C (hom-right-adjoint-Adjunction FG g) h)
          ( f))
      ( map-inv-equiv-is-adjoint-pair-Adjunction FG X2 Y2)
  naturality-inv-equiv-is-adjoint-pair-Adjunction FG =
    naturality-inv-equiv-is-adjoint-pair-Large-Precat
      ( left-adjoint-Adjunction FG)
      ( right-adjoint-Adjunction FG)
      ( is-adjoint-pair-Adjunction FG)

  unit-Adjunction :
    (FG : Adjunction) →
    natural-transformation-Large-Precat
      ( id-functor-Large-Precat)
      ( comp-functor-Large-Precat
        ( right-adjoint-Adjunction FG)
        ( left-adjoint-Adjunction FG))
  obj-natural-transformation-Large-Precat (unit-Adjunction FG) X =
    map-inv-equiv-is-adjoint-pair-Adjunction FG X
      ( obj-left-adjoint-Adjunction FG X)
      ( id-hom-Large-Precat D)
  coherence-square-natural-transformation-Large-Precat
    ( unit-Adjunction FG) {X = X} {Y} f =
    ( inv
      ( left-unit-law-comp-hom-Large-Precat C
        ( comp-hom-Large-Precat C (η Y) f))) ∙
      ( ( ap
          ( comp-hom-Large-Precat' C (comp-hom-Large-Precat C (η Y) f))
          ( inv
            ( preserves-id-right-adjoint-Adjunction FG
              ( obj-left-adjoint-Adjunction FG Y)))) ∙
        ( ( inv
            ( associative-comp-hom-Large-Precat C
              ( hom-right-adjoint-Adjunction FG (id-hom-Large-Precat D))
              ( map-inv-equiv-is-adjoint-pair-Adjunction FG Y
                ( obj-left-adjoint-Adjunction FG Y)
                ( id-hom-Large-Precat D))
              ( f))) ∙
          ( ( inv
              ( naturality-inv-equiv-is-adjoint-pair-Adjunction FG f
                ( id-hom-Large-Precat D)
                ( id-hom-Large-Precat D))) ∙
            ( ( ap
                ( map-inv-equiv-is-adjoint-pair-Adjunction FG X
                  ( obj-left-adjoint-Adjunction FG Y))
                  ( ( associative-comp-hom-Large-Precat D
                      ( id-hom-Large-Precat D)
                      ( id-hom-Large-Precat D)
                      ( hom-left-adjoint-Adjunction FG f)) ∙
                    ( ( left-unit-law-comp-hom-Large-Precat D
                        ( comp-hom-Large-Precat D
                          ( id-hom-Large-Precat D)
                          ( hom-left-adjoint-Adjunction FG f))) ∙
                      ( ( left-unit-law-comp-hom-Large-Precat D
                          ( hom-left-adjoint-Adjunction FG f)) ∙
                        ( ( inv
                            ( right-unit-law-comp-hom-Large-Precat D
                              ( hom-left-adjoint-Adjunction FG f))) ∙
                          ( ( inv
                              ( right-unit-law-comp-hom-Large-Precat D
                                ( comp-hom-Large-Precat D
                                  ( hom-left-adjoint-Adjunction FG f)
                                  ( id-hom-Large-Precat D)))) ∙
                            ( ap
                              ( comp-hom-Large-Precat D
                                ( comp-hom-Large-Precat D
                                  ( hom-left-adjoint-Adjunction FG f)
                                  ( id-hom-Large-Precat D)))
                              ( inv
                                ( preserves-id-left-adjoint-Adjunction FG X)
                                )))))))) ∙
              ( ( naturality-inv-equiv-is-adjoint-pair-Adjunction FG
                  ( id-hom-Large-Precat C)
                  ( hom-left-adjoint-Adjunction FG f)
                  ( id-hom-Large-Precat D)) ∙
                ( right-unit-law-comp-hom-Large-Precat C
                  ( comp-hom-Large-Precat C
                    ( hom-right-adjoint-Adjunction FG
                      ( hom-left-adjoint-Adjunction FG f))
                    ( η X))))))))
    where
    η : {l : Level} (X : obj-Large-Precat C l) →
        type-hom-Large-Precat X
        ( obj-right-adjoint-Adjunction FG (obj-left-adjoint-Adjunction FG X))
    η = obj-natural-transformation-Large-Precat (unit-Adjunction FG)

  counit-Adjunction :
    (FG : Adjunction) →
    natural-transformation-Large-Precat
      ( comp-functor-Large-Precat
        ( left-adjoint-Adjunction FG)
        ( right-adjoint-Adjunction FG))
      ( id-functor-Large-Precat)
  obj-natural-transformation-Large-Precat (counit-Adjunction FG) Y =
    map-equiv-is-adjoint-pair-Adjunction FG
      ( obj-right-adjoint-Adjunction FG Y)
      ( Y)
      ( id-hom-Large-Precat C)
  coherence-square-natural-transformation-Large-Precat
    (counit-Adjunction FG) {X = X} {Y = Y} f =
    ( inv
      ( left-unit-law-comp-hom-Large-Precat D
      ( ( ε Y) ∘C
        ( hom-left-adjoint-Adjunction FG
          ( hom-right-adjoint-Adjunction FG f))))) ∙
    ( ( inv
        ( associative-comp-hom-Large-Precat D
          ( id-hom-Large-Precat D)
          ( map-equiv-is-adjoint-pair-Adjunction FG
            ( obj-right-adjoint-Adjunction FG Y)
            ( Y)
            ( id-hom-Large-Precat C))
          ( hom-left-adjoint-Adjunction FG
            ( hom-right-adjoint-Adjunction FG f)))) ∙
      ( ( inv
          ( naturality-equiv-is-adjoint-pair-Adjunction FG
            ( hom-right-adjoint-Adjunction FG f)
            ( id-hom-Large-Precat D)
            ( id-hom-Large-Precat C))) ∙
        ( ( ap
            ( map-equiv-is-adjoint-pair-Adjunction FG
              ( obj-right-adjoint-Adjunction FG X)
              ( Y))
            ( ( ap
                ( comp-hom-Large-Precat' C (hom-right-adjoint-Adjunction FG f))
                ( ( right-unit-law-comp-hom-Large-Precat C
                    ( hom-right-adjoint-Adjunction FG
                      ( id-hom-Large-Precat D))) ∙
                  ( preserves-id-right-adjoint-Adjunction FG Y))) ∙
              ( ( left-unit-law-comp-hom-Large-Precat C
                  ( hom-right-adjoint-Adjunction FG f)) ∙
                ( ( inv
                    ( right-unit-law-comp-hom-Large-Precat C
                      ( hom-right-adjoint-Adjunction FG f))) ∙
                  ( inv
                    ( right-unit-law-comp-hom-Large-Precat C
                      ( ( hom-right-adjoint-Adjunction FG f) ∘C
                        ( id-hom-Large-Precat C)))))))) ∙
          ( ( naturality-equiv-is-adjoint-pair-Adjunction FG
              ( id-hom-Large-Precat C)
              ( f)
              ( id-hom-Large-Precat C)) ∙
            ( ( ap
                ( comp-hom-Large-Precat D (f ∘C ε X))
                ( preserves-id-left-adjoint-Adjunction FG
                  ( obj-right-adjoint-Adjunction FG X))) ∙
              ( right-unit-law-comp-hom-Large-Precat D (f ∘C ε X)))))))
    where
    ε : {l : Level} (Y : obj-Large-Precat D l) →
        type-hom-Large-Precat
        ( obj-left-adjoint-Adjunction FG (obj-right-adjoint-Adjunction FG Y))
        ( Y)
    ε = obj-natural-transformation-Large-Precat (counit-Adjunction FG)
