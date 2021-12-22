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

  record is-adjoint-pair-Large-Precat : Setω
    where
    field
      equiv-is-adjoint-pair-Large-Precat :
        {l1 l2 : Level} (X : obj-Large-Precat C l1)
        (Y : obj-Large-Precat D l2) →
        ( type-hom-Large-Precat C X (obj-functor-Large-Precat G Y)) ≃
        ( type-hom-Large-Precat D (obj-functor-Large-Precat F X) Y)
      naturality-equiv-is-adjoint-pair-Large-Precat :
        {l1 l2 l3 l4 : Level} {X1 : obj-Large-Precat C l1}
        {X2 : obj-Large-Precat C l2} {Y1 : obj-Large-Precat D l3}
        {Y2 : obj-Large-Precat D l4} (f : type-hom-Large-Precat C X2 X1)
        (g : type-hom-Large-Precat D Y1 Y2) →
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
    ( type-hom-Large-Precat C X (obj-functor-Large-Precat G Y)) →
    ( type-hom-Large-Precat D (obj-functor-Large-Precat F X) Y)
  map-equiv-is-adjoint-pair-Large-Precat H X Y =
    map-equiv (equiv-is-adjoint-pair-Large-Precat H X Y)

  inv-equiv-is-adjoint-pair-Large-Precat :
    (H : is-adjoint-pair-Large-Precat) {l1 l2 : Level}
    (X : obj-Large-Precat C l1) (Y : obj-Large-Precat D l2) →
    ( type-hom-Large-Precat D (obj-functor-Large-Precat F X) Y) ≃
    ( type-hom-Large-Precat C X (obj-functor-Large-Precat G Y))
  inv-equiv-is-adjoint-pair-Large-Precat H X Y =
    inv-equiv (equiv-is-adjoint-pair-Large-Precat H X Y)

  map-inv-equiv-is-adjoint-pair-Large-Precat :
    (H : is-adjoint-pair-Large-Precat) {l1 l2 : Level}
    (X : obj-Large-Precat C l1) (Y : obj-Large-Precat D l2) →
    ( type-hom-Large-Precat D (obj-functor-Large-Precat F X) Y) →
    ( type-hom-Large-Precat C X (obj-functor-Large-Precat G Y))
  map-inv-equiv-is-adjoint-pair-Large-Precat H X Y =
    map-inv-equiv (equiv-is-adjoint-pair-Large-Precat H X Y)
    

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
      is-adjoint-pair-right-adjoint-Adjunction :
        is-adjoint-pair-Large-Precat
          left-adjoint-Adjunction
          right-adjoint-Adjunction

  open Adjunction public

  unit-Adjunction :
    (A : Adjunction) →
    natural-transformation-Large-Precat C C
      ( id-functor-Large-Precat C)
      ( comp-functor-Large-Precat
        ( right-adjoint-Adjunction A)
        ( left-adjoint-Adjunction A))
  obj-natural-transformation-Large-Precat (unit-Adjunction A) X =
    map-inv-equiv
      ( equiv-is-adjoint-pair-Large-Precat
        ( is-adjoint-pair-right-adjoint-Adjunction A)
        ( X)
        ( obj-functor-Large-Precat (left-adjoint-Adjunction A) X))
      ( id-hom-Large-Precat D)
  coherence-square-natural-transformation-Large-Precat (unit-Adjunction A) f =
    {!!}
