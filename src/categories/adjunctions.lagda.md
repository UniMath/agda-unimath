---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.adjunctions where

open import categories.large-categories public

module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  (F : functor-Large-Precat C D γF) (G : functor-Large-Precat D C γG)
  where

  record is-right-adjoint-functor-Large-Precat : Setω where
    field
      equiv :
        {l1 l2 : Level} (X : obj-Large-Precat C l1)
        (Y : obj-Large-Precat D l2) →
        ( type-hom-Large-Precat C X (obj-functor-Large-Precat G Y)) ≃
        ( type-hom-Large-Precat D (obj-functor-Large-Precat F X) Y)
      naturality :
        {l1 l2 l3 l4 : Level} {X1 : obj-Large-Precat C l1}
        {X2 : obj-Large-Precat C l2} {Y1 : obj-Large-Precat D l3}
        {Y2 : obj-Large-Precat D l4} (f : type-hom-Large-Precat C X2 X1)
        (g : type-hom-Large-Precat D Y1 Y2) →
        ( ( map-equiv (equiv X2 Y2)) ∘
          ( λ h →
            comp-hom-Large-Precat C
              ( comp-hom-Large-Precat C (hom-functor-Large-Precat G g) h) f)) ~
        ( ( λ h →
            comp-hom-Large-Precat D
              ( comp-hom-Large-Precat D g h)
              ( hom-functor-Large-Precat F f)) ∘
          ( map-equiv (equiv X1 Y1)))
