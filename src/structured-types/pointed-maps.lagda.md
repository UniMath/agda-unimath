# Pointed maps

```agda
{-# OPTIONS --without-K --exact-split #-}

module structured-types.pointed-maps where

open import foundation.constant-maps using (const)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (_∘_; id)
open import foundation.identity-types using (Id; refl; tr; inv; apd; _∙_; ap)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import structured-types.pointed-dependent-functions using
  ( pointed-Π; function-pointed-Π; preserves-point-function-pointed-Π)
open import structured-types.pointed-families-of-types using
  ( Pointed-Fam; fam-Pointed-Fam; pt-Pointed-Fam; constant-Pointed-Fam)
open import structured-types.pointed-types using
  ( Pointed-Type; type-Pointed-Type; pt-Pointed-Type)
```

## Idea

A pointed map from a pointed type `A` to a pointed type `B` is a base point preserving function from `A` to `B`.

```agda
module _
  {l1 l2 : Level}
  where

  _→*_ : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  A →* B = pointed-Π A (constant-Pointed-Fam A B)

  [_→*_] : Pointed-Type l1 → Pointed-Type l2 → Pointed-Type (l1 ⊔ l2)
  [ A →* B ] =
    pair
      ( A →* B)
      ( pair
        ( const (type-Pointed-Type A) (type-Pointed-Type B) (pt-Pointed-Type B))
        ( refl))

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where
  
  map-pointed-map : A →* B → type-Pointed-Type A → type-Pointed-Type B
  map-pointed-map f = pr1 f

  preserves-point-map-pointed-map :
    (f : A →* B) →
    Id (map-pointed-map f (pt-Pointed-Type A)) (pt-Pointed-Type B)
  preserves-point-map-pointed-map f = pr2 f

module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Fam l3 B) (f : A →* B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  precomp-Pointed-Fam =
    pair
      ( fam-Pointed-Fam B C ∘ map-pointed-map A B f)
      ( tr
        ( fam-Pointed-Fam B C)
        ( inv (preserves-point-map-pointed-map A B f))
        ( pt-Pointed-Fam B C))

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  precomp-pointed-Π g =
    pair
      ( λ x → function-pointed-Π B C g (map-pointed-map A B f x))
      ( ( inv
          ( apd
            ( function-pointed-Π B C g)
            ( inv (preserves-point-map-pointed-map A B f)))) ∙
        ( ap
          ( tr
            ( fam-Pointed-Fam B C)
            ( inv (preserves-point-map-pointed-map A B f)))
          ( preserves-point-function-pointed-Π B C g)))

module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Type l3)
  where

  precomp-pointed-map : A →* B → B →* C → A →* C
  precomp-pointed-map f g =
    pair
      ( map-pointed-map B C g ∘ map-pointed-map A B f)
      ( ( ap (map-pointed-map B C g) (preserves-point-map-pointed-map A B f)) ∙
        ( preserves-point-map-pointed-map B C g))

  comp-pointed-map : B →* C → A →* B → A →* C
  comp-pointed-map g f = precomp-pointed-map f g

module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  id-pointed-map : A →* A
  id-pointed-map = pair id refl
```
