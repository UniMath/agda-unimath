# Pushouts of pointed types

```agda
module synthetic-homotopy-theory.pushouts-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans-of-pointed-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a span of pointed maps, then the pushout is in fact a pushout diagram in
the category of pointed types.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  pushout-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → Pointed-Type (l1 ⊔ l2 ⊔ l3)
  pr1 (pushout-Pointed-Type f g) =
    pushout (map-pointed-map f) (map-pointed-map g)
  pr2 (pushout-Pointed-Type f g) =
    inl-pushout
      ( map-pointed-map f)
      ( map-pointed-map g)
      ( point-Pointed-Type A)
```

## Properties

### The pushout of a pointed map along a pointed map is pointed

```agda
module _
  {l1 l2 l3 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  inl-pushout-Pointed-Type :
      (f : S →∗ A) (g : S →∗ B) → A →∗ pushout-Pointed-Type f g
  pr1 (inl-pushout-Pointed-Type f g) =
    inl-pushout (map-pointed-map f) (map-pointed-map g)
  pr2 (inl-pushout-Pointed-Type f g) = refl

  inr-pushout-Pointed-Type :
      (f : S →∗ A) (g : S →∗ B) → B →∗ pushout-Pointed-Type f g
  pr1 (inr-pushout-Pointed-Type f g) =
    inr-pushout (map-pointed-map f) (map-pointed-map g)
  pr2 (inr-pushout-Pointed-Type f g) =
      ( ( ap
          ( inr-pushout (map-pointed-map f) (map-pointed-map g))
          ( inv (preserves-point-pointed-map g))) ∙
        ( inv
          ( glue-pushout
            ( map-pointed-map f)
            ( map-pointed-map g)
            ( point-Pointed-Type S)))) ∙
      ( ap
        ( inl-pushout (map-pointed-map f) (map-pointed-map g))
        ( preserves-point-pointed-map f))
```

### The cogap map for pushouts of pointed types

```agda
module _
  {l1 l2 l3 : Level}
  {S : Pointed-Type l1} {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  map-cogap-Pointed-Type :
    {l4 : Level}
    (f : S →∗ A) (g : S →∗ B) →
    {X : Pointed-Type l4} →
    type-cocone-Pointed-Type f g X →
    type-Pointed-Type (pushout-Pointed-Type f g) → type-Pointed-Type X
  map-cogap-Pointed-Type f g c =
    cogap
      ( map-pointed-map f)
      ( map-pointed-map g)
      ( cocone-type-cocone-Pointed-Type f g c)

  cogap-Pointed-Type :
    {l4 : Level}
    (f : S →∗ A) (g : S →∗ B) →
    {X : Pointed-Type l4} →
    type-cocone-Pointed-Type f g X → pushout-Pointed-Type f g →∗ X
  pr1 (cogap-Pointed-Type f g c) = map-cogap-Pointed-Type f g c
  pr2 (cogap-Pointed-Type f g {X} c) =
    ( compute-inl-cogap
      ( map-pointed-map f)
      ( map-pointed-map g)
      ( cocone-type-cocone-Pointed-Type f g c)
      ( point-Pointed-Type A)) ∙
    ( preserves-point-pointed-map
      ( horizontal-pointed-map-cocone-Pointed-Type f g c))
```
