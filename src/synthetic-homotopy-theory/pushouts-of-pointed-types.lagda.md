# Pushouts of pointed types

```agda
module synthetic-homotopy-theory.pushouts-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.commuting-triangles-of-pointed-maps
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-span-diagrams
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given a span of [pointed maps](structured-types.pointed-maps.md), then the
[pushout](synthetic-homotopy-theory.pushouts.md) is in fact a pushout diagram in
the (wild) category of [pointed types](structured-types.pointed-types.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (𝒮 : pointed-span-diagram l1 l2 l3)
  where

  standard-pointed-pushout :
    Pointed-Type (l1 ⊔ l2 ⊔ l3)
  pr1 standard-pointed-pushout =
    standard-pushout
      ( span-diagram-pointed-span-diagram 𝒮)
  pr2 standard-pointed-pushout =
    inl-standard-pushout
      ( span-diagram-pointed-span-diagram 𝒮)
      ( point-domain-pointed-span-diagram 𝒮)
```

## Properties

### The pushout of a pointed map along a pointed map is pointed

```agda
module _
  {l1 l2 l3 : Level}
  (𝒮 : pointed-span-diagram l1 l2 l3)
  where

  inl-standard-pointed-pushout :
    pointed-domain-pointed-span-diagram 𝒮 →∗ standard-pointed-pushout 𝒮
  pr1 inl-standard-pointed-pushout =
    inl-standard-pushout (span-diagram-pointed-span-diagram 𝒮)
  pr2 inl-standard-pointed-pushout =
    refl

  inr-standard-pointed-pushout :
    pointed-codomain-pointed-span-diagram 𝒮 →∗ standard-pointed-pushout 𝒮
  pr1 inr-standard-pointed-pushout =
    inr-standard-pushout (span-diagram-pointed-span-diagram 𝒮)
  pr2 inr-standard-pointed-pushout =
    ( ap
      ( inr-standard-pushout (span-diagram-pointed-span-diagram 𝒮))
      ( inv (preserves-point-right-map-pointed-span-diagram 𝒮))) ∙
    ( inv
      ( glue-standard-pushout
        ( span-diagram-pointed-span-diagram 𝒮)
        ( point-spanning-type-pointed-span-diagram 𝒮))) ∙
    ( ap
      ( inl-standard-pushout (span-diagram-pointed-span-diagram 𝒮))
      ( preserves-point-left-map-pointed-span-diagram 𝒮))
```

### The cogap map for pushouts of pointed types

```agda
module _
  {l1 l2 l3 : Level}
  (𝒮 : pointed-span-diagram l1 l2 l3)
  where

  map-cogap-cocone-pointed-span-diagram :
    {l4 : Level} {X : Pointed-Type l4} →
    cocone-pointed-span-diagram 𝒮 X →
    type-Pointed-Type (standard-pointed-pushout 𝒮) → type-Pointed-Type X
  map-cogap-cocone-pointed-span-diagram c =
    cogap-cocone-span-diagram
      ( span-diagram-pointed-span-diagram 𝒮)
      ( cocone-cocone-pointed-span-diagram 𝒮 c)

  cogap-cocone-pointed-span-diagram :
    {l4 : Level} {X : Pointed-Type l4} →
    cocone-pointed-span-diagram 𝒮 X →
    standard-pointed-pushout 𝒮 →∗ X
  pr1 (cogap-cocone-pointed-span-diagram c) =
    map-cogap-cocone-pointed-span-diagram c
  pr2 (cogap-cocone-pointed-span-diagram c) =
    ( compute-inl-cogap-cocone-span-diagram
      ( span-diagram-pointed-span-diagram 𝒮)
      ( cocone-cocone-pointed-span-diagram 𝒮 c)
      ( point-domain-pointed-span-diagram 𝒮)) ∙
    ( preserves-point-left-map-cocone-pointed-span-diagram 𝒮 c)
```

### Computation with the cogap map for pointed types

```
module _
  {l1 l2 l3 l4 : Level}
  (𝒮 : pointed-span-diagram l1 l2 l3)
  {X : Pointed-Type l4} (c : cocone-pointed-span-diagram 𝒮 X)
  where

  htpy-compute-inl-cogap-cocone-pointed-span-diagram :
    coherence-triangle-maps'
      ( left-map-cocone-pointed-span-diagram 𝒮 c)
      ( map-cogap-cocone-pointed-span-diagram 𝒮 c)
      ( map-pointed-map (inl-standard-pointed-pushout 𝒮))
  htpy-compute-inl-cogap-cocone-pointed-span-diagram =
    compute-inl-cogap-cocone-span-diagram
      ( span-diagram-pointed-span-diagram 𝒮)
      ( cocone-cocone-pointed-span-diagram 𝒮 c)

  coherence-point-htpy-compute-inl-cogap-cocone-pointed-span-diagram :
    coherence-point-unpointed-htpy-pointed-Π
      ( cogap-cocone-pointed-span-diagram 𝒮 c ∘∗ inl-standard-pointed-pushout 𝒮)
      ( left-pointed-map-cocone-pointed-span-diagram 𝒮 c)
      ( htpy-compute-inl-cogap-cocone-pointed-span-diagram)
  coherence-point-htpy-compute-inl-cogap-cocone-pointed-span-diagram =
    refl

  compute-inl-cogap-cocone-pointed-span-diagram :
    coherence-triangle-pointed-maps'
      ( left-pointed-map-cocone-pointed-span-diagram 𝒮 c)
      ( cogap-cocone-pointed-span-diagram 𝒮 c)
      ( inl-standard-pointed-pushout 𝒮)
  pr1 compute-inl-cogap-cocone-pointed-span-diagram  =
    htpy-compute-inl-cogap-cocone-pointed-span-diagram
  pr2 compute-inl-cogap-cocone-pointed-span-diagram  =
    coherence-point-htpy-compute-inl-cogap-cocone-pointed-span-diagram

  htpy-compute-inr-cogap-cocone-pointed-span-diagram :
    coherence-triangle-maps'
      ( right-map-cocone-pointed-span-diagram 𝒮 c)
      ( map-cogap-cocone-pointed-span-diagram 𝒮 c)
      ( map-pointed-map (inr-standard-pointed-pushout 𝒮))
  htpy-compute-inr-cogap-cocone-pointed-span-diagram =
    compute-inr-cogap-cocone-span-diagram
      ( span-diagram-pointed-span-diagram 𝒮)
      ( cocone-cocone-pointed-span-diagram 𝒮 c)
```
