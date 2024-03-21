# Null cocones under pointed span diagrams

```agda
module synthetic-homotopy-theory.null-cocones-under-pointed-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.constant-pointed-maps
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-span-diagrams
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams
```

</details>

## Idea

The {{#concept "null cocone" Disambiguation="pointed span diagram"}} under a
[pointed span diagram](structured-types.pointed-span-diagrams.md) `𝒮` given by

```text
      f       g
  A <---- S ----> B
```

with codomain `X` is the
[cocone](synthetic-homotopy-theory.cocones-under-pointed-span-diagrams.md) under
`𝒮` consisting of the
[constant pointed maps](structured-types.constant-pointed-maps.md) `A →∗ X` and
`B →∗ X` and the canonical homotopy witnessing that the square of pointed maps

```text
        g
    S -----> B
    |        |
  f |        | const
    ∨        ∨
    A -----> X
      const
```

[commutes](structured-types.commuting-squares-of-pointed-maps.md). The null
cocone under `𝒮` provides a canonical pointing of the type
`cocone-pointed-span-diagram f g`.

## Definitions

### Null cocones under pointed span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : pointed-span-diagram l1 l2 l3)
  (X : Pointed-Type l4)
  where

  left-pointed-map-null-cocone-pointed-span-diagram :
    pointed-domain-pointed-span-diagram 𝒮 →∗ X
  left-pointed-map-null-cocone-pointed-span-diagram = constant-pointed-map _ X

  left-map-null-cocone-pointed-span-diagram :
    domain-pointed-span-diagram 𝒮 → type-Pointed-Type X
  left-map-null-cocone-pointed-span-diagram =
    map-pointed-map left-pointed-map-null-cocone-pointed-span-diagram

  preserves-point-left-map-null-cocone-pointed-span-diagram :
    left-map-null-cocone-pointed-span-diagram (point-domain-pointed-span-diagram 𝒮) ＝
    point-Pointed-Type X
  preserves-point-left-map-null-cocone-pointed-span-diagram =
    preserves-point-pointed-map left-pointed-map-null-cocone-pointed-span-diagram

  right-pointed-map-null-cocone-pointed-span-diagram :
    pointed-codomain-pointed-span-diagram 𝒮 →∗ X
  right-pointed-map-null-cocone-pointed-span-diagram = constant-pointed-map _ X

  right-map-null-cocone-pointed-span-diagram :
    codomain-pointed-span-diagram 𝒮 → type-Pointed-Type X
  right-map-null-cocone-pointed-span-diagram =
    map-pointed-map right-pointed-map-null-cocone-pointed-span-diagram

  preserves-point-right-map-null-cocone-pointed-span-diagram :
    right-map-null-cocone-pointed-span-diagram
      ( point-codomain-pointed-span-diagram 𝒮) ＝
    point-Pointed-Type X
  preserves-point-right-map-null-cocone-pointed-span-diagram =
    preserves-point-pointed-map right-pointed-map-null-cocone-pointed-span-diagram

  htpy-coherence-square-null-cocone-pointed-span-diagram :
    coherence-square-maps
      ( map-pointed-map (right-pointed-map-pointed-span-diagram 𝒮))
      ( map-pointed-map (left-pointed-map-pointed-span-diagram 𝒮))
      ( map-constant-pointed-map (pointed-codomain-pointed-span-diagram 𝒮) X)
      ( map-constant-pointed-map (pointed-domain-pointed-span-diagram 𝒮) X)
  htpy-coherence-square-null-cocone-pointed-span-diagram = refl-htpy

  coherence-point-coherence-square-null-cocone-pointed-span-diagram :
    coherence-point-unpointed-htpy-pointed-Π
      ( constant-pointed-map _ X ∘∗ (left-pointed-map-pointed-span-diagram 𝒮))
      ( constant-pointed-map _ X ∘∗ (right-pointed-map-pointed-span-diagram 𝒮))
      ( htpy-coherence-square-null-cocone-pointed-span-diagram)
  coherence-point-coherence-square-null-cocone-pointed-span-diagram =
    right-whisker-concat
      ( ( ap-const
          ( point-Pointed-Type X)
          ( preserves-point-left-map-pointed-span-diagram 𝒮)) ∙
        ( inv
          ( ap-const
            ( point-Pointed-Type X)
            ( preserves-point-right-map-pointed-span-diagram 𝒮))))
      ( refl)

  coherence-square-null-cocone-pointed-span-diagram :
    coherence-square-pointed-maps
      ( right-pointed-map-pointed-span-diagram 𝒮)
      ( left-pointed-map-pointed-span-diagram 𝒮)
      ( right-pointed-map-null-cocone-pointed-span-diagram)
      ( left-pointed-map-null-cocone-pointed-span-diagram)
  pr1 coherence-square-null-cocone-pointed-span-diagram =
    htpy-coherence-square-null-cocone-pointed-span-diagram
  pr2 coherence-square-null-cocone-pointed-span-diagram =
    coherence-point-coherence-square-null-cocone-pointed-span-diagram

  null-cocone-pointed-span-diagram : cocone-pointed-span-diagram 𝒮 X
  pr1 null-cocone-pointed-span-diagram =
    left-pointed-map-null-cocone-pointed-span-diagram
  pr1 (pr2 null-cocone-pointed-span-diagram) =
    right-pointed-map-null-cocone-pointed-span-diagram
  pr2 (pr2 null-cocone-pointed-span-diagram) =
    coherence-square-null-cocone-pointed-span-diagram
```

### The pointed type of cocones under pointed span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : pointed-span-diagram l1 l2 l3)
  (X : Pointed-Type l4)
  where

  type-cocone-pointed-type-Pointed-Type : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-cocone-pointed-type-Pointed-Type = cocone-pointed-span-diagram 𝒮 X

  cocone-pointed-type-Pointed-Type : Pointed-Type (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 cocone-pointed-type-Pointed-Type = type-cocone-pointed-type-Pointed-Type
  pr2 cocone-pointed-type-Pointed-Type = null-cocone-pointed-span-diagram 𝒮 X
```
