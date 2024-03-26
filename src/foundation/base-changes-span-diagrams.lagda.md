# Base changes of span diagrams

```agda
module foundation.base-changes-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrows
open import foundation.cartesian-morphisms-span-diagrams
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.universe-levels
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮 := (A <-f- S -g-> B)`.
A
{{#concept "base change" Disambiguation="span diagram" Agda=base-change-span-diagram}}
of `𝒮` consists of a span diagram `𝒯` and a
[cartesian morphism](foundation.cartesian-morphisms-span-diagrams.md) of span
diagrams `𝒯 → 𝒮`.

## Definitions

### Base changes of span diagrams

```agda
module _
  {l1 l2 l3 : Level} (l4 l5 l6 : Level) (𝒮 : span-diagram l1 l2 l3)
  where

  base-change-span-diagram :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ lsuc l6)
  base-change-span-diagram =
    Σ (span-diagram l4 l5 l6) (λ 𝒯 → cartesian-hom-span-diagram 𝒯 𝒮)

module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (f : base-change-span-diagram l4 l5 l6 𝒮)
  where

  span-diagram-base-change-span-diagram : span-diagram l4 l5 l6
  span-diagram-base-change-span-diagram = pr1 f

  domain-span-diagram-base-change-span-diagram : UU l4
  domain-span-diagram-base-change-span-diagram =
    domain-span-diagram span-diagram-base-change-span-diagram

  codomain-span-diagram-base-change-span-diagram : UU l5
  codomain-span-diagram-base-change-span-diagram =
    codomain-span-diagram span-diagram-base-change-span-diagram

  spanning-type-span-diagram-base-change-span-diagram : UU l6
  spanning-type-span-diagram-base-change-span-diagram =
    spanning-type-span-diagram span-diagram-base-change-span-diagram

  left-map-span-diagram-base-change-span-diagram :
    spanning-type-span-diagram-base-change-span-diagram →
    domain-span-diagram-base-change-span-diagram
  left-map-span-diagram-base-change-span-diagram =
    left-map-span-diagram span-diagram-base-change-span-diagram

  right-map-span-diagram-base-change-span-diagram :
    spanning-type-span-diagram-base-change-span-diagram →
    codomain-span-diagram-base-change-span-diagram
  right-map-span-diagram-base-change-span-diagram =
    right-map-span-diagram span-diagram-base-change-span-diagram

  cartesian-hom-base-change-span-diagram :
    cartesian-hom-span-diagram span-diagram-base-change-span-diagram 𝒮
  cartesian-hom-base-change-span-diagram = pr2 f

  hom-cartesian-hom-base-change-span-diagram :
    hom-span-diagram span-diagram-base-change-span-diagram 𝒮
  hom-cartesian-hom-base-change-span-diagram =
    hom-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( cartesian-hom-base-change-span-diagram)

  map-domain-cartesian-hom-base-change-span-diagram :
    domain-span-diagram span-diagram-base-change-span-diagram →
    domain-span-diagram 𝒮
  map-domain-cartesian-hom-base-change-span-diagram =
    map-domain-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)

  map-codomain-cartesian-hom-base-change-span-diagram :
    codomain-span-diagram span-diagram-base-change-span-diagram →
    codomain-span-diagram 𝒮
  map-codomain-cartesian-hom-base-change-span-diagram =
    map-codomain-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)

  spanning-map-cartesian-hom-base-change-span-diagram :
    spanning-type-span-diagram span-diagram-base-change-span-diagram →
    spanning-type-span-diagram 𝒮
  spanning-map-cartesian-hom-base-change-span-diagram =
    spanning-map-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)

  left-square-cartesian-hom-base-change-span-diagram :
    coherence-square-maps
      ( spanning-map-cartesian-hom-base-change-span-diagram)
      ( left-map-span-diagram span-diagram-base-change-span-diagram)
      ( left-map-span-diagram 𝒮)
      ( map-domain-cartesian-hom-base-change-span-diagram)
  left-square-cartesian-hom-base-change-span-diagram =
    left-square-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)

  left-hom-arrow-cartesian-hom-base-change-span-diagram :
    hom-arrow
      ( left-map-span-diagram span-diagram-base-change-span-diagram)
      ( left-map-span-diagram 𝒮)
  left-hom-arrow-cartesian-hom-base-change-span-diagram =
    left-hom-arrow-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)

  right-square-cartesian-hom-base-change-span-diagram :
    coherence-square-maps
      ( spanning-map-cartesian-hom-base-change-span-diagram)
      ( right-map-span-diagram span-diagram-base-change-span-diagram)
      ( right-map-span-diagram 𝒮)
      ( map-codomain-cartesian-hom-base-change-span-diagram)
  right-square-cartesian-hom-base-change-span-diagram =
    right-square-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)

  right-hom-arrow-cartesian-hom-base-change-span-diagram :
    hom-arrow
      ( right-map-span-diagram span-diagram-base-change-span-diagram)
      ( right-map-span-diagram 𝒮)
  right-hom-arrow-cartesian-hom-base-change-span-diagram =
    right-hom-arrow-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)

  is-cartesian-cartesian-hom-base-change-span-diagram :
    is-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)
  is-cartesian-cartesian-hom-base-change-span-diagram =
    is-cartesian-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( cartesian-hom-base-change-span-diagram)

  is-left-cartesian-cartesian-hom-base-change-span-diagram :
    is-left-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)
  is-left-cartesian-cartesian-hom-base-change-span-diagram =
    is-left-cartesian-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( cartesian-hom-base-change-span-diagram)

  left-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram :
    cartesian-hom-arrow
      ( left-map-span-diagram span-diagram-base-change-span-diagram)
      ( left-map-span-diagram 𝒮)
  left-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram =
    left-cartesian-hom-arrow-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( cartesian-hom-base-change-span-diagram)

  is-right-cartesian-cartesian-hom-base-change-span-diagram :
    is-right-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( hom-cartesian-hom-base-change-span-diagram)
  is-right-cartesian-cartesian-hom-base-change-span-diagram =
    is-right-cartesian-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( cartesian-hom-base-change-span-diagram)

  right-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram :
    cartesian-hom-arrow
      ( right-map-span-diagram span-diagram-base-change-span-diagram)
      ( right-map-span-diagram 𝒮)
  right-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram =
    right-cartesian-hom-arrow-cartesian-hom-span-diagram
      ( span-diagram-base-change-span-diagram)
      ( 𝒮)
      ( cartesian-hom-base-change-span-diagram)
```
