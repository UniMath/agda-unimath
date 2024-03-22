# Flattening dependent span diagrams

```agda
module foundation.flattening-dependent-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.dependent-span-diagrams
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

Consider a [dependent span diagram](foundation.dependent-span-diagrams.md) `𝒯 := (P , Q , T , h , k)` over a [span diagram](foundation.span-diagrams.md) `𝒮 := (A , B , S , f , g)`. By taking [dependent pair types](foundation-core.dependent-pair-types.md), we obtain a new span diagram `Σ 𝒮 𝒯`

```text
  Σ (a : A), P a <----- Σ (s : S), T s -----> Σ (b : B), Q b.
```

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (𝒯 : dependent-span-diagram l4 l5 l6 𝒮)
  where

  domain-flattening-dependent-span-diagram : UU (l1 ⊔ l4)
  domain-flattening-dependent-span-diagram =
    Σ (domain-span-diagram 𝒮) (domain-dependent-span-diagram 𝒯)

  codomain-flattening-dependent-span-diagram : UU (l2 ⊔ l5)
  codomain-flattening-dependent-span-diagram =
    Σ (codomain-span-diagram 𝒮) (codomain-dependent-span-diagram 𝒯)

  spanning-type-flattening-dependent-span-diagram : UU (l3 ⊔ l6)
  spanning-type-flattening-dependent-span-diagram =
    Σ (spanning-type-span-diagram 𝒮) (spanning-type-dependent-span-diagram 𝒯)

  left-map-flattening-dependent-span-diagram :
    spanning-type-flattening-dependent-span-diagram →
    domain-flattening-dependent-span-diagram
  left-map-flattening-dependent-span-diagram =
    map-Σ _ (left-map-span-diagram 𝒮) (left-map-dependent-span-diagram 𝒯)

  right-map-flattening-dependent-span-diagram :
    spanning-type-flattening-dependent-span-diagram →
    codomain-flattening-dependent-span-diagram
  right-map-flattening-dependent-span-diagram =
    map-Σ _ (right-map-span-diagram 𝒮) (right-map-dependent-span-diagram 𝒯)

  span-flattening-dependent-span-diagram :
    span
      ( l3 ⊔ l6)
      ( domain-flattening-dependent-span-diagram)
      ( codomain-flattening-dependent-span-diagram)
  pr1 span-flattening-dependent-span-diagram =
    spanning-type-flattening-dependent-span-diagram
  pr1 (pr2 span-flattening-dependent-span-diagram) =
    left-map-flattening-dependent-span-diagram
  pr2 (pr2 span-flattening-dependent-span-diagram) =
    right-map-flattening-dependent-span-diagram

  flattening-dependent-span-diagram : span-diagram (l1 ⊔ l4) (l2 ⊔ l5) (l3 ⊔ l6)
  pr1 flattening-dependent-span-diagram =
    domain-flattening-dependent-span-diagram
  pr1 (pr2 flattening-dependent-span-diagram) =
    codomain-flattening-dependent-span-diagram
  pr2 (pr2 flattening-dependent-span-diagram) =
    span-flattening-dependent-span-diagram

  left-map-projection-flattening-dependent-span-diagram :
    domain-flattening-dependent-span-diagram →
    domain-span-diagram 𝒮
  left-map-projection-flattening-dependent-span-diagram = pr1

  right-map-projection-flattening-dependent-span-diagram :
    codomain-flattening-dependent-span-diagram → codomain-span-diagram 𝒮
  right-map-projection-flattening-dependent-span-diagram = pr1

  spanning-map-projection-flattening-dependent-span-diagram :
    spanning-type-flattening-dependent-span-diagram →
    spanning-type-span-diagram 𝒮
  spanning-map-projection-flattening-dependent-span-diagram = pr1

  left-square-projection-flattening-dependent-span-diagram :
    coherence-hom-arrow
      ( left-map-flattening-dependent-span-diagram)
      ( left-map-span-diagram 𝒮)
      ( spanning-map-projection-flattening-dependent-span-diagram)
      ( left-map-projection-flattening-dependent-span-diagram)
  left-square-projection-flattening-dependent-span-diagram = refl-htpy

  left-hom-arrow-projection-flattening-dependent-span-diagram :
    hom-arrow
      ( left-map-flattening-dependent-span-diagram)
      ( left-map-span-diagram 𝒮)
  pr1 left-hom-arrow-projection-flattening-dependent-span-diagram =
    spanning-map-projection-flattening-dependent-span-diagram
  pr1 (pr2 left-hom-arrow-projection-flattening-dependent-span-diagram) =
    left-map-projection-flattening-dependent-span-diagram
  pr2 (pr2 left-hom-arrow-projection-flattening-dependent-span-diagram) =
    left-square-projection-flattening-dependent-span-diagram

  right-square-projection-flattening-dependent-span-diagram :
    coherence-hom-arrow
      ( right-map-flattening-dependent-span-diagram)
      ( right-map-span-diagram 𝒮)
      ( spanning-map-projection-flattening-dependent-span-diagram)
      ( right-map-projection-flattening-dependent-span-diagram)
  right-square-projection-flattening-dependent-span-diagram = refl-htpy

  right-hom-arrow-projection-flattening-dependent-span-diagram :
    hom-arrow
      ( right-map-flattening-dependent-span-diagram)
      ( right-map-span-diagram 𝒮)
  pr1 right-hom-arrow-projection-flattening-dependent-span-diagram =
    spanning-map-projection-flattening-dependent-span-diagram
  pr1 (pr2 right-hom-arrow-projection-flattening-dependent-span-diagram) =
    right-map-projection-flattening-dependent-span-diagram
  pr2 (pr2 right-hom-arrow-projection-flattening-dependent-span-diagram) =
    right-square-projection-flattening-dependent-span-diagram

  projection-flattening-dependent-span-diagram :
    hom-span-diagram flattening-dependent-span-diagram 𝒮
  pr1 projection-flattening-dependent-span-diagram =
    left-map-projection-flattening-dependent-span-diagram
  pr1 (pr2 projection-flattening-dependent-span-diagram) =
    right-map-projection-flattening-dependent-span-diagram
  pr1 (pr2 (pr2 projection-flattening-dependent-span-diagram)) =
    spanning-map-projection-flattening-dependent-span-diagram
  pr1 (pr2 (pr2 (pr2 projection-flattening-dependent-span-diagram))) =
    left-square-projection-flattening-dependent-span-diagram
  pr2 (pr2 (pr2 (pr2 projection-flattening-dependent-span-diagram))) =
    right-square-projection-flattening-dependent-span-diagram
```
