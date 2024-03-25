# Cocones under pointed span diagrams

```agda
module synthetic-homotopy-theory.cocones-under-pointed-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-span-diagrams
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

A
[cocone under a span](synthetic-homotopy-theory.cocones-under-span-diagrams.md)
of [pointed types](structured-types.pointed-types.md) is a **pointed cocone** if
it consists of [pointed maps](structured-types.pointed-maps.md) equipped with a
[pointed homotopy](structured-types.pointed-homotopies.md) witnessing that the
naturality square
[commutes](structured-types.commuting-squares-of-pointed-maps.md).

The type of pointed cocones under a span of pointed types is again canonically
pointed at the constant cocone, with `refl` as coherence proof.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (𝒮 : pointed-span-diagram l1 l2 l3)
  where

  cocone-pointed-span-diagram :
    {l4 : Level} → Pointed-Type l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-pointed-span-diagram X =
    Σ ( pointed-domain-pointed-span-diagram 𝒮 →∗ X)
      ( λ i →
        Σ ( pointed-codomain-pointed-span-diagram 𝒮 →∗ X)
          ( λ j →
            coherence-square-pointed-maps
              ( right-pointed-map-pointed-span-diagram 𝒮)
              ( left-pointed-map-pointed-span-diagram 𝒮)
              ( j)
              ( i)))
```

### Components of a cocone of pointed types

```agda
module _
  {l1 l2 l3 l4 : Level}
  {X : Pointed-Type l4}
  (𝒮 : pointed-span-diagram l1 l2 l3)
  (c : cocone-pointed-span-diagram 𝒮 X)
  where

  left-pointed-map-cocone-pointed-span-diagram :
    pointed-domain-pointed-span-diagram 𝒮 →∗ X
  left-pointed-map-cocone-pointed-span-diagram = pr1 c

  left-map-cocone-pointed-span-diagram :
    domain-pointed-span-diagram 𝒮 → type-Pointed-Type X
  left-map-cocone-pointed-span-diagram =
    map-pointed-map left-pointed-map-cocone-pointed-span-diagram

  preserves-point-left-map-cocone-pointed-span-diagram :
    left-map-cocone-pointed-span-diagram
      ( point-domain-pointed-span-diagram 𝒮) ＝
    point-Pointed-Type X
  preserves-point-left-map-cocone-pointed-span-diagram =
    preserves-point-pointed-map left-pointed-map-cocone-pointed-span-diagram

  right-pointed-map-cocone-pointed-span-diagram :
    pointed-codomain-pointed-span-diagram 𝒮 →∗ X
  right-pointed-map-cocone-pointed-span-diagram = pr1 (pr2 c)

  right-map-cocone-pointed-span-diagram :
    codomain-pointed-span-diagram 𝒮 → type-Pointed-Type X
  right-map-cocone-pointed-span-diagram =
    map-pointed-map right-pointed-map-cocone-pointed-span-diagram

  preserves-point-right-map-cocone-pointed-span-diagram :
    right-map-cocone-pointed-span-diagram
      ( point-codomain-pointed-span-diagram 𝒮) ＝
    point-Pointed-Type X
  preserves-point-right-map-cocone-pointed-span-diagram =
    preserves-point-pointed-map right-pointed-map-cocone-pointed-span-diagram

  coherence-square-cocone-pointed-span-diagram :
    coherence-square-pointed-maps
      ( right-pointed-map-pointed-span-diagram 𝒮)
      ( left-pointed-map-pointed-span-diagram 𝒮)
      ( right-pointed-map-cocone-pointed-span-diagram)
      ( left-pointed-map-cocone-pointed-span-diagram)
  coherence-square-cocone-pointed-span-diagram = pr2 (pr2 c)

  htpy-coherence-square-cocone-pointed-span-diagram :
    coherence-square-maps
      ( right-map-pointed-span-diagram 𝒮)
      ( left-map-pointed-span-diagram 𝒮)
      ( right-map-cocone-pointed-span-diagram)
      ( left-map-cocone-pointed-span-diagram)
  htpy-coherence-square-cocone-pointed-span-diagram =
    coherence-square-maps-coherence-square-pointed-maps
      ( right-pointed-map-pointed-span-diagram 𝒮)
      ( left-pointed-map-pointed-span-diagram 𝒮)
      ( right-pointed-map-cocone-pointed-span-diagram)
      ( left-pointed-map-cocone-pointed-span-diagram)
      ( coherence-square-cocone-pointed-span-diagram)

  coherence-point-coherence-square-cocone-pointed-span-diagram :
    coherence-point-unpointed-htpy-pointed-Π
      ( ( left-pointed-map-cocone-pointed-span-diagram) ∘∗
        ( left-pointed-map-pointed-span-diagram 𝒮))
      ( ( right-pointed-map-cocone-pointed-span-diagram) ∘∗
        ( right-pointed-map-pointed-span-diagram 𝒮))
      ( htpy-coherence-square-cocone-pointed-span-diagram)
  coherence-point-coherence-square-cocone-pointed-span-diagram =
    coherence-point-pointed-htpy coherence-square-cocone-pointed-span-diagram

  cocone-cocone-pointed-span-diagram :
    cocone-span-diagram
      ( span-diagram-pointed-span-diagram 𝒮)
      ( type-Pointed-Type X)
  pr1 cocone-cocone-pointed-span-diagram =
    left-map-cocone-pointed-span-diagram
  pr1 (pr2 cocone-cocone-pointed-span-diagram) =
    right-map-cocone-pointed-span-diagram
  pr2 (pr2 cocone-cocone-pointed-span-diagram) =
    htpy-coherence-square-cocone-pointed-span-diagram
```

## See also

- [Pushouts of pointed types](synthetic-homotopy-theory.pushouts-of-pointed-types.md)
- [Null cocones under pointed span diagrams](synthetic-homotopy-theory.null-cocones-under-pointed-span-diagrams.md)
