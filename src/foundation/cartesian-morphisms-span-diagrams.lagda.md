# Cartesian morphisms of span diagrams

```agda
module foundation.cartesian-morphisms-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrows
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.universe-levels
```

</details>

## Idea

A [morphism](foundation.morphisms-span-diagrams.md) `α : 𝒮 → 𝒯` of
[span diagrams](foundation.span-diagrams.md) is said to be
{{#concept "cartesian" Disambiguation="morphism of span diagrams" Agda=is-cartesian-hom-span-diagram}} if the two
squares in the diagram

```text
       h       k
  C <----- T -----> D
  |      ⌞ | ⌟      |
  |        |        |
  ∨        ∨        ∨
  A <----- S -----> B
       f       g
```

are [pullback squares](foundation-core.pullbacks.md).

## Definitions

### The predicate of being a left cartesian morphism of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (𝒯 : span-diagram l4 l5 l6) (α : hom-span-diagram 𝒮 𝒯)
  where

  is-left-cartesian-hom-span-diagram : UU (l1 ⊔ l3 ⊔ l4 ⊔ l6)
  is-left-cartesian-hom-span-diagram =
    is-cartesian-hom-arrow
      ( left-map-span-diagram 𝒮)
      ( left-map-span-diagram 𝒯)
      ( left-hom-arrow-hom-span-diagram 𝒮 𝒯 α)
```

### Left cartesian morphisms of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (𝒯 : span-diagram l4 l5 l6)
  where

  left-cartesian-hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  left-cartesian-hom-span-diagram =
    Σ (hom-span-diagram 𝒮 𝒯) (is-left-cartesian-hom-span-diagram 𝒮 𝒯)

  module _
    (h : left-cartesian-hom-span-diagram)
    where

    hom-left-cartesian-hom-span-diagram : hom-span-diagram 𝒮 𝒯
    hom-left-cartesian-hom-span-diagram = pr1 h

    map-domain-left-cartesian-hom-span-diagram :
      domain-span-diagram 𝒮 → domain-span-diagram 𝒯
    map-domain-left-cartesian-hom-span-diagram =
      map-domain-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram

    map-codomain-left-cartesian-hom-span-diagram :
      codomain-span-diagram 𝒮 → codomain-span-diagram 𝒯
    map-codomain-left-cartesian-hom-span-diagram =
      map-codomain-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram

    spanning-map-left-cartesian-hom-span-diagram :
      spanning-type-span-diagram 𝒮 → spanning-type-span-diagram 𝒯
    spanning-map-left-cartesian-hom-span-diagram =
      spanning-map-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram

    left-square-left-cartesian-hom-span-diagram :
      coherence-square-maps
        ( spanning-map-left-cartesian-hom-span-diagram)
        ( left-map-span-diagram 𝒮)
        ( left-map-span-diagram 𝒯)
        ( map-domain-left-cartesian-hom-span-diagram)
    left-square-left-cartesian-hom-span-diagram =
      left-square-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram

    left-hom-arrow-left-cartesian-hom-span-diagram :
      hom-arrow (left-map-span-diagram 𝒮) (left-map-span-diagram 𝒯)
    left-hom-arrow-left-cartesian-hom-span-diagram =
      left-hom-arrow-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram

    right-square-left-cartesian-hom-span-diagram :
      coherence-square-maps
        ( spanning-map-left-cartesian-hom-span-diagram)
        ( right-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒯)
        ( map-codomain-left-cartesian-hom-span-diagram)
    right-square-left-cartesian-hom-span-diagram =
      right-square-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram

    right-hom-arrow-left-cartesian-hom-span-diagram :
      hom-arrow (right-map-span-diagram 𝒮) (right-map-span-diagram 𝒯)
    right-hom-arrow-left-cartesian-hom-span-diagram =
      right-hom-arrow-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram

    is-left-cartesian-left-cartesian-hom-span-diagram :
      is-left-cartesian-hom-span-diagram 𝒮 𝒯 hom-left-cartesian-hom-span-diagram
    is-left-cartesian-left-cartesian-hom-span-diagram = pr2 h
```

### The predicate of being a right cartesian morphism of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (𝒯 : span-diagram l4 l5 l6) (α : hom-span-diagram 𝒮 𝒯)
  where

  is-right-cartesian-hom-span-diagram : UU (l2 ⊔ l3 ⊔ l5 ⊔ l6)
  is-right-cartesian-hom-span-diagram =
    is-cartesian-hom-arrow
      ( right-map-span-diagram 𝒮)
      ( right-map-span-diagram 𝒯)
      ( right-hom-arrow-hom-span-diagram 𝒮 𝒯 α)
```

### Right cartesian morphisms of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (𝒯 : span-diagram l4 l5 l6)
  where

  right-cartesian-hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  right-cartesian-hom-span-diagram =
    Σ (hom-span-diagram 𝒮 𝒯) (is-right-cartesian-hom-span-diagram 𝒮 𝒯)

  module _
    (h : right-cartesian-hom-span-diagram)
    where

    hom-right-cartesian-hom-span-diagram : hom-span-diagram 𝒮 𝒯
    hom-right-cartesian-hom-span-diagram = pr1 h

    map-domain-right-cartesian-hom-span-diagram :
      domain-span-diagram 𝒮 → domain-span-diagram 𝒯
    map-domain-right-cartesian-hom-span-diagram =
      map-domain-hom-span-diagram 𝒮 𝒯 hom-right-cartesian-hom-span-diagram

    map-codomain-right-cartesian-hom-span-diagram :
      codomain-span-diagram 𝒮 → codomain-span-diagram 𝒯
    map-codomain-right-cartesian-hom-span-diagram =
      map-codomain-hom-span-diagram 𝒮 𝒯 hom-right-cartesian-hom-span-diagram

    spanning-map-right-cartesian-hom-span-diagram :
      spanning-type-span-diagram 𝒮 → spanning-type-span-diagram 𝒯
    spanning-map-right-cartesian-hom-span-diagram =
      spanning-map-hom-span-diagram 𝒮 𝒯 hom-right-cartesian-hom-span-diagram

    left-square-right-cartesian-hom-span-diagram :
      coherence-square-maps
        ( spanning-map-right-cartesian-hom-span-diagram)
        ( left-map-span-diagram 𝒮)
        ( left-map-span-diagram 𝒯)
        ( map-domain-right-cartesian-hom-span-diagram)
    left-square-right-cartesian-hom-span-diagram =
      left-square-hom-span-diagram 𝒮 𝒯 hom-right-cartesian-hom-span-diagram

    left-hom-arrow-right-cartesian-hom-span-diagram :
      hom-arrow (left-map-span-diagram 𝒮) (left-map-span-diagram 𝒯)
    left-hom-arrow-right-cartesian-hom-span-diagram =
      left-hom-arrow-hom-span-diagram 𝒮 𝒯 hom-right-cartesian-hom-span-diagram

    right-square-right-cartesian-hom-span-diagram :
      coherence-square-maps
        ( spanning-map-right-cartesian-hom-span-diagram)
        ( right-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒯)
        ( map-codomain-right-cartesian-hom-span-diagram)
    right-square-right-cartesian-hom-span-diagram =
      right-square-hom-span-diagram 𝒮 𝒯 hom-right-cartesian-hom-span-diagram

    right-hom-arrow-right-cartesian-hom-span-diagram :
      hom-arrow (right-map-span-diagram 𝒮) (right-map-span-diagram 𝒯)
    right-hom-arrow-right-cartesian-hom-span-diagram =
      right-hom-arrow-hom-span-diagram 𝒮 𝒯 hom-right-cartesian-hom-span-diagram

    is-right-cartesian-right-cartesian-hom-span-diagram :
      is-right-cartesian-hom-span-diagram 𝒮 𝒯
        ( hom-right-cartesian-hom-span-diagram)
    is-right-cartesian-right-cartesian-hom-span-diagram = pr2 h
```

### The predicate of being a cartesian morphism of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (𝒯 : span-diagram l4 l5 l6) (α : hom-span-diagram 𝒮 𝒯)
  where

  is-cartesian-hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-cartesian-hom-span-diagram =
    is-left-cartesian-hom-span-diagram 𝒮 𝒯 α ×
    is-right-cartesian-hom-span-diagram 𝒮 𝒯 α
```

### Cartesian morphisms of span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  (𝒯 : span-diagram l4 l5 l6)
  where

  cartesian-hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  cartesian-hom-span-diagram =
    Σ (hom-span-diagram 𝒮 𝒯) (is-cartesian-hom-span-diagram 𝒮 𝒯)

  module _
    (h : cartesian-hom-span-diagram)
    where

    hom-cartesian-hom-span-diagram : hom-span-diagram 𝒮 𝒯
    hom-cartesian-hom-span-diagram = pr1 h

    map-domain-cartesian-hom-span-diagram :
      domain-span-diagram 𝒮 → domain-span-diagram 𝒯
    map-domain-cartesian-hom-span-diagram =
      map-domain-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram

    map-codomain-cartesian-hom-span-diagram :
      codomain-span-diagram 𝒮 → codomain-span-diagram 𝒯
    map-codomain-cartesian-hom-span-diagram =
      map-codomain-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram

    spanning-map-cartesian-hom-span-diagram :
      spanning-type-span-diagram 𝒮 → spanning-type-span-diagram 𝒯
    spanning-map-cartesian-hom-span-diagram =
      spanning-map-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram

    left-square-cartesian-hom-span-diagram :
      coherence-square-maps
        ( spanning-map-cartesian-hom-span-diagram)
        ( left-map-span-diagram 𝒮)
        ( left-map-span-diagram 𝒯)
        ( map-domain-cartesian-hom-span-diagram)
    left-square-cartesian-hom-span-diagram =
      left-square-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram

    left-hom-arrow-cartesian-hom-span-diagram :
      hom-arrow (left-map-span-diagram 𝒮) (left-map-span-diagram 𝒯)
    left-hom-arrow-cartesian-hom-span-diagram =
      left-hom-arrow-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram

    right-square-cartesian-hom-span-diagram :
      coherence-square-maps
        ( spanning-map-cartesian-hom-span-diagram)
        ( right-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒯)
        ( map-codomain-cartesian-hom-span-diagram)
    right-square-cartesian-hom-span-diagram =
      right-square-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram

    right-hom-arrow-cartesian-hom-span-diagram :
      hom-arrow (right-map-span-diagram 𝒮) (right-map-span-diagram 𝒯)
    right-hom-arrow-cartesian-hom-span-diagram =
      right-hom-arrow-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram

    is-cartesian-cartesian-hom-span-diagram :
      is-cartesian-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram
    is-cartesian-cartesian-hom-span-diagram = pr2 h

    is-left-cartesian-cartesian-hom-span-diagram :
      is-left-cartesian-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram
    is-left-cartesian-cartesian-hom-span-diagram =
      pr1 is-cartesian-cartesian-hom-span-diagram

    left-cartesian-hom-arrow-cartesian-hom-span-diagram :
      cartesian-hom-arrow
        ( left-map-span-diagram 𝒮)
        ( left-map-span-diagram 𝒯)
    pr1 left-cartesian-hom-arrow-cartesian-hom-span-diagram =
      left-hom-arrow-cartesian-hom-span-diagram
    pr2 left-cartesian-hom-arrow-cartesian-hom-span-diagram =
      is-left-cartesian-cartesian-hom-span-diagram

    is-right-cartesian-cartesian-hom-span-diagram :
      is-right-cartesian-hom-span-diagram 𝒮 𝒯 hom-cartesian-hom-span-diagram
    is-right-cartesian-cartesian-hom-span-diagram =
      pr2 is-cartesian-cartesian-hom-span-diagram

    right-cartesian-hom-arrow-cartesian-hom-span-diagram :
      cartesian-hom-arrow
        ( right-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒯)
    pr1 right-cartesian-hom-arrow-cartesian-hom-span-diagram =
      right-hom-arrow-cartesian-hom-span-diagram
    pr2 right-cartesian-hom-arrow-cartesian-hom-span-diagram =
      is-right-cartesian-cartesian-hom-span-diagram
```
