# Cartesian morphisms of span diagrams

```agda
module foundation.cartesian-morphisms-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.cartesian-morphisms-arrows
open import foundation.dependent-pair-types
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.universe-levels
```

</details>

## Idea

A [morphism](foundation.morphisms-span-diagrams.md) `α : 𝒮 → 𝒯` of [span diagrams](foundation.span-diagrams.md) is said to be {{#concept "cartesian" Disambiguation="morphism of span diagrams"}} if the two squares in the diagram

```text
       h       k
  C <----- T -----> D
  |        |        |
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
```
