# The action on cocones under span diagrams of functions

```agda
module
  synthetic-homotopy-theory.action-on-cocones-under-span-diagrams-functions
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B`.
equipped with a
[cocone](synthetic-homotopy-theory.cocones-under-span-diagrams.md)
`c := (i , j , H)` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |   H    | j
    V        V
    A -----> X.
        i
```

Then any map `h : X → Y` induces a cocone

```text
         g
    S -------> B
    |          |
  f |  h · H   | h ∘ j
    V          V
    A -------> Y.
       h ∘ i
```

This
{{#concept "action on cocones under span diagrams" Disambiguation="functions" Agda=cocone-map-span-diagram}}
is used to express the
[universal property of pushouts](synthetic-homotopy-theory.universal-property-pushouts.md).

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4} {Y : UU l5}
  (c : cocone-span-diagram 𝒮 X) (h : X → Y)
  where

  left-map-cocone-map-span-diagram : domain-span-diagram 𝒮 → Y
  left-map-cocone-map-span-diagram =
    h ∘ left-map-cocone-span-diagram 𝒮 c

  right-map-cocone-map-span-diagram : codomain-span-diagram 𝒮 → Y
  right-map-cocone-map-span-diagram =
    h ∘ right-map-cocone-span-diagram 𝒮 c

  coherence-square-cocone-map-span-diagram :
    coherence-square-maps
      ( right-map-span-diagram 𝒮)
      ( left-map-span-diagram 𝒮)
      ( right-map-cocone-map-span-diagram)
      ( left-map-cocone-map-span-diagram)
  coherence-square-cocone-map-span-diagram =
    h ·l coherence-square-cocone-span-diagram 𝒮 c

  cocone-map-span-diagram : cocone-span-diagram 𝒮 Y
  pr1 cocone-map-span-diagram = left-map-cocone-map-span-diagram
  pr1 (pr2 cocone-map-span-diagram) = right-map-cocone-map-span-diagram
  pr2 (pr2 cocone-map-span-diagram) = coherence-square-cocone-map-span-diagram
```

## Properties

### Computing `cocone-map` at the identity function

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  where

  compute-id-cocone-map-span-diagram :
    (c : cocone-span-diagram 𝒮 X) → cocone-map-span-diagram 𝒮 c id ＝ c
  compute-id-cocone-map-span-diagram c =
    eq-pair-Σ refl
      ( eq-pair-Σ refl
        ( eq-htpy (ap-id ∘ coherence-square-cocone-span-diagram 𝒮 c)))
```

### Computing `cocone-map` at a composition of functions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  where

  compute-comp-cocone-map-span-diagram :
    (c : cocone-span-diagram 𝒮 X) (h : X → Y) (k : Y → Z) →
    cocone-map-span-diagram 𝒮 c (k ∘ h) ＝
    cocone-map-span-diagram 𝒮 (cocone-map-span-diagram 𝒮 c h) k
  compute-comp-cocone-map-span-diagram (i , j , H) h k =
    eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy (ap-comp k h ∘ H)))
```
