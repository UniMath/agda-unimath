# The action of dependent functions on cocones under span diagrams

```agda
module
  synthetic-homotopy-theory.action-dependent-functions-cocones-under-span-diagrams
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.dependent-pair-types
open import foundation.span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
```

</details>

## Idea

Consider a cocone `c := (i , j , H)` with codomain `X` under a span diagram `𝒮 := (A <-f- S -g-> B)`. Furthermore, consider a dependent function `h : (x : X) → Y x`. Then `h` induces the dependent cocone

```text
 (i' , j' , H') : dependent-cocone 𝒮 c Y
```

given by

```text
  i' := h ∘ i
  j' := h ∘ j
  H' := apd h ∘ H.
```

Here, `apd` is the [action of dependent functions on identifications](foundation.action-on-identifications-dependent-functions.md).

## Definitions

### The action of dependent functions on cocones under span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X) (P : X → UU l5)
  where

  dependent-cocone-map-span-diagram :
    ((x : X) → P x) → dependent-cocone-span-diagram 𝒮 c P
  pr1 (dependent-cocone-map-span-diagram h) a =
    h (left-map-cocone-span-diagram 𝒮 c a)
  pr1 (pr2 (dependent-cocone-map-span-diagram h)) b =
    h (right-map-cocone-span-diagram 𝒮 c b)
  pr2 (pr2 (dependent-cocone-map-span-diagram h)) s =
    apd h (coherence-square-cocone-span-diagram 𝒮 c s)
```
