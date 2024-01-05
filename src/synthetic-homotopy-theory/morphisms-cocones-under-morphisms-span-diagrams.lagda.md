# Morphisms of cocones under morphisms of span diagrams

```agda
module
  synthetic-homotopy-theory.morphisms-cocones-under-morphisms-span-diagrams
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

Consider a [morphism of span diagrams](foundation.morphisms-span-diagrams.md) `h : hom-span-diagram s t` and [cocones](synthetic-homotopy-theory.cocones-under-span-diagrams.md) `c` with vertex `X` and `d` with vertex `Y` on `s` and `t`, respectively. A {{#concept "morphism of cocones under a morphism of span diagrams"}} from `c` to `d` under `h` consists of a map `u : X → Y` such that the cube

```text
          S
         /|\
        / | \
       /  hS \
      ∨   ∨   ∨
     A    T    B
     |\  / \  /|
  hA | \/   \/ | hB
     | /\   /\ |
     ∨∨  ∨ ∨  ∨∨
     A'   X    B'
      \   |   /
       \  |u /
        \ | /
         ∨∨∨
          Y
```

[commutes](foundation.commuting-cubes-of-maps.md).

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (s : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram s X)
  (t : span-diagram l5 l6 l7) {Y : UU l8} (d : cocone-span-diagram t Y)
  (h : hom-span-diagram s t)
  where

  left-coherence-square-hom-cocone-hom-span-diagram :
    (X → Y) → UU (l1 ⊔ l8)
  left-coherence-square-hom-cocone-hom-span-diagram u =
    coherence-square-maps
      ( left-map-cocone-span-diagram s c)
      ( map-domain-hom-span-diagram s t h)
      ( u)
      ( left-map-cocone-span-diagram t d)

  right-coherence-square-hom-cocone-hom-span-diagram : (X → Y) → UU (l2 ⊔ l8)
  right-coherence-square-hom-cocone-hom-span-diagram u =
    coherence-square-maps
      ( right-map-cocone-span-diagram s c)
      ( map-codomain-hom-span-diagram s t h)
      ( u)
      ( right-map-cocone-span-diagram t d)

  coherence-cube-hom-cocone-hom-span-diagram :
    (u : X → Y) → 
    left-coherence-square-hom-cocone-hom-span-diagram u →
    right-coherence-square-hom-cocone-hom-span-diagram u → UU (l3 ⊔ l8)
  coherence-cube-hom-cocone-hom-span-diagram u L R =
    coherence-cube-maps
      ( left-map-span-diagram t)
      ( right-map-span-diagram t)
      ( left-map-cocone-span-diagram t d)
      ( right-map-cocone-span-diagram t d)
      ( left-map-span-diagram s)
      ( right-map-span-diagram s)
      ( left-map-cocone-span-diagram s c)
      ( right-map-cocone-span-diagram s c)
      ( spanning-map-hom-span-diagram s t h)
      ( map-domain-hom-span-diagram s t h)
      ( map-codomain-hom-span-diagram s t h)
      ( u)
      ( coherence-square-cocone-span-diagram s c)
      ( inv-htpy (left-square-hom-span-diagram s t h))
      ( inv-htpy (right-square-hom-span-diagram s t h))
      ( L)
      ( R)
      ( coherence-square-cocone-span-diagram t d)

  hom-cocone-hom-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l8)
  hom-cocone-hom-span-diagram =
    Σ ( X → Y)
      ( λ u →
        Σ ( left-coherence-square-hom-cocone-hom-span-diagram u)
          ( λ L →
            Σ ( right-coherence-square-hom-cocone-hom-span-diagram u)
              ( coherence-cube-hom-cocone-hom-span-diagram u L)))

  module _
    (u : hom-cocone-hom-span-diagram)
    where

    map-hom-cocone-hom-span-diagram : X → Y
    map-hom-cocone-hom-span-diagram = pr1 u

    left-square-hom-cocone-hom-span-diagram :
      left-coherence-square-hom-cocone-hom-span-diagram
        ( map-hom-cocone-hom-span-diagram)
    left-square-hom-cocone-hom-span-diagram =
      pr1 (pr2 u)

    right-square-hom-cocone-hom-span-diagram :
      right-coherence-square-hom-cocone-hom-span-diagram
        ( map-hom-cocone-hom-span-diagram)
    right-square-hom-cocone-hom-span-diagram =
      pr1 (pr2 (pr2 u))

    cube-hom-cocone-hom-span-diagram :
      coherence-cube-hom-cocone-hom-span-diagram
        ( map-hom-cocone-hom-span-diagram)
        ( left-square-hom-cocone-hom-span-diagram)
        ( right-square-hom-cocone-hom-span-diagram)
    cube-hom-cocone-hom-span-diagram =
      pr2 (pr2 (pr2 u))
```
