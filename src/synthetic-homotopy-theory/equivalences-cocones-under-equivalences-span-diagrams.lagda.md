# Equivalences of cocones under equivalences of span diagrams

```agda
module
  synthetic-homotopy-theory.equivalences-cocones-under-equivalences-span-diagrams
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-span-diagrams
open import foundation.homotopies
open import foundation.span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.morphisms-cocones-under-morphisms-span-diagrams
```

</details>

## Idea

Consider an [equivalence of span diagrams](foundation.equivalences-span-diagrams.md) `e : equiv-span-diagram s t` and [cocones](synthetic-homotopy-theory.cocones-under-span-diagrams.md) `c` with vertex `X` and `d` with vertex `Y` on `s` and `t`, respectively. An {{#concept "equivalence of cocones under an equivalence of span diagrams"}} from `c` to `d` under `e` consists of an [equivalence](foundation-core.equivalences.md) `e : X ≃ Y` such that the cube

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
  (e : equiv-span-diagram s t)
  where

  horizontal-coherence-square-equiv-cocone-equiv-span-diagram :
    (X ≃ Y) → UU (l1 ⊔ l8)
  horizontal-coherence-square-equiv-cocone-equiv-span-diagram u =
    coherence-square-maps
      ( horizontal-map-cocone-span-diagram s c)
      ( map-domain-equiv-span-diagram s t e)
      ( map-equiv u)
      ( horizontal-map-cocone-span-diagram t d)

  vertical-coherence-square-equiv-cocone-equiv-span-diagram :
    (X ≃ Y) → UU (l2 ⊔ l8)
  vertical-coherence-square-equiv-cocone-equiv-span-diagram u =
    coherence-square-maps
      ( vertical-map-cocone-span-diagram s c)
      ( map-codomain-equiv-span-diagram s t e)
      ( map-equiv u)
      ( vertical-map-cocone-span-diagram t d)

  coherence-cube-equiv-cocone-equiv-span-diagram :
    (u : X ≃ Y) → 
    horizontal-coherence-square-equiv-cocone-equiv-span-diagram u →
    vertical-coherence-square-equiv-cocone-equiv-span-diagram u → UU (l3 ⊔ l8)
  coherence-cube-equiv-cocone-equiv-span-diagram u L R =
    coherence-cube-maps
      ( left-map-span-diagram t)
      ( right-map-span-diagram t)
      ( horizontal-map-cocone-span-diagram t d)
      ( vertical-map-cocone-span-diagram t d)
      ( left-map-span-diagram s)
      ( right-map-span-diagram s)
      ( horizontal-map-cocone-span-diagram s c)
      ( vertical-map-cocone-span-diagram s c)
      ( spanning-map-equiv-span-diagram s t e)
      ( map-domain-equiv-span-diagram s t e)
      ( map-codomain-equiv-span-diagram s t e)
      ( map-equiv u)
      ( coherence-square-cocone-span-diagram s c)
      ( inv-htpy (left-square-equiv-span-diagram s t e))
      ( inv-htpy (right-square-equiv-span-diagram s t e))
      ( L)
      ( R)
      ( coherence-square-cocone-span-diagram t d)

  equiv-cocone-equiv-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l8)
  equiv-cocone-equiv-span-diagram =
    Σ ( X ≃ Y)
      ( λ u →
        Σ ( horizontal-coherence-square-equiv-cocone-equiv-span-diagram u)
          ( λ L →
            Σ ( vertical-coherence-square-equiv-cocone-equiv-span-diagram u)
              ( coherence-cube-equiv-cocone-equiv-span-diagram u L)))

  module _
    (u : equiv-cocone-equiv-span-diagram)
    where

    equiv-equiv-cocone-equiv-span-diagram : X ≃ Y
    equiv-equiv-cocone-equiv-span-diagram = pr1 u

    map-equiv-cocone-equiv-span-diagram : X → Y
    map-equiv-cocone-equiv-span-diagram =
      map-equiv equiv-equiv-cocone-equiv-span-diagram

    is-equiv-equiv-cocone-equiv-span-diagram :
      is-equiv map-equiv-cocone-equiv-span-diagram
    is-equiv-equiv-cocone-equiv-span-diagram =
      is-equiv-map-equiv equiv-equiv-cocone-equiv-span-diagram

    horizontal-square-equiv-cocone-equiv-span-diagram :
      horizontal-coherence-square-equiv-cocone-equiv-span-diagram
        ( equiv-equiv-cocone-equiv-span-diagram)
    horizontal-square-equiv-cocone-equiv-span-diagram =
      pr1 (pr2 u)

    vertical-square-equiv-cocone-equiv-span-diagram :
      vertical-coherence-square-equiv-cocone-equiv-span-diagram
        ( equiv-equiv-cocone-equiv-span-diagram)
    vertical-square-equiv-cocone-equiv-span-diagram =
      pr1 (pr2 (pr2 u))

    cube-equiv-cocone-equiv-span-diagram :
      coherence-cube-equiv-cocone-equiv-span-diagram
        ( equiv-equiv-cocone-equiv-span-diagram)
        ( horizontal-square-equiv-cocone-equiv-span-diagram)
        ( vertical-square-equiv-cocone-equiv-span-diagram)
    cube-equiv-cocone-equiv-span-diagram =
      pr2 (pr2 (pr2 u))

    hom-cocone-equiv-cocone-equiv-span-diagram :
      hom-cocone-hom-span-diagram s c t d (hom-equiv-span-diagram s t e)
    pr1 hom-cocone-equiv-cocone-equiv-span-diagram =
      map-equiv-cocone-equiv-span-diagram
    pr1 (pr2 hom-cocone-equiv-cocone-equiv-span-diagram) =
      horizontal-square-equiv-cocone-equiv-span-diagram
    pr1 (pr2 (pr2 hom-cocone-equiv-cocone-equiv-span-diagram)) =
      vertical-square-equiv-cocone-equiv-span-diagram
    pr2 (pr2 (pr2 hom-cocone-equiv-cocone-equiv-span-diagram)) =
      cube-equiv-cocone-equiv-span-diagram
```

