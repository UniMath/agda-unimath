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

Consider an
[equivalence of span diagrams](foundation.equivalences-span-diagrams.md)
`e : equiv-span-diagram s t` and
[cocones](synthetic-homotopy-theory.cocones-under-span-diagrams.md) `c` with
vertex `X` and `d` with vertex `Y` on `𝒮` and `t`, respectively. An
{{#concept "equivalence of cocones under an equivalence of span diagrams"}} from
`c` to `d` under `e` consists of an
[equivalence](foundation-core.equivalences.md) `e : X ≃ Y` such that the cube

```text
              S
            / | \
          /   |   \
        /   hS|     \
      ∨       ∨       ∨
     A        T        B
     | \    /   \    / |
  hA |   \/       \/   | hB
     |  /  \     /  \  |
     ∨∨      ∨ ∨      ∨∨
     A'       X        B'
       \      |      /
         \    |u   /
           \  |  /
             ∨∨∨
              Y
```

[commutes](foundation.commuting-cubes-of-maps.md).

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (𝒮 : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (𝒯 : span-diagram l5 l6 l7) {Y : UU l8} (d : cocone-span-diagram 𝒯 Y)
  (e : equiv-span-diagram 𝒮 𝒯)
  where

  left-coherence-square-equiv-cocone-equiv-span-diagram :
    (X ≃ Y) → UU (l1 ⊔ l8)
  left-coherence-square-equiv-cocone-equiv-span-diagram u =
    coherence-square-maps
      ( left-map-cocone-span-diagram 𝒮 c)
      ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
      ( map-equiv u)
      ( left-map-cocone-span-diagram 𝒯 d)

  right-coherence-square-equiv-cocone-equiv-span-diagram :
    (X ≃ Y) → UU (l2 ⊔ l8)
  right-coherence-square-equiv-cocone-equiv-span-diagram u =
    coherence-square-maps
      ( right-map-cocone-span-diagram 𝒮 c)
      ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
      ( map-equiv u)
      ( right-map-cocone-span-diagram 𝒯 d)

  coherence-cube-equiv-cocone-equiv-span-diagram :
    (u : X ≃ Y) →
    left-coherence-square-equiv-cocone-equiv-span-diagram u →
    right-coherence-square-equiv-cocone-equiv-span-diagram u → UU (l3 ⊔ l8)
  coherence-cube-equiv-cocone-equiv-span-diagram u L R =
    coherence-cube-maps
      ( left-map-span-diagram 𝒯)
      ( right-map-span-diagram 𝒯)
      ( left-map-cocone-span-diagram 𝒯 d)
      ( right-map-cocone-span-diagram 𝒯 d)
      ( left-map-span-diagram 𝒮)
      ( right-map-span-diagram 𝒮)
      ( left-map-cocone-span-diagram 𝒮 c)
      ( right-map-cocone-span-diagram 𝒮 c)
      ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
      ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
      ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
      ( map-equiv u)
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( inv-htpy (left-square-equiv-span-diagram 𝒮 𝒯 e))
      ( inv-htpy (right-square-equiv-span-diagram 𝒮 𝒯 e))
      ( L)
      ( R)
      ( coherence-square-cocone-span-diagram 𝒯 d)

  equiv-cocone-equiv-span-diagram : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l8)
  equiv-cocone-equiv-span-diagram =
    Σ ( X ≃ Y)
      ( λ u →
        Σ ( left-coherence-square-equiv-cocone-equiv-span-diagram u)
          ( λ L →
            Σ ( right-coherence-square-equiv-cocone-equiv-span-diagram u)
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

    left-square-equiv-cocone-equiv-span-diagram :
      left-coherence-square-equiv-cocone-equiv-span-diagram
        ( equiv-equiv-cocone-equiv-span-diagram)
    left-square-equiv-cocone-equiv-span-diagram =
      pr1 (pr2 u)

    right-square-equiv-cocone-equiv-span-diagram :
      right-coherence-square-equiv-cocone-equiv-span-diagram
        ( equiv-equiv-cocone-equiv-span-diagram)
    right-square-equiv-cocone-equiv-span-diagram =
      pr1 (pr2 (pr2 u))

    cube-equiv-cocone-equiv-span-diagram :
      coherence-cube-equiv-cocone-equiv-span-diagram
        ( equiv-equiv-cocone-equiv-span-diagram)
        ( left-square-equiv-cocone-equiv-span-diagram)
        ( right-square-equiv-cocone-equiv-span-diagram)
    cube-equiv-cocone-equiv-span-diagram =
      pr2 (pr2 (pr2 u))

    hom-cocone-equiv-cocone-equiv-span-diagram :
      hom-cocone-hom-span-diagram 𝒮 c 𝒯 d (hom-equiv-span-diagram 𝒮 𝒯 e)
    pr1 hom-cocone-equiv-cocone-equiv-span-diagram =
      map-equiv-cocone-equiv-span-diagram
    pr1 (pr2 hom-cocone-equiv-cocone-equiv-span-diagram) =
      left-square-equiv-cocone-equiv-span-diagram
    pr1 (pr2 (pr2 hom-cocone-equiv-cocone-equiv-span-diagram)) =
      right-square-equiv-cocone-equiv-span-diagram
    pr2 (pr2 (pr2 hom-cocone-equiv-cocone-equiv-span-diagram)) =
      cube-equiv-cocone-equiv-span-diagram
```

## Properties

### For any equivalence of cocones under an equivalence of span diagrams, there is a naturality square involving `cocone-map`

This remains to be formalized.
