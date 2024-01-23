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
open import foundation.function-types
open import foundation.homotopies
open import foundation.morphisms-span-diagrams
open import foundation.precomposition-functions
open import foundation.span-diagrams
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
```

</details>

## Idea

Consider a [morphism of span diagrams](foundation.morphisms-span-diagrams.md)
`h : hom-span-diagram s t` and
[cocones](synthetic-homotopy-theory.cocones-under-span-diagrams.md) `c` with
vertex `X` and `d` with vertex `Y` on `𝒮` and `t`, respectively. A
{{#concept "morphism of cocones under a morphism of span diagrams"}} from `c` to
`d` under `h` consists of a map `u : X → Y` such that the cube

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
  (f : hom-span-diagram 𝒮 𝒯)
  where

  left-coherence-square-hom-cocone-hom-span-diagram :
    (X → Y) → UU (l1 ⊔ l8)
  left-coherence-square-hom-cocone-hom-span-diagram u =
    coherence-square-maps
      ( left-map-cocone-span-diagram 𝒮 c)
      ( map-domain-hom-span-diagram 𝒮 𝒯 f)
      ( u)
      ( left-map-cocone-span-diagram 𝒯 d)

  right-coherence-square-hom-cocone-hom-span-diagram : (X → Y) → UU (l2 ⊔ l8)
  right-coherence-square-hom-cocone-hom-span-diagram u =
    coherence-square-maps
      ( right-map-cocone-span-diagram 𝒮 c)
      ( map-codomain-hom-span-diagram 𝒮 𝒯 f)
      ( u)
      ( right-map-cocone-span-diagram 𝒯 d)

  coherence-cube-hom-cocone-hom-span-diagram :
    (u : X → Y) →
    left-coherence-square-hom-cocone-hom-span-diagram u →
    right-coherence-square-hom-cocone-hom-span-diagram u → UU (l3 ⊔ l8)
  coherence-cube-hom-cocone-hom-span-diagram u L R =
    coherence-cube-maps
      ( left-map-span-diagram 𝒯)
      ( right-map-span-diagram 𝒯)
      ( left-map-cocone-span-diagram 𝒯 d)
      ( right-map-cocone-span-diagram 𝒯 d)
      ( left-map-span-diagram 𝒮)
      ( right-map-span-diagram 𝒮)
      ( left-map-cocone-span-diagram 𝒮 c)
      ( right-map-cocone-span-diagram 𝒮 c)
      ( spanning-map-hom-span-diagram 𝒮 𝒯 f)
      ( map-domain-hom-span-diagram 𝒮 𝒯 f)
      ( map-codomain-hom-span-diagram 𝒮 𝒯 f)
      ( u)
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( inv-htpy (left-square-hom-span-diagram 𝒮 𝒯 f))
      ( inv-htpy (right-square-hom-span-diagram 𝒮 𝒯 f))
      ( L)
      ( R)
      ( coherence-square-cocone-span-diagram 𝒯 d)

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

## Properties

### For any morphism of cocones under a morphism of span diagrams, there is a naturality square involving `cocone-map`

**Lemma.** Consider a morphism of cocones `(h , H)` under a morphism `f : 𝒮 → 𝒯`
of span diagrams, where the map between the codomains of the cocones is
`h : X → Y`. Then the square

```text
                                - ∘ h
          (Y → Z) ---------------------------------------> (X → Z)
             |                                                |
  cocone-map |                                                | cocone-map
             V                                                V
        cocone 𝒯 Z ------------------------------------> cocone 𝒮 Z
                    comp-cocone-hom-span-diagram 𝒮 𝒯 f
```

**Proof.** Consider a map `g : Y → Z`. Then we have to construct a homotopy of
cocones under span diagrams

```text
  f ∘ cocone-map 𝒯 d g ~ cocone-map 𝒮 c (g ∘ h)
```

from the composite of the cocone `cocoen-map 𝒯 d g` and the morphism of span
diagrams `f` to the cocone `cocone-map 𝒮 c (g ∘ h)`. The cocone on the left hand
side consists of

```text
  S ------------> B
  |               |
  |               | g ∘ j' ∘ f₁
  V               V
  A ------------> Y
     g ∘ i' ∘ f₀
```

The cocone on the right hand side consists of

```text
  S ------------> B
  |               |
  |               | g ∘ h ∘ j
  V               V
  A ------------> Y
     g ∘ h ∘ i
```

Thus we see that we have to construct a triple consisting of

```text
  α : g ∘ i' ∘ f₀ ~ g ∘ h ∘ i
  β : g ∘ j' ∘ f₁ ~ g ∘ h ∘ j
```

and a homotopy `γ` witnessing that the square of homotopies

```text
         α · f
  i ∘ f -------> i' ∘ f
    |               |
  H |      γ        | H'
    V               V
  j ∘ g -------> j' ∘ g
         β · g
```

commutes.

The homotopy `α` is defined to be `g ·l H₀`, where `H₀` is the first component
of the triple `H`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  (𝒮 : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (𝒯 : span-diagram l5 l6 l7) {Y : UU l8} (d : cocone-span-diagram 𝒯 Y)
  (f : hom-span-diagram 𝒮 𝒯) (h : hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f)
  {Z : UU l9}
  where

  module _
    (g : Y → Z)
    where

    left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      ( ( g) ∘
        ( left-map-cocone-span-diagram 𝒯 d) ∘
        ( map-domain-hom-span-diagram 𝒮 𝒯 f)) ~
      ( ( g) ∘
        ( map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h) ∘
        ( left-map-cocone-span-diagram 𝒮 c))
    left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram =
      g ·l left-square-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h

    right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      ( ( g) ∘
        ( right-map-cocone-span-diagram 𝒯 d) ∘
        ( map-codomain-hom-span-diagram 𝒮 𝒯 f)) ~
      ( ( g) ∘
        ( map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h) ∘
        ( right-map-cocone-span-diagram 𝒮 c))
    right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram =
      g ·l right-square-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h

    coherence-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      statement-coherence-htpy-cocone-span-diagram 𝒮
        ( comp-cocone-hom-span-diagram 𝒮 𝒯 f (cocone-map-span-diagram 𝒯 d g))
        ( cocone-map-span-diagram 𝒮 c
          ( g ∘ map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h))
        ( left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram)
        ( right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram)
    coherence-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram =
      {!!}

    htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      htpy-cocone-span-diagram 𝒮
        ( comp-cocone-hom-span-diagram 𝒮 𝒯 f (cocone-map-span-diagram 𝒯 d g))
        ( cocone-map-span-diagram 𝒮 c
          ( g ∘ map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h))
    pr1 htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram =
      left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram
    pr1 (pr2 htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram) =
      right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram
    pr2 (pr2 htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram) =
      coherence-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram

  coherence-square-cocone-map-hom-cocone-hom-span-diagram :
    coherence-square-maps
      ( precomp (map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h) Z)
      ( cocone-map-span-diagram 𝒯 d)
      ( cocone-map-span-diagram 𝒮 c)
      ( comp-cocone-hom-span-diagram 𝒮 𝒯 f)
  coherence-square-cocone-map-hom-cocone-hom-span-diagram g =
    eq-htpy-cocone-span-diagram 𝒮
      ( comp-cocone-hom-span-diagram 𝒮 𝒯 f (cocone-map-span-diagram 𝒯 d g))
      ( cocone-map-span-diagram 𝒮 c
        ( g ∘ map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d f h))
      ( htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram g)
```
