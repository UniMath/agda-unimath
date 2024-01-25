# Morphisms of cocones under morphisms of span diagrams

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module
  synthetic-homotopy-theory.morphisms-cocones-under-morphisms-span-diagrams
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-span-diagrams
open import foundation.precomposition-functions
open import foundation.span-diagrams
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.action-on-cocones-under-span-diagrams-functions
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

**Lemma.** Consider a morphism of cocones `(h , β)` under a morphism `α : 𝒮 → 𝒯`
of span diagrams, where the map between the codomains of the cocones is
`h : X → Y`. Then the square

```text
                                - ∘ h
          (Y → Z) ---------------------------------------> (X → Z)
             |                                                |
  cocone-map |                                                | cocone-map
             V                                                V
        cocone 𝒯 Z ------------------------------------> cocone 𝒮 Z
                    comp-cocone-hom-span-diagram 𝒮 𝒯 α
```

commutes.

**Proof.** Consider a map `k : Y → Z`. Then we have to construct a homotopy of
cocones under span diagrams

```text
  cocone-map 𝒯 d k ∘ α ~ cocone-map 𝒮 c (k ∘ h)
```

from the composite of the cocone `cocone-map 𝒯 d k` and the morphism of span
diagrams `α` to the cocone `cocone-map 𝒮 c (k ∘ h)`. The cocone on the left hand
side consists of

```text
  S -------------> B
  |                |
  |       K        | k ∘ j' ∘ α₁
  V                V
  A -------------> Y,
     k ∘ i' ∘ α₀
```

where `K := (((k ∘ i') ·l α₃) ∙h ((k ·l H) ·r α₂)) ∙h ((k ∘ j') ·l α₄)`. The cocone on the right hand side consists of

```text
  S -------------> B
  |                |
  |        K'      | k ∘ h ∘ j
  V                V
  A -------------> Y
      k ∘ h ∘ i
```

where `K' := (k ∘ h) ·l H`. Thus we see that we have to construct a triple consisting of

```text
  γ : k ∘ i' ∘ α₀ ~ k ∘ h ∘ i
  δ : k ∘ j' ∘ α₁ ~ k ∘ h ∘ j
```

and a homotopy `ε` witnessing that the square of homotopies

```text
                   γ ·r f
  k ∘ i' ∘ α₀ ∘ f --------> k ∘ h ∘ i ∘ f
         |                       |
       K |           ε           | K'
         V                       V
  k ∘ j' ∘ α₁ ∘ g --------> k ∘ h ∘ j ∘ g
                   δ ·r g
```

commutes.

We define the homotopies

```text
  γ := k ·l β₀
  δ := k ·l β₁,
```

where `β₀` is the first component of the triple `β` and `β₁` is the second component of `β`. Then it remains to construct a homotopy

```text
  ((((k ∘ i') ·l α₃) ∙h ((k ·l H) ·r α₂)) ∙h ((k ∘ j') ·l α₄)) ∙h ((k ·l β₁) ·r g) ~
  ((k ·l β₀) ·r f) ∙h ((k ∘ h) ·l H).
```

{-
goal:
  ap (k ∘ i')) (α₃ s) ∙
  ap k (H' (α₂ s)) ∙
  ap (k ∘ j') (inv (α₄ s)) ∙
  ap k (β₂ (g s))) ＝
  ap k (β₁ (f s)) ∙
  ap (k ∘ β₀) (H s)

β₂ s :
  ap i' (inv (α₃ s)) ∙
  β₁ (f s) ∙
  ap β₀ (H s) ＝
  H' (α₂ s) ∙
  ( ap j' (inv (α₄ s)) ∙
    β₂ (g s))
 -}

Recall that the homotopy `β₃` is a family of identifications of type

```text
  ( ( ( ap h (inv (α₃ a'))) ∙
      ( L (f' a'))) ∙
    ( ap hD (coherence-square-cocone-span-diagram 𝒮 c a'))) ＝
  ( ( coherence-square-cocone-span-diagram 𝒯 d (hA a')) ∙
    ( ( ap k (inv-htpy (right-square-hom-span-diagram 𝒮 𝒯 f) a')) ∙
      ( R (g' a'))))

```

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  (𝒮 : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (𝒯 : span-diagram l5 l6 l7) {Y : UU l8} (d : cocone-span-diagram 𝒯 Y)
  (α : hom-span-diagram 𝒮 𝒯) (β : hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α)
  {Z : UU l9}
  where

  module _
    (k : Y → Z)
    where

    left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      ( ( k) ∘
        ( left-map-cocone-span-diagram 𝒯 d) ∘
        ( map-domain-hom-span-diagram 𝒮 𝒯 α)) ~
      ( ( k) ∘
        ( map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β) ∘
        ( left-map-cocone-span-diagram 𝒮 c))
    left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram =
      k ·l left-square-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β

    right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      ( ( k) ∘
        ( right-map-cocone-span-diagram 𝒯 d) ∘
        ( map-codomain-hom-span-diagram 𝒮 𝒯 α)) ~
      ( ( k) ∘
        ( map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β) ∘
        ( right-map-cocone-span-diagram 𝒮 c))
    right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram =
      k ·l right-square-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β

    coherence-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      statement-coherence-htpy-cocone-span-diagram 𝒮
        ( comp-cocone-hom-span-diagram 𝒮 𝒯 α (cocone-map-span-diagram 𝒯 d k))
        ( cocone-map-span-diagram 𝒮 c
          ( k ∘ map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β))
        ( left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram)
        ( right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram)
    coherence-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram x =
      {!!}

-- cube-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β
 
    htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram :
      htpy-cocone-span-diagram 𝒮
        ( comp-cocone-hom-span-diagram 𝒮 𝒯 α (cocone-map-span-diagram 𝒯 d k))
        ( cocone-map-span-diagram 𝒮 c
          ( k ∘ map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β))
    pr1 htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram =
      left-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram
    pr1 (pr2 htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram) =
      right-square-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram
    pr2 (pr2 htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram) =
      coherence-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram

  coherence-square-cocone-map-hom-cocone-hom-span-diagram :
    coherence-square-maps
      ( precomp (map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β) Z)
      ( cocone-map-span-diagram 𝒯 d)
      ( cocone-map-span-diagram 𝒮 c)
      ( comp-cocone-hom-span-diagram 𝒮 𝒯 α)
  coherence-square-cocone-map-hom-cocone-hom-span-diagram k =
    eq-htpy-cocone-span-diagram 𝒮
      ( comp-cocone-hom-span-diagram 𝒮 𝒯 α (cocone-map-span-diagram 𝒯 d k))
      ( cocone-map-span-diagram 𝒮 c
        ( k ∘ map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β))
      ( htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram k)
```
