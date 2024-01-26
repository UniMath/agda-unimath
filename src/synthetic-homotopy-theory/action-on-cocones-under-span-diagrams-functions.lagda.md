# The action on cocones under span diagrams of functions

```agda
module
  synthetic-homotopy-theory.action-on-cocones-under-span-diagrams-functions
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences-span-diagrams
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-span-diagrams
open import foundation.precomposition-functions
open import foundation.span-diagrams
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-span-diagrams
open import synthetic-homotopy-theory.morphisms-cocones-under-morphisms-span-diagrams
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
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

where `K := (((k ∘ i') ·l α₃) ∙h ((k ·l H) ·r α₂)) ∙h ((k ∘ j') ·l α₄)`. The
cocone on the right hand side consists of

```text
  S -------------> B
  |                |
  |        K'      | k ∘ h ∘ j
  V                V
  A -------------> Y
      k ∘ h ∘ i
```

where `K' := (k ∘ h) ·l H`. Thus we see that we have to construct a triple
consisting of

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

where `β₀` is the first component of the triple `β` and `β₁` is the second
component of `β`. Then it remains to construct a family of identifications

```text
  ap (k ∘ i')) (α₃ s) ∙ ap k (H' (α₂ s)) ∙ ap (k ∘ j') (α₄ s)⁻¹ ∙ ap k (β₁ (g s))) ＝
  ap k (β₀ (f s)) ∙ ap (k ∘ h) (H s)
```

indexed by `s : S`. Recall that `β₂` witnessing that a cube commutes, i.e., that
`β₂ s` is an identifcation of type

```text
  ap i' (α₃ s)⁻¹ ∙ β₀ (f s) ∙ ap h (H s) ＝
  H' (α₂ s) ∙ (ap j' (α₄ s)⁻¹ ∙ β₁ (g s)).
```

By whiskering the commutativity `β₂` of a cube with the map `k` and inverting,
we obtain identifications of type

```text
ap k (H' (α₂ s)) ∙ (ap (k ∘ j') (α₄ s)⁻¹ ∙ ap k (β₂ (g s))) ＝
ap (k ∘ i') (α₃ s)⁻¹ ∙ ap k (β₁ (f s)) ∙ ap (k ∘ h) (H s)
```

By `ap-inv` we have `ap (k ∘ i') (α₃ s)⁻¹ ＝ (ap (k ∘ i') (α₃ s))⁻¹` on the
right hand side. This can be transposed to the left hand side to obtain an
identification of type

```text
ap (k ∘ i') (α₃ s) ∙ (ap k (H' (α₂ s)) ∙ (ap (k ∘ j') (α₄ s)⁻¹ ∙ ap k (β₂ (g s))))) ＝
ap k (β₁ (f s)) ∙ ap (k ∘ h) (H s)
```

This identification solves our goal up to some applications of associativity.

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
    coherence-htpy-coherence-square-cocone-map-hom-cocone-hom-span-diagram s =
      ( double-assoc
        ( ap
          ( k ∘ left-map-cocone-span-diagram 𝒯 d)
          ( left-square-hom-span-diagram 𝒮 𝒯 α s))
        ( _)
        ( _)
        ( _)) ∙
      ( inv-left-transpose-eq-concat
        ( ap
          ( k ∘ left-map-cocone-span-diagram 𝒯 d)
          ( left-square-hom-span-diagram 𝒮 𝒯 α s))
        ( _)
        ( _)
        ( ( ( ( ( inv
                  ( left-whisker-coherence-cube-maps k
                    ( left-map-span-diagram 𝒯)
                    ( right-map-span-diagram 𝒯)
                    ( left-map-cocone-span-diagram 𝒯 d)
                    ( right-map-cocone-span-diagram 𝒯 d)
                    ( left-map-span-diagram 𝒮)
                    ( right-map-span-diagram 𝒮)
                    ( left-map-cocone-span-diagram 𝒮 c)
                    ( right-map-cocone-span-diagram 𝒮 c)
                    ( spanning-map-hom-span-diagram 𝒮 𝒯 α)
                    ( map-domain-hom-span-diagram 𝒮 𝒯 α)
                    ( map-codomain-hom-span-diagram 𝒮 𝒯 α)
                    ( map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β)
                    ( coherence-square-cocone-span-diagram 𝒮 c)
                    ( inv-htpy (left-square-hom-span-diagram 𝒮 𝒯 α))
                    ( inv-htpy (right-square-hom-span-diagram 𝒮 𝒯 α))
                    ( left-square-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β)
                    ( right-square-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β)
                    ( coherence-square-cocone-span-diagram 𝒯 d)
                    ( cube-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β)
                    ( s))) ∙
                ( assoc
                    ( ap
                      ( k ∘ left-map-cocone-span-diagram 𝒯 d)
                      ( inv
                        ( left-square-hom-span-diagram 𝒮 𝒯 α s)))
                    ( _)
                    ( _)))) ∙
            ( ( ap
                ( λ p →
                  p ∙
                  ( ( ap k
                      ( left-square-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β
                        ( left-map-span-diagram 𝒮 s))) ∙
                    ( ap
                      ( k ∘ map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d α β)
                      ( coherence-square-cocone-span-diagram 𝒮 c s))))
                ( ap-inv
                  ( k ∘ left-map-cocone-span-diagram 𝒯 d)
                  ( left-square-hom-span-diagram 𝒮 𝒯 α s)))))))

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

### For any equivalence of cocones under an equivalence of span diagrams, there is a naturality square involving `cocone-map`

**Lemma.** Consider an equivalence of cocones `(h , β)` under an equivalence
`α : 𝒮 ≃ 𝒯` of span diagrams, where the equivalence between the codomains of the
cocones is `h : X ≃ Y`. Then the square

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

**Proof.** This statement is a direct corollary of the previous statement about
morphisms of cocones under morphisms of span diagrams.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  (𝒮 : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (𝒯 : span-diagram l5 l6 l7) {Y : UU l8} (d : cocone-span-diagram 𝒯 Y)
  (α : equiv-span-diagram 𝒮 𝒯) (β : equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d α)
  {Z : UU l9}
  where

  coherence-square-cocone-map-equiv-cocone-equiv-span-diagram :
    coherence-square-maps
      ( precomp (map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d α β) Z)
      ( cocone-map-span-diagram 𝒯 d)
      ( cocone-map-span-diagram 𝒮 c)
      ( comp-cocone-equiv-span-diagram 𝒮 𝒯 α)
  coherence-square-cocone-map-equiv-cocone-equiv-span-diagram =
    coherence-square-cocone-map-hom-cocone-hom-span-diagram 𝒮 c 𝒯 d
      ( hom-equiv-span-diagram 𝒮 𝒯 α)
      ( hom-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d α β)
```
