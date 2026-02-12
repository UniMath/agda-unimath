# The universal property of pullbacks

```agda
module foundation.universal-property-pullbacks where

open import foundation-core.universal-property-pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.subtype-identity-principle
open import foundation.commuting-cubes-of-maps
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.homotopies
open import foundation-core.function-types
open import foundation.pullbacks
```

</details>

## Idea

The {{#concept "universal property of pullbacks" Disambiguation="types"}}
describes the optimal way to complete a diagram of the form

```text
           B
           |
           |
           ∨
  A -----> X
```

to a square

```text
  C -----> B
  | ⌟      |
  |        |
  ∨        ∨
  A -----> X.
```

## Properties

### Unique uniqueness of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} {C' : UU l5}
  where

  abstract
    uniquely-unique-universal-property-pullback :
      ( c' : cone f g C') (c : cone f g C) →
      ( up-c' : universal-property-pullback f g c') →
      ( up-c : universal-property-pullback f g c) →
      is-contr
        ( Σ (C' ≃ C) (λ e → htpy-cone f g (cone-map f g c (map-equiv e)) c'))
    uniquely-unique-universal-property-pullback c' c up-c' up-c =
      is-torsorial-Eq-subtype
        ( uniqueness-universal-property-pullback f g c up-c C' c')
        ( is-property-is-equiv)
        ( map-universal-property-pullback f g c up-c c')
        ( htpy-cone-map-universal-property-pullback f g c up-c c')
        ( is-equiv-up-pullback-up-pullback c c'
          ( map-universal-property-pullback f g c up-c c')
          ( htpy-cone-map-universal-property-pullback f g c up-c c')
          up-c up-c')
```

### The horizontal pullback pasting property

Given a diagram

```text
  ∙ -------> ∙ -------> ∙
  |          | ⌟        |
  |          |          |
  ∨          ∨          ∨
  ∙ -------> ∙ -------> ∙
```

where the right-hand square is a pullback, then the left-hand square is a
pullback if and only if the composite square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  abstract
    universal-property-pullback-rectangle-universal-property-pullback-left-square :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      universal-property-pullback j h c →
      universal-property-pullback i (vertical-map-cone j h c) d →
      universal-property-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d)
    universal-property-pullback-rectangle-universal-property-pullback-left-square
      c d up-pb-c up-pb-d =
      universal-property-pullback-is-pullback (j ∘ i) h
        ( pasting-horizontal-cone i j h c d)
        ( is-pullback-rectangle-is-pullback-left-square i j h c d
          ( is-pullback-universal-property-pullback j h c up-pb-c)
          ( is-pullback-universal-property-pullback i
            ( vertical-map-cone j h c) d up-pb-d))

  abstract
    universal-property-pullback-left-square-universal-property-pullback-rectangle :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      universal-property-pullback j h c →
      universal-property-pullback (j ∘ i) h
        ( pasting-horizontal-cone i j h c d) →
      universal-property-pullback i (vertical-map-cone j h c) d
    universal-property-pullback-left-square-universal-property-pullback-rectangle
      c d up-pb-c up-pb-rect =
      universal-property-pullback-is-pullback
        ( i)
        ( vertical-map-cone j h c)
        ( d)
        ( is-pullback-left-square-is-pullback-rectangle i j h c d
          ( is-pullback-universal-property-pullback j h c up-pb-c)
          ( is-pullback-universal-property-pullback (j ∘ i) h
            ( pasting-horizontal-cone i j h c d) up-pb-rect))
```

### The vertical pullback pasting property

Given a diagram

```text
  ∙ -------> ∙
  |          |
  |          |
  ∨          ∨
  ∙ -------> ∙
  | ⌟        |
  |          |
  ∨          ∨
  ∙ -------> ∙
```

where the bottom square is a pullback, then the top square is a pullback if and
only if the composite square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  abstract
    universal-property-pullback-top-universal-property-pullback-rectangle :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      universal-property-pullback f g c →
      universal-property-pullback f (g ∘ h) (pasting-vertical-cone f g h c d) →
      universal-property-pullback (horizontal-map-cone f g c) h d
    universal-property-pullback-top-universal-property-pullback-rectangle
      c d up-pb-c up-pb-dc =
      universal-property-pullback-is-pullback
        ( horizontal-map-cone f g c)
        ( h)
        ( d)
        ( is-pullback-top-square-is-pullback-rectangle f g h c d
          ( is-pullback-universal-property-pullback f g c up-pb-c)
          ( is-pullback-universal-property-pullback f (g ∘ h)
            ( pasting-vertical-cone f g h c d)
            ( up-pb-dc)))

  abstract
    universal-property-pullback-rectangle-universal-property-pullback-top :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      universal-property-pullback f g c →
      universal-property-pullback (horizontal-map-cone f g c) h d →
      universal-property-pullback f (g ∘ h) (pasting-vertical-cone f g h c d)
    universal-property-pullback-rectangle-universal-property-pullback-top
      c d up-pb-c up-pb-d =
      universal-property-pullback-is-pullback
        ( f)
        ( g ∘ h)
        ( pasting-vertical-cone f g h c d)
        ( is-pullback-rectangle-is-pullback-top-square f g h c d
          ( is-pullback-universal-property-pullback f g c up-pb-c)
          ( is-pullback-universal-property-pullback
            ( horizontal-map-cone f g c)
            ( h)
            ( d)
            ( up-pb-d)))
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pullback if and only if the top square is a pullback

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' ≃ A) (hB : B' ≃ B) (hC : C' ≃ C) (hD : D' ≃ D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ map-equiv hA ~ map-equiv hB ∘ f')
  (back-right : g ∘ map-equiv hA ~ map-equiv hC ∘ g')
  (front-left : h ∘ map-equiv hB ~ map-equiv hD ∘ h')
  (front-right : k ∘ map-equiv hC ~ map-equiv hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k'
      ( map-equiv hA) (map-equiv hB) (map-equiv hC) (map-equiv hD)
      top back-left back-right front-left front-right bottom)
  where abstract

  universal-property-pullback-bottom-universal-property-pullback-top-cube-equiv :
    universal-property-pullback h' k' (f' , g' , top) →
    universal-property-pullback h k (f , g , bottom)
  universal-property-pullback-bottom-universal-property-pullback-top-cube-equiv
    up-top =
    universal-property-pullback-is-pullback h k (f , g , bottom)
      ( is-pullback-bottom-is-pullback-top-cube-equiv
        f g h k f' g' h' k' hA hB hC hD
        ( top)
        ( back-left)
        ( back-right)
        ( front-left)
        ( front-right)
        ( bottom)
        ( c)
        ( is-pullback-universal-property-pullback  h' k'
          ( f' , g' , top)
          ( up-top)))

  universal-property-pullback-top-universal-property-pullback-bottom-cube-equiv :
    universal-property-pullback h k (f , g , bottom) →
    universal-property-pullback h' k' (f' , g' , top)
  universal-property-pullback-top-universal-property-pullback-bottom-cube-equiv
    up-bottom =
    universal-property-pullback-is-pullback h' k' (f' , g' , top)
      ( is-pullback-top-is-pullback-bottom-cube-equiv
        f g h k f' g' h' k' hA hB hC hD
        ( top)
        ( back-left)
        ( back-right)
        ( front-left)
        ( front-right)
        ( bottom)
        ( c)
        ( is-pullback-universal-property-pullback h k
          ( f , g , bottom)
          ( up-bottom)))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
