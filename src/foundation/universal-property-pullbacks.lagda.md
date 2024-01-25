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
open import foundation.functoriality-cartesian-product-types
open import foundation.pullbacks
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.postcomposition-functions
```

</details>

## Idea

The {{#concept "universal property of pullbacks" Disambiguation="types"}}
describes the optimal way to complete a diagram of the form

```text
         B
         |
         |
         V
A -----> X
```

to a square

```text
C -----> B
| ⌟      |
|        |
V        V
A -----> X
```

## Properties

### The homotopy of cones obtained from the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where

  htpy-cone-map-universal-property-pullback :
    (c : cone f g C) (up : universal-property-pullback f g c) →
    {l5 : Level} {C' : UU l5} (c' : cone f g C') →
    htpy-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
  htpy-cone-map-universal-property-pullback c up c' =
    htpy-eq-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
      ( compute-map-universal-property-pullback f g c up c')
```

### Unique uniqueness of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} {C' : UU l5}
  where

  abstract
    uniquely-unique-pullback :
      ( c' : cone f g C') (c : cone f g C) →
      ( up-c' : universal-property-pullback f g c') →
      ( up-c : universal-property-pullback f g c) →
      is-contr
        ( Σ (C' ≃ C) (λ e → htpy-cone f g (cone-map f g c (map-equiv e)) c'))
    uniquely-unique-pullback c' c up-c' up-c =
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
  v          v          v
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
    up-pullback-rectangle-up-pullback-left-square :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      universal-property-pullback j h c →
      universal-property-pullback i (vertical-map-cone j h c) d →
      universal-property-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d)
    up-pullback-rectangle-up-pullback-left-square c d up-pb-c up-pb-d =
      universal-property-pullback-is-pullback (j ∘ i) h
        ( pasting-horizontal-cone i j h c d)
        ( is-pullback-rectangle-is-pullback-left-square i j h c d
          ( is-pullback-universal-property-pullback j h c up-pb-c)
          ( is-pullback-universal-property-pullback i
            ( vertical-map-cone j h c) d up-pb-d))

  abstract
    up-pullback-left-square-up-pullback-rectangle :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      universal-property-pullback j h c →
      universal-property-pullback (j ∘ i) h
        ( pasting-horizontal-cone i j h c d) →
      universal-property-pullback i (vertical-map-cone j h c) d
    up-pullback-left-square-up-pullback-rectangle c d up-pb-c up-pb-rect =
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
  v          v
  ∙ -------> ∙
  | ⌟        |
  |          |
  v          v
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
    up-pullback-top-up-pullback-rectangle :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      universal-property-pullback f g c →
      universal-property-pullback f (g ∘ h) (pasting-vertical-cone f g h c d) →
      universal-property-pullback (horizontal-map-cone f g c) h d
    up-pullback-top-up-pullback-rectangle c d up-pb-c up-pb-dc =
      universal-property-pullback-is-pullback
        ( horizontal-map-cone f g c)
        ( h)
        ( d)
        ( is-pullback-top-is-pullback-rectangle f g h c d
          ( is-pullback-universal-property-pullback f g c up-pb-c)
          ( is-pullback-universal-property-pullback f (g ∘ h)
            ( pasting-vertical-cone f g h c d)
            ( up-pb-dc)))

  abstract
    up-pullback-rectangle-up-pullback-top :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      universal-property-pullback f g c →
      universal-property-pullback (horizontal-map-cone f g c) h d →
      universal-property-pullback f (g ∘ h) (pasting-vertical-cone f g h c d)
    up-pullback-rectangle-up-pullback-top c d up-pb-c up-pb-d =
      universal-property-pullback-is-pullback
        ( f)
        ( g ∘ h)
        ( pasting-vertical-cone f g h c d)
        ( is-pullback-rectangle-is-pullback-top f g h c d
          ( is-pullback-universal-property-pullback f g c up-pb-c)
          ( is-pullback-universal-property-pullback
            ( horizontal-map-cone f g c)
            ( h)
            ( d)
            ( up-pb-d)))
```

### Pullbacks are closed under dependent products

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  {C : I → UU l5} (c : (i : I) → cone (f i) (g i) (C i))
  where

  up-pullback-Π :
    ((i : I) → universal-property-pullback (f i) (g i) (c i)) →
    universal-property-pullback (map-Π f) (map-Π g) (cone-Π f g c)
  up-pullback-Π H =
    universal-property-pullback-is-pullback
      ( map-Π f)
      ( map-Π g)
      ( cone-Π f g c)
      ( is-pullback-Π f g c
        ( λ i →
          is-pullback-universal-property-pullback (f i) (g i) (c i) (H i)))
```

### Pullbacks are closed under cartesian products

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C')
  where

  up-pullback-prod :
    universal-property-pullback f g c →
    universal-property-pullback f' g' c' →
    universal-property-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c')
  up-pullback-prod H H' =
    universal-property-pullback-is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c')
      ( is-pullback-prod-is-pullback-pair f g f' g' c c'
        ( is-pullback-universal-property-pullback f g c H)
        ( is-pullback-universal-property-pullback f' g' c' H'))
```

### Pullbacks are closed under exponentiation

Given a pullback square

```text
          f'
    C ---------> B
    | ⌟          |
  g'|            | g
    |            |
    v            v
    A ---------> X
          f
```

then the exponentiated square given by postcomposition

```text
                f' ∘ -
      (S → C) ---------> (S → B)
         |                  |
  g' ∘ - |                  | g ∘ -
         |                  |
         v                  v
      (S → A) ---------> (S → X)
                f ∘ -
```

is a pullback square for any type `S`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C)
  where

  up-pullback-postcomp :
    universal-property-pullback f g c →
    universal-property-pullback
      ( postcomp T f)
      ( postcomp T g)
      ( postcomp-cone T f g c)
  up-pullback-postcomp H =
    universal-property-pullback-is-pullback
      ( postcomp T f)
      ( postcomp T g)
      ( postcomp-cone T f g c)
      ( is-pullback-postcomp-is-pullback f g c
        ( is-pullback-universal-property-pullback f g c H)
        ( T))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
