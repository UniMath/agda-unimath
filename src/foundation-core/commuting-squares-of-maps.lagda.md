# Commuting squares of maps

```agda
module foundation-core.commuting-squares-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A square of maps

```text
  A ------> X
  |         |
  |         |
  |         |
  V         V
  B ------> Y
```

is said to commute if there is a homotopy between both composites.

## Definitions

```agda
coherence-square-maps :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (top : C → B) (left : C → A) (right : B → X) (bottom : A → X) →
  UU (l3 ⊔ l4)
coherence-square-maps top left right bottom =
  (bottom ∘ left) ~ (right ∘ top)
```

## Properties

### Pasting commuting squares horizontally

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top-left : A → B) (top-right : B → C)
  (left : A → X) (mid : B → Y) (right : C → Z)
  (bottom-left : X → Y) (bottom-right : Y → Z)
  where

  pasting-horizontal-coherence-square-maps :
    coherence-square-maps top-left left mid bottom-left →
    coherence-square-maps top-right mid right bottom-right →
    coherence-square-maps
      (top-right ∘ top-left) left right (bottom-right ∘ bottom-left)
  pasting-horizontal-coherence-square-maps sq-left sq-right =
    (bottom-right ·l sq-left) ∙h (sq-right ·r top-left)

  pasting-horizontal-up-to-htpy-coherence-square-maps :
    {top : A → C} (H : coherence-triangle-maps top top-right top-left)
    {bottom : X → Z}
    (K : coherence-triangle-maps bottom bottom-right bottom-left) →
    coherence-square-maps top-left left mid bottom-left →
    coherence-square-maps top-right mid right bottom-right →
    coherence-square-maps top left right bottom
  pasting-horizontal-up-to-htpy-coherence-square-maps H K sq-left sq-right =
    ( ( K ·r left) ∙h
      ( pasting-horizontal-coherence-square-maps sq-left sq-right)) ∙h
    ( inv-htpy (right ·l H))
```

### Pasting commuting squares vertically

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top : A → X)
  (left-top : A → B) (right-top : X → Y)
  (mid : B → Y)
  (left-bottom : B → C) (right-bottom : Y → Z)
  (bottom : C → Z)
  where

  pasting-vertical-coherence-square-maps :
    coherence-square-maps top left-top right-top mid →
    coherence-square-maps mid left-bottom right-bottom bottom →
    coherence-square-maps
      top (left-bottom ∘ left-top) (right-bottom ∘ right-top) bottom
  pasting-vertical-coherence-square-maps sq-top sq-bottom =
    (sq-bottom ·r left-top) ∙h (right-bottom ·l sq-top)

  pasting-vertical-up-to-htpy-coherence-square-maps :
    {left : A → C} (H : coherence-triangle-maps left left-bottom left-top)
    {right : X → Z} (K : coherence-triangle-maps right right-bottom right-top) →
    coherence-square-maps top left-top right-top mid →
    coherence-square-maps mid left-bottom right-bottom bottom →
    coherence-square-maps top left right bottom
  pasting-vertical-up-to-htpy-coherence-square-maps H K sq-top sq-bottom =
    ( ( bottom ·l H) ∙h
      ( pasting-vertical-coherence-square-maps sq-top sq-bottom)) ∙h
    ( inv-htpy (K ·r top))
```
