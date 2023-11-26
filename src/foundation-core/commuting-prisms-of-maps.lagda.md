# Commuting prisms of maps

```agda
module foundation-core.commuting-prisms-of-maps where
```

```agda
open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies

open import foundation.universe-levels
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( top : A → X) (left-front : A → C) (left-back : A → B)
  ( right-front : X → Z) (right-back : X → Y)
  ( back-bottom : B → Y) (left-bottom : B → C) (right-bottom : Y → Z)
  ( front-bottom : C → Z)
  ( back : coherence-square-maps top left-back right-back back-bottom)
  ( left : coherence-triangle-maps' left-front left-bottom left-back)
  ( right : coherence-triangle-maps' right-front right-bottom right-back)
  ( front : coherence-square-maps top left-front right-front front-bottom)
  ( bottom :
    coherence-square-maps back-bottom left-bottom right-bottom front-bottom)
  where

  horizontal-coherence-prism-maps : UU (l1 ⊔ l6)
  horizontal-coherence-prism-maps =
    ( ( front-bottom ·l left) ∙h front) ~
    ( ( pasting-vertical-coherence-square-maps
        ( top)
        ( left-back)
        ( right-back)
        ( back-bottom)
        ( left-bottom)
        ( right-bottom)
        ( front-bottom)
        ( back)
        ( bottom)) ∙h
      ( right ·r top))
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( top-left : A → B) (top-right : B → C) (top-front : A → C)
  ( front-left : A → X) (back : B → Y) (front-right : C → Z)
  ( bottom-left : X → Y) (bottom-right : Y → Z) (bottom-front : X → Z)
  ( top : coherence-triangle-maps top-front top-right top-left)
  ( left : coherence-square-maps top-left front-left back bottom-left)
  ( right : coherence-square-maps top-right back front-right bottom-right)
  ( front : coherence-square-maps top-front front-left front-right bottom-front)
  ( bottom : coherence-triangle-maps bottom-front bottom-right bottom-left)
  where

  vertical-coherence-prism-maps : UU (l1 ⊔ l6)
  vertical-coherence-prism-maps =
    ( ( bottom ·r front-left) ∙h
      ( pasting-horizontal-coherence-square-maps
        ( top-left)
        ( top-right)
        ( front-left)
        ( back)
        ( front-right)
        ( bottom-left)
        ( bottom-right)
        ( left)
        ( right))) ~
    ( front ∙h (front-right ·l top))
```
