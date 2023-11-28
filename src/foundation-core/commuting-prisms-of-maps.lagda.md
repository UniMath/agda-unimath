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

## Definitions

### Horizontal commuting prisms of maps

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

### Vertical commuting prisms of maps

```agda
module _
  { l1 l2 l3 l1' l2' l3' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  ( top : coherence-triangle-maps f g h)
  ( front : coherence-square-maps f hA hC f')
  ( right : coherence-square-maps g hB hC g')
  ( left : coherence-square-maps h hA hB h')
  ( bottom : coherence-triangle-maps f' g' h')
  where

  vertical-coherence-prism-maps : UU (l1 ⊔ l3')
  vertical-coherence-prism-maps =
    ( ( bottom ·r hA) ∙h
      ( pasting-horizontal-coherence-square-maps h g hA hB hC h' g'
        ( left)
        ( right))) ~
    ( front ∙h (hC ·l top))
```
