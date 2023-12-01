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
  { l1 l2 l3 l1' l2' l3' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( hA : A → A') (h : A → B) (h' : A' → B')
  ( hB : B → B') (g : B → C) (g' : B' → C')
  ( hC : C → C') (f : A → C) (f' : A' → C')
  ( left : coherence-triangle-maps' f g h)
  ( sq-top : coherence-square-maps hA h h' hB)
  ( sq-bottom : coherence-square-maps hB g g' hC)
  ( sq-front : coherence-square-maps hA f f' hC)
  ( right : coherence-triangle-maps' f' g' h')
  where

  horizontal-coherence-prism-maps : UU (l1 ⊔ l3')
  horizontal-coherence-prism-maps =
    ( ( hC ·l left) ∙h sq-front) ~
    ( ( pasting-vertical-coherence-square-maps hA h h' hB g g' hC
        ( sq-top)
        ( sq-bottom)) ∙h
      ( right ·r hA))
```

### Vertical commuting prisms of maps

Because triangular prisms are less symmetric than, say, cubes, we have more than
one natural formulations for where to draw the "seems" for the filler. We
present two choices, and show that they are equivalent in
[`foundation.commuting-prisms-of-maps`](foundation.commuting-prisms-of-maps.md).

```agda
module _
  { l1 l2 l3 l1' l2' l3' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  where

  module _
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

  module _
    ( top : coherence-triangle-maps f g h)
    ( inv-front : coherence-square-maps hA f f' hC)
    ( inv-right : coherence-square-maps hB g g' hC)
    ( left : coherence-square-maps h hA hB h')
    ( bottom : coherence-triangle-maps f' g' h')
    where

    vertical-coherence-prism-maps' : UU (l1 ⊔ l3')
    vertical-coherence-prism-maps' =
      ( inv-front ∙h ((bottom ·r hA) ∙h (g' ·l left))) ~
      ( (hC ·l top) ∙h (inv-right ·r h))
```
