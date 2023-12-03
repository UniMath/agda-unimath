# Commuting prisms of maps

```agda
module foundation-core.commuting-prisms-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Consider an arrangment of maps composable into a diagram as follows:

```text
         hA
   A ---------> A'
   |\           |\
   | \ h   ⇗    | \ h'
   |  \      f' |  \
   |   V        |   V
 f | ⇐ B ------ | -> B'
   |   /   hB   | ⇐ /
   |  / g       |  / g'
   | /     ⇗    | /
   VV           VV
   C ---------> C' ,
         hC
```

and [homotopies](foundation-core.homotopies.md) filling its faces. Then a
{{#concept "horizontal commuting prism of maps" Agda=horizontal-coherence-prism-maps}}
is a homotopy filling the shape. In other words, we may choose two homotopies
from the composition `hC ∘ g ∘ h` to `f' ∘ hA`, namely 1) following the left
[triangle](foundation-core.commuting-triangles-of-maps.md) and then the front
[square](foundation-core.commuting-squares-of-maps.md), or 2) the two back
squares and then the right triangle; the prism is then a homotopy between these
two homotopies. In this way, a commuting prism may be viewed as a homotopy
between a pasting of squares and their composite --- that is the motivation for
having the triangles go the unconventional way, from the composition to the
composite.

We may also arrange the maps into a more vertical shape, like so:

```text
          B
      h  ^| \  g
       /  |   \
     /  f | ⇑   V
    A ---------> C
    |     | hB   |
    | ⇗   V   ⇗  |
 hA |     B'     | hC
    | h' ^  \ g' |
    |  /  ⇑   \  |
    V/          VV
    A' --------> C' .
          f'
```

Then, given homotopies for the faces, we call a homotopy filling this shape a
{{#concept "vertical commuting prism of maps" Agda=vertical-coherence-prism-maps Agda=vertical-coherence-prism-maps'}}.
This rotation of a prism may be viewed as a homotopy between two triangles with
different but related sides.

It remains to be formalized that the type of vertical prisms is equivalent to
the type of horizontal prisms.

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
one natural formulations for where to draw the "seems" for the filler. Here, we
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
