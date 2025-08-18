# Commuting prisms of maps

```agda
module foundation-core.commuting-prisms-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-pentagons-of-identifications
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
```

</details>

## Idea

Consider an arrangement of maps composable into a diagram as follows:

```text
          hA
    A ---------> A'
    |\           |\
    | \ h   ⇗    | \ h'
    |  \      f' |  \
    |   ∨        |   ∨
  f | ⇐ B ------ | -> B'
    |   /   hB   | ⇐ /
    |  / g       |  / g'
    | /     ⇗    | /
    ∨∨           ∨∨
    C ---------> C' ,
          hC
```

and [homotopies](foundation-core.homotopies.md) filling its faces. Then a
{{#concept "horizontal commuting prism of maps" Agda=horizontal-coherence-prism-maps}}
is a homotopy filling the shape. In other words, we may choose two homotopies
from the composition `hC ∘ g ∘ h` to `f' ∘ hA`, namely following 1) the left
[triangle](foundation-core.commuting-triangles-of-maps.md) and then the front
[square](foundation-core.commuting-squares-of-maps.md), or 2) the two back
squares and then the right triangle; the prism is then a homotopy between these
two homotopies. In this way, a commuting prism may be viewed as a homotopy
between a pasting of squares and their composite — that is the motivation for
having the triangles go the unconventional way, from the composition to the
composite.

We may also arrange the maps into a more vertical shape, like so:

```text
          B
      h  ∧| \  g
       /  |   \
     /  f | ⇑   ∨
    A ---------> C
    |     | hB   |
    | ⇗   ∨   ⇗  |
 hA |     B'     | hC
    | h' ∧  \ g' |
    |  /  ⇑   \  |
    ∨/          ∨∨
    A' --------> C' .
          f'
```

Then, given homotopies for the faces, we call a homotopy filling this shape a
{{#concept "vertical commuting prism of maps" Agda=vertical-coherence-prism-maps Agda=vertical-coherence-prism-maps'}}.
This rotation of a prism may be viewed as a homotopy between two triangles with
different but related sides.

It remains to be formalized that the type of vertical prisms is
[equivalent](foundation-core.equivalences.md) to the type of horizontal prisms.

## Definitions

### Horizontal commuting prisms of maps

```agda
module _
  { l1 l2 l3 l1' l2' l3' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
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
one natural formulation for where to draw the "seams" for the filler. Here, we
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
    ( inv-front : coherence-square-maps' f hA hC f')
    ( inv-right : coherence-square-maps' g hB hC g')
    ( left : coherence-square-maps h hA hB h')
    ( bottom : coherence-triangle-maps f' g' h')
    where

    vertical-coherence-prism-maps' : UU (l1 ⊔ l3')
    vertical-coherence-prism-maps' =
      ( inv-front ∙h ((bottom ·r hA) ∙h (g' ·l left))) ~
      ( (hC ·l top) ∙h (inv-right ·r h))

  module _
    ( top : coherence-triangle-maps f g h)
    ( inv-front : coherence-square-maps' f hA hC f')
    ( inv-right : coherence-square-maps' g hB hC g')
    ( inv-left : coherence-square-maps' h hA hB h')
    ( bottom : coherence-triangle-maps f' g' h')
    where

    vertical-coherence-prism-inv-squares-maps : UU (l1 ⊔ l3')
    vertical-coherence-prism-inv-squares-maps =
      ( inv-front ∙h (bottom ·r hA)) ~
      ( (hC ·l top) ∙h ((inv-right ·r h) ∙h (g' ·l inv-left)))

  module _
    ( inv-top : coherence-triangle-maps' f g h)
    ( front : coherence-square-maps f hA hC f')
    ( right : coherence-square-maps g hB hC g')
    ( left : coherence-square-maps h hA hB h')
    ( inv-bottom : coherence-triangle-maps' f' g' h')
    where

    vertical-coherence-prism-inv-triangles-maps : UU (l1 ⊔ l3')
    vertical-coherence-prism-inv-triangles-maps =
      ( (g' ·l left) ∙h (right ·r h) ∙h (hC ·l inv-top)) ~
      ( (inv-bottom ·r hA) ∙h front)

  module _
    ( inv-top : coherence-triangle-maps' f g h)
    ( inv-front : coherence-square-maps' f hA hC f')
    ( inv-right : coherence-square-maps' g hB hC g')
    ( inv-left : coherence-square-maps' h hA hB h')
    ( inv-bottom : coherence-triangle-maps' f' g' h')
    where

    vertical-coherence-prism-inv-boundary-maps : UU (l1 ⊔ l3')
    vertical-coherence-prism-inv-boundary-maps =
      ( (inv-right ·r h) ∙h (g' ·l inv-left) ∙h (inv-bottom ·r hA)) ~
      ( (hC ·l inv-top) ∙h inv-front)
```

## Translations between coherences of prisms of maps

Our different formulations of commuting prisms of maps are of course all
equivalent, although this remains to be formalized. Below, we record various
translations between them.

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
    ( inv-front : coherence-square-maps' f hA hC f')
    ( inv-right : coherence-square-maps' g hB hC g')
    ( inv-left : coherence-square-maps' h hA hB h')
    ( bottom : coherence-triangle-maps f' g' h')
    where

    vertical-coherence-prism-maps-vertical-coherence-prism-inv-squares-maps :
      vertical-coherence-prism-inv-squares-maps f g h f' g' h' hA hB hC
        ( top)
        ( inv-front)
        ( inv-right)
        ( inv-left)
        ( bottom) →
      vertical-coherence-prism-maps f g h f' g' h' hA hB hC
        ( top)
        ( inv-htpy inv-front)
        ( inv-htpy inv-right)
        ( inv-htpy inv-left)
        ( bottom)
    vertical-coherence-prism-maps-vertical-coherence-prism-inv-squares-maps H =
      ( ap-concat-htpy
        ( bottom ·r hA)
        ( ( ap-concat-htpy'
            ( inv-htpy inv-right ·r h)
            ( left-whisker-inv-htpy g' inv-left)) ∙h
          ( inv-htpy-distributive-inv-concat-htpy
            ( inv-right ·r h)
            ( g' ·l inv-left)))) ∙h
      ( inv-htpy-right-transpose-htpy-concat
        ( inv-htpy inv-front ∙h (hC ·l top))
        ( inv-right ·r h ∙h (g' ·l inv-left))
        ( bottom ·r hA)
        ( ( assoc-htpy
            ( inv-htpy inv-front)
            ( hC ·l top)
            ( inv-right ·r h ∙h (g' ·l inv-left))) ∙h
          ( inv-htpy-left-transpose-htpy-concat
            ( inv-front)
            ( bottom ·r hA)
            ( (hC ·l top) ∙h (inv-right ·r h ∙h (g' ·l inv-left)))
            ( H))))

  module _
    ( top : coherence-triangle-maps f g h)
    ( inv-front : coherence-square-maps f hA hC f')
    ( inv-right : coherence-square-maps g hB hC g')
    ( inv-left : coherence-square-maps h hA hB h')
    ( bottom : coherence-triangle-maps f' g' h')
    where

    vertical-coherence-prism-inv-squares-maps-vertical-coherence-prism-maps :
      vertical-coherence-prism-maps f g h f' g' h' hA hB hC
        ( top)
        ( inv-front)
        ( inv-right)
        ( inv-left)
        ( bottom) →
      vertical-coherence-prism-inv-squares-maps f g h f' g' h' hA hB hC
        ( top)
        ( inv-htpy inv-front)
        ( inv-htpy inv-right)
        ( inv-htpy inv-left)
        ( bottom)
    vertical-coherence-prism-inv-squares-maps-vertical-coherence-prism-maps
      H a =
      ( reflect-top-left-coherence-pentagon-identifications
        ( bottom (hA a))
        ( inv-front a)
        ( ap g' (inv-left a))
        ( ap hC (top a))
        ( inv-right (h a))
        ( inv
          ( ( assoc (bottom (hA a)) (ap g' (inv-left a)) (inv-right (h a))) ∙
            ( H a)))) ∙
      ( left-whisker-concat
        ( ap hC (top a) ∙ inv (inv-right (h a)))
        ( inv (ap-inv g' (inv-left a)))) ∙
      ( assoc
        ( ap hC (top a))
        ( inv (inv-right (h a)))
        ( ap g' (inv (inv-left a))))

  module _
    ( inv-top : coherence-triangle-maps' f g h)
    ( inv-front : coherence-square-maps' f hA hC f')
    ( inv-right : coherence-square-maps' g hB hC g')
    ( inv-left : coherence-square-maps' h hA hB h')
    ( inv-bottom : coherence-triangle-maps' f' g' h')
    where

    vertical-coherence-prism-inv-triangles-maps-vertical-coherence-prism-inv-boundary-maps :
      vertical-coherence-prism-inv-boundary-maps f g h f' g' h' hA hB hC
        ( inv-top)
        ( inv-front)
        ( inv-right)
        ( inv-left)
        ( inv-bottom) →
      vertical-coherence-prism-inv-triangles-maps f g h f' g' h' hA hB hC
        ( inv-top)
        ( inv-htpy inv-front)
        ( inv-htpy inv-right)
        ( inv-htpy inv-left)
        ( inv-bottom)
    vertical-coherence-prism-inv-triangles-maps-vertical-coherence-prism-inv-boundary-maps
      H =
      ( ap-concat-htpy'
        ( hC ·l inv-top)
        ( ( ap-concat-htpy'
            ( inv-htpy inv-right ·r h)
            ( left-whisker-inv-htpy g' inv-left)) ∙h
          ( inv-htpy-distributive-inv-concat-htpy
            ( inv-right ·r h)
            ( g' ·l inv-left)))) ∙h
      ( right-transpose-htpy-concat
        ( ( inv-htpy (inv-right ·r h ∙h (g' ·l inv-left))) ∙h (hC ·l inv-top))
        ( inv-front)
        ( inv-bottom ·r hA)
        ( ( assoc-htpy
            ( inv-htpy (inv-right ·r h ∙h (g' ·l inv-left)))
            ( hC ·l inv-top)
            ( inv-front)) ∙h
          ( inv-htpy-left-transpose-htpy-concat
            ( inv-right ·r h ∙h (g' ·l inv-left))
            ( inv-bottom ·r hA)
            ( (hC ·l inv-top) ∙h inv-front)
            ( H))))
```
