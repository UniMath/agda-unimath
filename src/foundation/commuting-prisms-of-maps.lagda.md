# Commuting prisms of maps

```agda
module foundation.commuting-prisms-of-maps where
```

```agda
open import foundation-core.commuting-squares-of-maps

open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.homotopies
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.whiskering-homotopies
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

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  { M : UU l7} {N : UU l8} {O : UU l9}
  ( top-left : A → B) (top-right : B → C) (top-front : A → C)
  ( front-left-top : A → X) (back-top : B → Y) (front-right-top : C → Z)
  ( mid-left : X → Y) (mid-right : Y → Z) (mid-front : X → Z)
  ( front-left-bottom : X → M) (back-bottom : Y → N)
  ( front-right-bottom : Z → O)
  ( bottom-left : M → N) (bottom-right : N → O) (bottom-front : M → O)
  ( top : coherence-triangle-maps top-front top-right top-left)
  ( left-top : coherence-square-maps top-left front-left-top back-top mid-left)
  ( right-top :
      coherence-square-maps top-right back-top front-right-top mid-right)
  ( front-top :
      coherence-square-maps top-front front-left-top front-right-top mid-front)
  ( mid : coherence-triangle-maps mid-front mid-right mid-left)
  ( left-bottom :
      coherence-square-maps mid-left front-left-bottom back-bottom bottom-left)
  ( right-bottom :
      coherence-square-maps
        ( mid-right)
        ( back-bottom)
        ( front-right-bottom)
        ( bottom-right))
  ( front-bottom :
      coherence-square-maps
        ( mid-front)
        ( front-left-bottom)
        ( front-right-bottom)
        ( bottom-front))
  ( bottom : coherence-triangle-maps bottom-front bottom-right bottom-left)
  where

  pasting-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps
      ( top-left)
      ( top-right)
      ( top-front)
      ( front-left-top)
      ( back-top)
      ( front-right-top)
      ( mid-left)
      ( mid-right)
      ( mid-front)
      ( top)
      ( left-top)
      ( right-top)
      ( front-top)
      ( mid) →
    vertical-coherence-prism-maps
      ( mid-left)
      ( mid-right)
      ( mid-front)
      ( front-left-bottom)
      ( back-bottom)
      ( front-right-bottom)
      ( bottom-left)
      ( bottom-right)
      ( bottom-front)
      ( mid)
      ( left-bottom)
      ( right-bottom)
      ( front-bottom)
      ( bottom) →
    vertical-coherence-prism-maps
      ( top-left)
      ( top-right)
      ( top-front)
      ( front-left-bottom ∘ front-left-top)
      ( back-bottom ∘ back-top)
      ( front-right-bottom ∘ front-right-top)
      ( bottom-left)
      ( bottom-right)
      ( bottom-front)
      ( top)
      ( pasting-vertical-coherence-square-maps
        ( top-left)
        ( front-left-top)
        ( back-top)
        ( mid-left)
        ( front-left-bottom)
        ( back-bottom)
        ( bottom-left)
        ( left-top)
        ( left-bottom))
      ( pasting-vertical-coherence-square-maps
        ( top-right)
        ( back-top)
        ( front-right-top)
        ( mid-right)
        ( back-bottom)
        ( front-right-bottom)
        ( bottom-right)
        ( right-top)
        ( right-bottom))
      ( pasting-vertical-coherence-square-maps
        ( top-front)
        ( front-left-top)
        ( front-right-top)
        ( mid-front)
        ( front-left-bottom)
        ( front-right-bottom)
        ( bottom-front)
        ( front-top)
        ( front-bottom))
      ( bottom)
  pasting-vertical-coherence-prism-maps prism-top prism-bottom =
    ( ap-concat-htpy
      ( bottom ·r front-left-bottom ·r front-left-top)
      ( _)
      ( _)
      ( commutative-pasting-vertical-pasting-horizontal-coherence-square-maps
        ( top-left)
        ( top-right)
        ( front-left-top)
        ( back-top)
        ( front-right-top)
        ( mid-left)
        ( mid-right)
        ( front-left-bottom)
        ( back-bottom)
        ( front-right-bottom)
        ( bottom-left)
        ( bottom-right)
        ( left-top)
        ( right-top)
        ( left-bottom)
        ( right-bottom))) ∙h
    ( right-whisk-square-htpy
      ( front-bottom ·r front-left-top)
      ( bottom ·r front-left-bottom ·r front-left-top)
      ( ( front-right-bottom) ·l
        ( (mid-right ·l left-top) ∙h (right-top ·r top-left)))
      ( prism-bottom ·r front-left-top)) ∙h
    ( ap-concat-htpy
      ( front-bottom ·r front-left-top)
      ( _)
      ( _)
      ( ( inv-htpy
          ( distributive-left-whisk-concat-htpy
            ( front-right-bottom)
            ( mid ·r front-left-top)
            ( pasting-horizontal-coherence-square-maps
              ( top-left)
              ( top-right)
              ( front-left-top)
              ( back-top)
              ( front-right-top)
              ( mid-left)
              ( mid-right)
              ( left-top)
              ( right-top)))) ∙h
        ( ap-left-whisk-htpy front-right-bottom prism-top) ∙h
        ( distributive-left-whisk-concat-htpy
          ( front-right-bottom)
          ( front-top)
          ( front-right-top ·l top)) ∙h
        ap-concat-htpy
          ( front-right-bottom ·l front-top)
          ( _)
          ( _)
          ( associative-left-whisk-comp
            ( front-right-bottom)
            ( front-right-top)
            ( top)))) ∙h
    ( inv-htpy-assoc-htpy
      ( front-bottom ·r front-left-top)
      ( front-right-bottom ·l front-top)
      ( ( front-right-bottom ∘ front-right-top) ·l top))
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( top-left : A → B) (top-right : B → C) (top-front : A → C)
  ( front-left : A → X) (back : B → Y) (front-right : C → Z)
  ( bottom-left : X → Y) (bottom-right : Y → Z) (bottom-front : X → Z)
  where

  [v] :
    ( top : coherence-triangle-maps top-front top-right top-left)
    ( left : coherence-square-maps top-left front-left back bottom-left)
    ( inv-right : coherence-square-maps back top-right bottom-right front-right)
    ( inv-front :
        coherence-square-maps front-left top-front bottom-front front-right)
    ( bottom : coherence-triangle-maps bottom-front bottom-right bottom-left) →
    ( ( inv-front ∙h ((bottom ·r front-left) ∙h (bottom-right ·l left))) ~
      ( (front-right ·l top) ∙h (inv-right ·r top-left))) →
    vertical-coherence-prism-maps
      ( top-left)
      ( top-right)
      ( top-front)
      ( front-left)
      ( back)
      ( front-right)
      ( bottom-left)
      ( bottom-right)
      ( bottom-front)
      ( top)
      ( left)
      ( inv-htpy inv-right)
      ( inv-htpy inv-front)
      ( bottom)
  [v] top left inv-right inv-front bottom α a =
    ( inv
      ( assoc
        ( bottom (front-left a))
        ( ap bottom-right (left a))
        ( inv (inv-right (top-left a))))) ∙
    ( inv
      ( right-transpose-eq-concat
        ( inv (inv-front a) ∙ ap front-right (top a))
        ( inv-right (top-left a))
        ( _)
        ( inv
          ( ( left-transpose-eq-concat
              ( inv-front a)
              ( bottom (front-left a) ∙ ap bottom-right (left a))
              ( _)
              ( α a)) ∙
            ( inv
              ( assoc
                ( inv (inv-front a))
                ( ap front-right (top a))
                ( inv-right (top-left a))))))))
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

  -- equiv-coherence-prism-maps :
  --   vertical-coherence-prism-maps top-left top-right top-front front-left back front-right bottom-left bottom-right bottom-front top left right front bottom ≃
  --   horizontal-coherence-prism-maps front-left top-front top-left bottom-front bottom-left back top-right bottom-right front-right (inv-htpy left) (inv-htpy top) (inv-htpy bottom) (inv-htpy front) (inv-htpy right)
  -- equiv-coherence-prism-maps = {!!}
```
