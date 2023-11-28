# Commuting prisms of maps

```agda
module foundation.commuting-prisms-of-maps where

open import foundation-core.commuting-prisms-of-maps public
```

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.whiskering-homotopies
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
open import foundation-core.function-types
open import foundation-core.identity-types
```

```agda
module _
  { l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  { A'' : UU l1''} {B'' : UU l2''} {C'' : UU l3''}
  ( f'' : A'' → C'') (g'' : B'' → C'') (h'' : A'' → B'')
  ( hA' : A' → A'') (hB' : B' → B'') (hC' : C' → C'')
  ( top : coherence-triangle-maps f g h)
  ( front-top : coherence-square-maps f hA hC f')
  ( right-top : coherence-square-maps g hB hC g')
  ( left-top : coherence-square-maps h hA hB h')
  ( mid : coherence-triangle-maps f' g' h')
  ( front-bottom : coherence-square-maps f' hA' hC' f'')
  ( right-bottom : coherence-square-maps g' hB' hC' g'')
  ( left-bottom : coherence-square-maps h' hA' hB' h'')
  ( bottom : coherence-triangle-maps f'' g'' h'')
  where

  pasting-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( front-top)
      ( right-top)
      ( left-top)
      ( mid) →
    vertical-coherence-prism-maps f' g' h' f'' g'' h'' hA' hB' hC'
      ( mid)
      ( front-bottom)
      ( right-bottom)
      ( left-bottom)
      ( bottom) →
    vertical-coherence-prism-maps f g h f'' g'' h''
      ( hA' ∘ hA)
      ( hB' ∘ hB)
      ( hC' ∘ hC)
      ( top)
      ( pasting-vertical-coherence-square-maps f hA hC f' hA' hC' f''
        ( front-top)
        ( front-bottom))
      ( pasting-vertical-coherence-square-maps g hB hC g' hB' hC' g''
        ( right-top)
        ( right-bottom))
      ( pasting-vertical-coherence-square-maps h hA hB h' hA' hB' h''
        ( left-top)
        ( left-bottom))
      ( bottom)
  pasting-vertical-coherence-prism-maps prism-top prism-bottom =
    ( ap-concat-htpy
      ( bottom ·r hA' ·r hA)
      ( commutative-pasting-vertical-pasting-horizontal-coherence-square-maps
        h g hA hB hC h' g' hA' hB' hC' h'' g''
        ( left-top)
        ( right-top)
        ( left-bottom)
        ( right-bottom))) ∙h
    ( right-whisk-square-htpy
      ( front-bottom ·r hA)
      ( bottom ·r hA' ·r hA)
      ( hC' ·l ((g' ·l left-top) ∙h (right-top ·r h)))
      ( prism-bottom ·r hA)) ∙h
    ( ap-concat-htpy
      ( front-bottom ·r hA)
      ( ( inv-htpy
          ( distributive-left-whisk-concat-htpy hC'
            ( mid ·r hA)
            ( pasting-horizontal-coherence-square-maps h g hA hB hC h' g'
              ( left-top)
              ( right-top)))) ∙h
        ( ap-left-whisk-htpy hC' prism-top) ∙h
        ( distributive-left-whisk-concat-htpy hC' front-top (hC ·l top)) ∙h
        ( ap-concat-htpy
          ( hC' ·l front-top)
          ( associative-left-whisk-comp
            ( hC')
            ( hC)
            ( top))))) ∙h
    ( inv-htpy-assoc-htpy
      ( front-bottom ·r hA)
      ( hC' ·l front-top)
      ( ( hC' ∘ hC) ·l top))
```

```agda
module _
  { l1 l2 l3 l1' l2' l3' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  where

  [v] :
    ( top : coherence-triangle-maps f g h)
    ( inv-front : coherence-square-maps hA f f' hC)
    ( inv-right : coherence-square-maps hB g g' hC)
    ( left : coherence-square-maps h hA hB h')
    ( bottom : coherence-triangle-maps f' g' h') →
    ( ( inv-front ∙h ((bottom ·r hA) ∙h (g' ·l left))) ~
      ( (hC ·l top) ∙h (inv-right ·r h))) →
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( inv-htpy inv-front)
      ( inv-htpy inv-right)
      ( left)
      ( bottom)
  [v] top inv-front inv-right left bottom α a =
    ( inv
      ( assoc
        ( bottom (hA a))
        ( ap g' (left a))
        ( inv (inv-right (h a))))) ∙
    ( inv
      ( right-transpose-eq-concat
        ( inv (inv-front a) ∙ ap hC (top a))
        ( inv-right (h a))
        ( _)
        ( inv
          ( ( left-transpose-eq-concat
              ( inv-front a)
              ( bottom (hA a) ∙ ap g' (left a))
              ( _)
              ( α a)) ∙
            ( inv
              ( assoc
                ( inv (inv-front a))
                ( ap hC (top a))
                ( inv-right (h a))))))))
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
