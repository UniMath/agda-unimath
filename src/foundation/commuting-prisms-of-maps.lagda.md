# Commuting prisms of maps

```agda
module foundation.commuting-prisms-of-maps where

open import foundation-core.commuting-prisms-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.precomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
```

</details>

## Definitions

### Vertical pasting of vertical prisms of maps

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
      ( ( ap-left-whisk-coherence-square-homotopies hC'
          ( front-top)
          ( mid ·r hA)
          ( prism-top)) ∙h
        ( ap-concat-htpy
          ( hC' ·l front-top)
          ( associative-left-whisk-comp hC' hC top)))) ∙h
    ( inv-htpy-assoc-htpy
      ( front-bottom ·r hA)
      ( hC' ·l front-top)
      ( ( hC' ∘ hC) ·l top))
```

## Properties

### The two definitions of vertical prisms are equivalent

```agda
module _
  { l1 l2 l3 l1' l2' l3' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  ( top : coherence-triangle-maps f g h)
  ( inv-front : coherence-square-maps hA f f' hC)
  ( inv-right : coherence-square-maps' g hB hC g')
  ( left : coherence-square-maps h hA hB h')
  ( bottom : coherence-triangle-maps f' g' h')
  where

  equiv-rotate-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps' f g h f' g' h' hA hB hC
      ( top)
      ( inv-front)
      ( inv-right)
      ( left)
      ( bottom) ≃
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( inv-htpy inv-front)
      ( inv-htpy inv-right)
      ( left)
      ( bottom)
  equiv-rotate-vertical-coherence-prism-maps =
    equiv-Π-equiv-family
      ( λ a →
        ( equiv-concat-assoc
          ( bottom (hA a))
          ( ap g' (left a))
          ( inv (inv-right (h a))) _) ∘e
        ( equiv-right-transpose-eq-concat' _
          ( inv (inv-front a) ∙ ap hC (top a))
          ( inv-right (h a))) ∘e
        ( inv-equiv
          ( equiv-concat-assoc' _
            ( inv (inv-front a))
            ( ap hC (top a))
            ( inv-right (h a)))) ∘e
        ( equiv-left-transpose-eq-concat
          ( inv-front a)
          ( bottom (hA a) ∙ ap g' (left a))
          ( _)))

  rotate-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps' f g h f' g' h' hA hB hC
      ( top)
      ( inv-front)
      ( inv-right)
      ( left)
      ( bottom) →
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( inv-htpy inv-front)
      ( inv-htpy inv-right)
      ( left)
      ( bottom)
  rotate-vertical-coherence-prism-maps =
    map-equiv equiv-rotate-vertical-coherence-prism-maps
```

### Commuting prisms of maps induces commuting prisms on function types via precomposition

```agda
module _
  { l1 l2 l3 l1' l2' l3' l : Level}
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
  ( H :
    vertical-coherence-prism-maps f g h f' g' h' hA hB hC
      ( top)
      ( front)
      ( right)
      ( left)
      ( bottom))
  (S : UU l)
  where

  precomp-vertical-coherence-prism-inv-squares-maps :
    vertical-coherence-prism-inv-squares-maps
      ( precomp f' S)
      ( precomp h' S)
      ( precomp g' S)
      ( precomp f S)
      ( precomp h S)
      ( precomp g S)
      ( precomp hC S)
      ( precomp hB S)
      ( precomp hA S)
      ( precomp-coherence-triangle-maps f' g' h' bottom S)
      ( precomp-coherence-square-maps f hA hC f' front S)
      ( precomp-coherence-square-maps h hA hB h' left S)
      ( precomp-coherence-square-maps g hB hC g' right S)
      ( precomp-coherence-triangle-maps f g h top S)
  precomp-vertical-coherence-prism-inv-squares-maps i =
    ( inv (eq-htpy-concat-htpy (i ·l front) ((i ∘ hC) ·l top))) ∙
    ( ap
      ( eq-htpy)
      ( ( ap
          ( (i ·l front) ∙h_)
          ( eq-htpy (inv-htpy (associative-left-whisk-comp i hC top)))) ∙
        ( inv
          ( eq-htpy
            ( distributive-left-whisk-concat-htpy i front (hC ·l top)))) ∙
        ( ap (i ·l_) (eq-htpy (inv-htpy H))) ∙
        ( eq-htpy
          ( ( distributive-left-whisk-concat-htpy i
              ( bottom ·r hA)
              ( (g' ·l left) ∙h (right ·r h))) ∙h
            ( ap-concat-htpy
              ( i ·l (bottom ·r hA))
              ( distributive-left-whisk-concat-htpy i
                ( g' ·l left)
                ( right ·r h))))))) ∙
    ( eq-htpy-concat-htpy
      ( (i ·l bottom) ·r hA)
      ( (i ·l g' ·l left) ∙h ((i ·l right) ·r h))) ∙
    ( ap-binary (_∙_)
      ( compute-eq-htpy-right-whisk hA (i ·l bottom))
      ( eq-htpy-concat-htpy (i ·l (g' ·l left)) (i ·l (right ·r h)))) ∙
    ( ap
      ( ap (precomp hA S) (eq-htpy (i ·l bottom)) ∙_)
      ( ap-binary (_∙_)
        ( ap eq-htpy (eq-htpy (associative-left-whisk-comp i g' left)))
        ( compute-eq-htpy-right-whisk h (i ·l right))))

  precomp-vertical-coherence-prism-maps :
    vertical-coherence-prism-maps
      ( precomp f' S)
      ( precomp h' S)
      ( precomp g' S)
      ( precomp f S)
      ( precomp h S)
      ( precomp g S)
      ( precomp hC S)
      ( precomp hB S)
      ( precomp hA S)
      ( precomp-coherence-triangle-maps f' g' h' bottom S)
      ( inv-htpy (precomp-coherence-square-maps f hA hC f' front S))
      ( inv-htpy (precomp-coherence-square-maps h hA hB h' left S))
      ( inv-htpy (precomp-coherence-square-maps g hB hC g' right S))
      ( precomp-coherence-triangle-maps f g h top S)
  precomp-vertical-coherence-prism-maps =
    vertical-coherence-prism-maps-vertical-coherence-prism-inv-squares-maps
      ( precomp f' S)
      ( precomp h' S)
      ( precomp g' S)
      ( precomp f S)
      ( precomp h S)
      ( precomp g S)
      ( precomp hC S)
      ( precomp hB S)
      ( precomp hA S)
      ( precomp-coherence-triangle-maps f' g' h' bottom S)
      ( precomp-coherence-square-maps f hA hC f' front S)
      ( precomp-coherence-square-maps h hA hB h' left S)
      ( precomp-coherence-square-maps g hB hC g' right S)
      ( precomp-coherence-triangle-maps f g h top S)
      ( precomp-vertical-coherence-prism-inv-squares-maps)

compute-htpy-precomp-right-whisker :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B} (h : C → A) (H : f ~ g) (S : UU l4) →
  precomp h S ·l htpy-precomp H S ~ htpy-precomp (H ·r h) S
compute-htpy-precomp-right-whisker {f = f} {g} h H S i =
  coherence-square-eq-htpy-ap-precomp h (i ∘ f) (i ∘ g) (i ·l H)

compute-htpy-precomp-left-whisker :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B} (h : B → C) (H : f ~ g) (S : UU l4) →
  htpy-precomp H S ·r precomp h S ~ htpy-precomp (h ·l H) S
compute-htpy-precomp-left-whisker {f = f} {g} h H S i =
  ap eq-htpy (eq-htpy (ap-comp i h ∘ H))

module _
  { l1 l2 l3 l1' l2' l3' l : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → C) (g : B → C) (h : A → B)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'}
  ( f' : A' → C') (g' : B' → C') (h' : A' → B')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  ( inv-top : coherence-triangle-maps' f g h)
  ( front : coherence-square-maps f hA hC f')
  ( right : coherence-square-maps g hB hC g')
  ( left : coherence-square-maps h hA hB h')
  ( inv-bottom : coherence-triangle-maps' f' g' h')
  ( H :
    vertical-coherence-prism-inv-triangles-maps f g h f' g' h' hA hB hC
      ( inv-top)
      ( front)
      ( right)
      ( left)
      ( inv-bottom))
  (S : UU l)
  where

  precomp-vertical-inv-boundary-vertical-coherence-inv-triangles-prism-maps :
    vertical-coherence-prism-inv-boundary-maps
      ( precomp f' S)
      ( precomp h' S)
      ( precomp g' S)
      ( precomp f S)
      ( precomp h S)
      ( precomp g S)
      ( precomp hC S)
      ( precomp hB S)
      ( precomp hA S)
      ( precomp-coherence-triangle-maps' f' g' h' inv-bottom S)
      ( precomp-coherence-square-maps f hA hC f' front S)
      ( precomp-coherence-square-maps h hA hB h' left S)
      ( precomp-coherence-square-maps g hB hC g' right S)
      ( precomp-coherence-triangle-maps' f g h inv-top S)
  precomp-vertical-inv-boundary-vertical-coherence-inv-triangles-prism-maps =
    ( ap-binary-concat-htpy
      ( ( ap-binary-concat-htpy
          ( compute-htpy-precomp-left-whisker g' left S)
          ( compute-htpy-precomp-right-whisker h right S)) ∙h
        ( inv-htpy (compute-concat-htpy-precomp (g' ·l left) (right ·r h) S)))
      ( compute-htpy-precomp-left-whisker hC inv-top S)) ∙h
    ( inv-htpy
      ( compute-concat-htpy-precomp
        ( (g' ·l left) ∙h (right ·r h))
        ( hC ·l inv-top)
        ( S))) ∙h
    ( λ i → ap (λ p → htpy-precomp p S i) (eq-htpy H)) ∙h
    ( compute-concat-htpy-precomp (inv-bottom ·r hA) front S) ∙h
    ( ap-concat-htpy'
      ( htpy-precomp front S)
      ( inv-htpy (compute-htpy-precomp-right-whisker hA inv-bottom S)))

  precomp-vertical-coherence-inv-triangles-prism-maps :
    vertical-coherence-prism-inv-triangles-maps
      ( precomp f' S)
      ( precomp h' S)
      ( precomp g' S)
      ( precomp f S)
      ( precomp h S)
      ( precomp g S)
      ( precomp hC S)
      ( precomp hB S)
      ( precomp hA S)
      ( precomp-coherence-triangle-maps' f' g' h' inv-bottom S)
      ( inv-htpy (precomp-coherence-square-maps f hA hC f' front S))
      ( inv-htpy (precomp-coherence-square-maps h hA hB h' left S))
      ( inv-htpy (precomp-coherence-square-maps g hB hC g' right S))
      ( precomp-coherence-triangle-maps' f g h inv-top S)
  precomp-vertical-coherence-inv-triangles-prism-maps =
    vertical-coherence-prism-inv-triangles-maps-vertical-coherence-prism-inv-boundary-maps
      ( precomp f' S)
      ( precomp h' S)
      ( precomp g' S)
      ( precomp f S)
      ( precomp h S)
      ( precomp g S)
      ( precomp hC S)
      ( precomp hB S)
      ( precomp hA S)
      ( precomp-coherence-triangle-maps' f' g' h' inv-bottom S)
      ( precomp-coherence-square-maps f hA hC f' front S)
      ( precomp-coherence-square-maps h hA hB h' left S)
      ( precomp-coherence-square-maps g hB hC g' right S)
      ( precomp-coherence-triangle-maps' f g h inv-top S)
      ( precomp-vertical-inv-boundary-vertical-coherence-inv-triangles-prism-maps)
```
