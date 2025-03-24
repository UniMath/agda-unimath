# Commuting prisms of maps

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.commuting-prisms-of-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where

open import foundation-core.commuting-prisms-of-maps funext public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps funext univalence
open import foundation.commuting-triangles-of-maps funext univalence
open import foundation.composition-algebra funext
open import foundation.function-extensionality funext
open import foundation.identity-types funext
open import foundation.postcomposition-functions funext
open import foundation.precomposition-functions funext
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-homotopies
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types funext
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
    ( right-whisker-concat-coherence-square-homotopies
      ( front-bottom ·r hA)
      ( bottom ·r hA' ·r hA)
      ( hC' ·l mid ·r hA)
      ( ( pasting-horizontal-coherence-square-maps
            h' g' hA' hB' hC' h'' g'' left-bottom right-bottom) ·r
        ( hA))
      ( prism-bottom ·r hA)
      ( hC' ·l ((g' ·l left-top) ∙h (right-top ·r h)))
      ) ∙h
    ( ap-concat-htpy
      ( front-bottom ·r hA)
      ( ( map-coherence-square-homotopies hC'
          ( front-top)
          ( mid ·r hA)
          (hC ·l top)
          ( pasting-horizontal-coherence-square-maps h g hA hB hC h' g'
            ( left-top)
            ( right-top))
          ( prism-top)) ∙h
        ( ap-concat-htpy
          ( hC' ·l front-top)
          ( preserves-comp-left-whisker-comp hC' hC top)))) ∙h
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
  ( inv-front : coherence-square-maps' f hA hC f')
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

### Commuting prisms of maps induce commuting prisms of precomposition maps

We prove this for a few different formulations of commuting prisms of maps.

The basic set-up is that, given a commuting prism of maps

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
    A' --------> C'
          f'
```

we have commuting prisms of
[precomposition maps](foundation-core.precomposition-functions.md)

```text
                    (B' → S)
         (- ∘ g') ∧     |     \ (- ∘ h')
                /       |       \
              / (- ∘ f')| ⇑       ∨
       (C' → S) ---------------> (A' → S)
           |            |            |
           |            | (- ∘ hB)   |
           |     ⇙      ∨      ⇙     |
  (- ∘ hC) |         (B → S)         | (- ∘ hA)
           |  (- ∘ g) ∧   \ (- ∘ h)  |
           |       /    ⇑    \       |
           ∨    /               ∨    ∨
        (C → S) ----------------> (A → S).
                     (- ∘ f)
```

Observe that the bottom and top triangles have switched positions, the diagram
is mirrored along the vertical axis compared to the underlying commuting prism,
and that the direction of the homotopies of the vertical squares are flipped.

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
  ( S : UU l)
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
  precomp-vertical-coherence-prism-inv-squares-maps =
    ( ap-concat-htpy
      ( htpy-precomp front S)
      ( inv-distributive-htpy-precomp-left-whisker hC top S)) ∙h
    ( inv-htpy
      ( distributive-htpy-precomp-concat-htpy front (hC ·l top) S)) ∙h
    ( λ i → ap eq-htpy (ap (i ·l_) (eq-htpy (inv-htpy H)))) ∙h
    ( distributive-htpy-precomp-concat-htpy
      ( bottom ·r hA)
      ( pasting-horizontal-coherence-square-maps h g hA hB hC h' g' left right)
      ( S)) ∙h
    ( ap-binary-concat-htpy
      ( distributive-htpy-precomp-right-whisker hA bottom S)
      ( ( distributive-htpy-precomp-concat-htpy (g' ·l left) (right ·r h) S) ∙h
        ( ap-binary-concat-htpy
          ( distributive-htpy-precomp-left-whisker g' left S)
          ( distributive-htpy-precomp-right-whisker h right S))))

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
    ( inv-htpy
      ( ( compute-concat-htpy-precomp
          ( (g' ·l left) ∙h (right ·r h))
          ( hC ·l inv-top)
          ( S)) ∙h
        ( ap-binary-concat-htpy
          ( ( compute-concat-htpy-precomp (g' ·l left) (right ·r h) S) ∙h
            ( ap-binary-concat-htpy
              ( distributive-htpy-precomp-left-whisker g' left S)
              ( distributive-htpy-precomp-right-whisker h right S)))
          ( distributive-htpy-precomp-left-whisker hC inv-top S)))) ∙h
    ( λ i → ap (λ p → htpy-precomp p S i) (eq-htpy H)) ∙h
    ( compute-concat-htpy-precomp (inv-bottom ·r hA) front S) ∙h
    ( ap-concat-htpy'
      ( htpy-precomp front S)
      ( distributive-htpy-precomp-right-whisker hA inv-bottom S))

  precomp-vertical-coherence-prism-inv-triangles-maps :
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
  precomp-vertical-coherence-prism-inv-triangles-maps =
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

### Commuting prisms of maps induce commuting prisms of postcomposition maps

Given a commuting prism of maps

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
    A' --------> C'
          f'
```

we have commuting prisms of
[postcomposition maps](foundation-core.postcomposition-functions.md)s

```text
                     (S → B)
          (h ∘ -) ∧     |     \ (g ∘ -)
                /       |       \
              /  (f ∘ -)| ⇑       ∨
        (S → A) ----------------> (S → C)
           |            |            |
           |            | (hB ∘ -)   |
           |     ⇗      ∨      ⇗     |
  (hA ∘ -) |         (S → B')        | (hC ∘ -)
           | (h' ∘ -) ∧   \ (g' ∘ -) |
           |       /    ⇑    \       |
           ∨    /               ∨    ∨
        (S → A') ---------------> (S → C').
                     (f' ∘ -)
```

```agda
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

  postcomp-vertical-coherence-prism-inv-triangles-maps :
    vertical-coherence-prism-inv-triangles-maps
      ( postcomp S f)
      ( postcomp S g)
      ( postcomp S h)
      ( postcomp S f')
      ( postcomp S g')
      ( postcomp S h')
      ( postcomp S hA)
      ( postcomp S hB)
      ( postcomp S hC)
      ( htpy-postcomp S inv-top)
      ( htpy-postcomp S front)
      ( htpy-postcomp S right)
      ( htpy-postcomp S left)
      ( htpy-postcomp S inv-bottom)
  postcomp-vertical-coherence-prism-inv-triangles-maps =
    ( inv-htpy
      ( ( distributive-htpy-postcomp-concat-htpy
          ( g' ·l left ∙h right ·r h)
          ( hC ·l inv-top)
          ( S)) ∙h
        ( ap-binary-concat-htpy
          ( ( distributive-htpy-postcomp-concat-htpy
              ( g' ·l left)
              ( right ·r h) S) ∙h
            ( ap-binary-concat-htpy
              ( distributive-htpy-postcomp-left-whisker g' left S)
              ( distributive-htpy-postcomp-right-whisker h right S)))
          ( distributive-htpy-postcomp-left-whisker hC inv-top S)))) ∙h
    ( λ i → ap (λ p → htpy-postcomp S p i) (eq-htpy H)) ∙h
    ( distributive-htpy-postcomp-concat-htpy (inv-bottom ·r hA) front S)
```
