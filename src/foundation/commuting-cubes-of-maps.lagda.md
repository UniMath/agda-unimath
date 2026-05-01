# Commuting cubes of maps

```agda
module foundation.commuting-cubes-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-hexagons-of-identifications
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

We specify the type of the homotopy witnessing that a cube commutes. Imagine
that the cube is presented as a lattice

```text
            A'
          / | \
         /  |  \
        ∨   ∨   ∨
       B'   A    C'
       |\ /   \ /|
       | \     / |
       ∨∨ ∨   ∨ ∨∨
       B    D'   C
        \   |   /
         \  |  /
          ∨ ∨ ∨
            D
```

with all maps pointing in the downwards direction. Presented in this way, a cube
of maps has a top face, a back-left face, a back-right face, a front-left face,
a front-right face, and a bottom face, all of which are homotopies. An element
of type `coherence-cube-maps` is a homotopy filling the cube.

## Definitions

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  where

  coherence-cube-maps :
    (top : (h' ∘ f') ~ (k' ∘ g'))
    (back-left : (f ∘ hA) ~ (hB ∘ f'))
    (back-right : (g ∘ hA) ~ (hC ∘ g'))
    (front-left : (h ∘ hB) ~ (hD ∘ h'))
    (front-right : (k ∘ hC) ~ (hD ∘ k'))
    (bottom : (h ∘ f) ~ (k ∘ g)) →
    UU (l4 ⊔ l1')
  coherence-cube-maps top back-left back-right front-left front-right bottom =
    (a' : A') →
    coherence-hexagon
      ( ap h (back-left a'))
      ( front-left (f' a'))
      ( ap hD (top a'))
      ( bottom (hA a'))
      ( ap k (back-right a'))
      ( front-right (g' a'))
```

### Symmetries of commuting cubes

The symmetry group D₃ acts on a cube. However, the coherence filling a cube
needs to be modified to show that the rotated/reflected cube again commutes. In
the following definitions we provide the homotopies witnessing that the
rotated/reflected cubes again commute.

Note: although in principle it ought to be enough to show this for the
generators of the symmetry group D₃, in practice it is more straightforward to
just do the work for each of the symmetries separately. One reason is that some
of the homotopies witnessing that the faces commute will be inverted as the
result of an application of a symmetry. Inverting a homotopy twice results in a
new homotopy that is only homotopic to the original homotopy.

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : coherence-square-maps g' f' k' h')
  (back-left : coherence-square-maps f' hA hB f)
  (back-right : coherence-square-maps g' hA hC g)
  (front-left : coherence-square-maps h' hB hD h)
  (front-right : coherence-square-maps k' hC hD k)
  (bottom : coherence-square-maps g f k h)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  coherence-cube-maps-rotate-120 :
    coherence-cube-maps hC k' k hD hA f' f hB g' g h' h
      ( back-left)
      ( inv-htpy back-right)
      ( inv-htpy top)
      ( inv-htpy bottom)
      ( inv-htpy front-left)
      ( front-right)
  coherence-cube-maps-rotate-120 a' =
    ( right-whisker-concat
      ( right-whisker-concat
        ( ap-inv k (back-right a'))
        ( inv (bottom (hA a'))))
      ( ap h (back-left a'))) ∙
    ( ( hexagon-rotate-120
        ( ap h (back-left a'))
        ( front-left (f' a'))
        ( ap hD (top a'))
        ( bottom (hA a'))
        ( ap k (back-right a'))
        ( front-right (g' a'))
        ( c a')) ∙
      ( inv
        ( left-whisker-concat
          ( front-right (g' a'))
          ( right-whisker-concat
            ( ap-inv hD (top a'))
            ( inv (front-left (f' a')))))))

  coherence-cube-maps-rotate-240 :
    coherence-cube-maps h' hB hD h g' hA hC g f' k' f k
      ( inv-htpy back-right)
      ( top)
      ( inv-htpy back-left)
      ( inv-htpy front-right)
      ( bottom)
      ( inv-htpy front-left)
  coherence-cube-maps-rotate-240 a' =
    ( left-whisker-concat _ (ap-inv k (back-right a'))) ∙
    ( ( hexagon-rotate-240
        ( ap h (back-left a'))
        ( front-left (f' a'))
        ( ap hD (top a'))
        ( bottom (hA a'))
        ( ap k (back-right a'))
        ( front-right (g' a'))
        ( c a')) ∙
      ( inv
        ( left-whisker-concat
          ( inv (front-left (f' a')))
          ( right-whisker-concat (ap-inv h (back-left a')) _))))

  coherence-cube-maps-mirror-A :
    coherence-cube-maps g f k h g' f' k' h' hA hC hB hD
      ( inv-htpy top)
      ( back-right)
      ( back-left)
      ( front-right)
      ( front-left)
      ( inv-htpy bottom)
  coherence-cube-maps-mirror-A a' =
    ( left-whisker-concat _ (ap-inv hD (top a'))) ∙
    ( hexagon-mirror-A
      ( ap h (back-left a'))
      ( front-left (f' a'))
      ( ap hD (top a'))
      ( bottom (hA a'))
      ( ap k (back-right a'))
      ( front-right (g' a'))
      ( c a'))

  coherence-cube-maps-mirror-B :
    coherence-cube-maps hB h' h hD hA g' g hC f' f k' k
      ( back-right)
      ( inv-htpy back-left)
      ( top)
      ( bottom)
      ( inv-htpy front-right)
      ( front-left)
  coherence-cube-maps-mirror-B a' =
    ( right-whisker-concat
      ( right-whisker-concat (ap-inv h (back-left a')) _)
      ( ap k (back-right a'))) ∙
    ( hexagon-mirror-B
      ( ap h (back-left a'))
      ( front-left (f' a'))
      ( ap hD (top a'))
      ( bottom (hA a'))
      ( ap k (back-right a'))
      ( front-right (g' a'))
      ( c a'))

  coherence-cube-maps-mirror-C :
    coherence-cube-maps k' hC hD k f' hA hB f g' h' g h
      ( inv-htpy back-left)
      ( inv-htpy top)
      ( inv-htpy back-right)
      ( inv-htpy front-left)
      ( inv-htpy bottom)
      ( inv-htpy front-right)
  coherence-cube-maps-mirror-C a' =
    ( ap
      ( λ t → (t ∙ inv (front-left (f' a'))) ∙ (ap h (inv (back-left a'))))
      ( ap-inv hD (top a'))) ∙
    ( ( left-whisker-concat _ (ap-inv h (back-left a'))) ∙
      ( ( hexagon-mirror-C
          ( ap h (back-left a'))
          ( front-left (f' a'))
          ( ap hD (top a'))
          ( bottom (hA a'))
          ( ap k (back-right a'))
          ( front-right (g' a'))
          ( c a')) ∙
        ( inv
          ( left-whisker-concat
            ( inv (front-right (g' a')))
            ( right-whisker-concat (ap-inv k (back-right a')) _)))))
```

### Rectangles in commuting cubes

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : coherence-square-maps g' f' k' h')
  (back-left : coherence-square-maps f' hA hB f)
  (back-right : coherence-square-maps g' hA hC g)
  (front-left : coherence-square-maps h' hB hD h)
  (front-right : coherence-square-maps k' hC hD k)
  (bottom : coherence-square-maps g f k h)
  where

  rectangle-left-cube :
    ((h ∘ f) ∘ hA) ~ (hD ∘ (h' ∘ f'))
  rectangle-left-cube =
    pasting-horizontal-coherence-square-maps
      f' h' hA hB hD f h back-left front-left

  rectangle-right-cube :
    ((k ∘ g) ∘ hA) ~ (hD ∘ (k' ∘ g'))
  rectangle-right-cube =
    pasting-horizontal-coherence-square-maps
      g' k' hA hC hD g k back-right front-right

  coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube :
    (c : coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
    coherence-htpy-parallel-cone
      ( bottom)
      ( refl-htpy' hD)
      ( hA , h' ∘ f' , rectangle-left-cube)
      ( hA , k' ∘ g' , rectangle-right-cube)
      ( refl-htpy' hA)
      ( top)
  coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube c =
    ( λ a' → left-whisker-concat (rectangle-left-cube a') right-unit) ∙h
    ( c)

  rectangle-top-front-left-cube :
    ((h ∘ hB) ∘ f') ~ ((hD ∘ k') ∘ g')
  rectangle-top-front-left-cube =
    ( front-left ·r f') ∙h (hD ·l top)

  rectangle-back-right-bottom-cube :
    ((h ∘ f) ∘ hA) ~ ((k ∘ hC) ∘ g')
  rectangle-back-right-bottom-cube =
    ( bottom ·r hA) ∙h (k ·l back-right)

  rectangle-top-front-right-cube :
    ((hD ∘ h') ∘ f') ~ ((k ∘ hC) ∘ g')
  rectangle-top-front-right-cube =
    (hD ·l top) ∙h (inv-htpy (front-right) ·r g')

  rectangle-back-left-bottom-cube :
    ((h ∘ hB) ∘ f') ~ ((k ∘ g) ∘ hA)
  rectangle-back-left-bottom-cube =
    (h ·l (inv-htpy back-left)) ∙h (bottom ·r hA)
```

In analogy to the coherence
`coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube` we also
expect to be able to construct a coherence

```text
  coherence-htpy-parallel-cone-rectangle-top-fl-rectangle-br-bot-cube :
    (c : coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
    coherence-htpy-parallel-cone
      ( inv-htpy front-right)
      ( refl-htpy' h)
      ( g' , hB ∘ f' , inv-htpy (rectangle-top-front-left-cube))
      ( g' , f ∘ hA , inv-htpy (rectangle-back-right-bottom-cube))
      ( refl-htpy' g')
      ( inv-htpy back-left)
```

### Vertical pasting of commuting cubes

> The following Agda code is not checked due to bad performance.
> [#1525](https://github.com/UniMath/agda-unimath/issues/1525)

```text
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' l1'' l2'' l3'' l4'' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  {A'' : UU l1''} {B'' : UU l2''} {C'' : UU l3''} {D'' : UU l4''}
  (f'' : A'' → B'') (g'' : A'' → C'') (h'' : B'' → D'') (k'' : C'' → D'')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (hA' : A'' → A') (hB' : B'' → B') (hC' : C'' → C') (hD' : D'' → D')
  (mid : (h' ∘ f') ~ (k' ∘ g'))
  (bottom-back-left : (f ∘ hA) ~ (hB ∘ f'))
  (bottom-back-right : (g ∘ hA) ~ (hC ∘ g'))
  (bottom-front-left : (h ∘ hB) ~ (hD ∘ h'))
  (bottom-front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g))
  (top : (h'' ∘ f'') ~ (k'' ∘ g''))
  (top-back-left : (f' ∘ hA') ~ (hB' ∘ f''))
  (top-back-right : (g' ∘ hA') ~ (hC' ∘ g''))
  (top-front-left : (h' ∘ hB') ~ (hD' ∘ h''))
  (top-front-right : (k' ∘ hC') ~ (hD' ∘ k''))
  where

  pasting-vertical-coherence-cube-maps :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      ( mid)
      ( bottom-back-left)
      ( bottom-back-right)
      ( bottom-front-left)
      ( bottom-front-right)
      ( bottom) →
    coherence-cube-maps f' g' h' k' f'' g'' h'' k'' hA' hB' hC' hD'
      ( top)
      ( top-back-left)
      ( top-back-right)
      ( top-front-left)
      ( top-front-right)
      ( mid) →
    coherence-cube-maps f g h k f'' g'' h'' k''
      ( hA ∘ hA') (hB ∘ hB') (hC ∘ hC') (hD ∘ hD')
      ( top)
      ( pasting-vertical-coherence-square-maps f'' hA' hB' f' hA hB f
        ( top-back-left) (bottom-back-left))
      ( pasting-vertical-coherence-square-maps g'' hA' hC' g' hA hC g
        ( top-back-right) (bottom-back-right))
      ( pasting-vertical-coherence-square-maps h'' hB' hD' h' hB hD h
        ( top-front-left) (bottom-front-left))
      ( pasting-vertical-coherence-square-maps k'' hC' hD' k' hC hD k
        ( top-front-right) (bottom-front-right))
      ( bottom)
  pasting-vertical-coherence-cube-maps α β =
    ( right-whisker-concat-htpy
      ( commutative-pasting-vertical-pasting-horizontal-coherence-square-maps
        f'' h'' hA' hB' hD' f' h' hA hB hD f h
        top-back-left top-front-left bottom-back-left bottom-front-left)
      ( (hD ∘ hD') ·l top)) ∙h
    ( left-whisker-concat-coherence-square-homotopies
      ( bottom-left-rect ·r hA')
      ( hD ·l (mid ·r hA'))
      ( hD ·l top-left-rect)
      ( hD ·l top-right-rect)
      ( (hD ∘ hD') ·l top)
      ( ( left-whisker-concat-htpy
          ( hD ·l top-left-rect)
          ( inv-preserves-comp-left-whisker-comp hD hD' top)) ∙h
        ( map-coherence-square-homotopies hD
          ( mid ·r hA') (top-left-rect) (top-right-rect) (hD' ·l top)
          ( β)))) ∙h
    ( right-whisker-concat-htpy
      ( α ·r hA')
      ( hD ·l top-right-rect)) ∙h
    ( assoc-htpy
      ( bottom ·r (hA ∘ hA'))
      ( bottom-right-rect ·r hA')
      ( hD ·l top-right-rect)) ∙h
    ( left-whisker-concat-htpy
      ( bottom ·r (hA ∘ hA'))
      ( inv-htpy
        ( commutative-pasting-vertical-pasting-horizontal-coherence-square-maps
          g'' k'' hA' hC' hD' g' k' hA hC hD g k
          top-back-right top-front-right bottom-back-right bottom-front-right)))
    where
      bottom-left-rect : h ∘ f ∘ hA ~ hD ∘ h' ∘ f'
      bottom-left-rect =
        pasting-horizontal-coherence-square-maps f' h' hA hB hD f h
          bottom-back-left bottom-front-left
      bottom-right-rect : k ∘ g ∘ hA ~ hD ∘ k' ∘ g'
      bottom-right-rect =
        pasting-horizontal-coherence-square-maps g' k' hA hC hD g k
          bottom-back-right bottom-front-right
      top-left-rect : h' ∘ f' ∘ hA' ~ hD' ∘ h'' ∘ f''
      top-left-rect =
        pasting-horizontal-coherence-square-maps f'' h'' hA' hB' hD' f' h'
          top-back-left top-front-left
      top-right-rect : k' ∘ g' ∘ hA' ~ hD' ∘ k'' ∘ g''
      top-right-rect =
        pasting-horizontal-coherence-square-maps g'' k'' hA' hC' hD' g' k'
          top-back-right top-front-right
      back-left-rect : f ∘ hA ∘ hA' ~ hB ∘ hB' ∘ f''
      back-left-rect =
        pasting-vertical-coherence-square-maps f'' hA' hB' f' hA hB f
          top-back-left bottom-back-left
```

### Any coherence of commuting cubes induces a coherence of parallel cones

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : coherence-square-maps g' f' k' h')
  (back-left : coherence-square-maps f' hA hB f)
  (back-right : coherence-square-maps g' hA hC g)
  (front-left : coherence-square-maps h' hB hD h)
  (front-right : coherence-square-maps k' hC hD k)
  (bottom : coherence-square-maps g f k h)
  where

  coherence-htpy-parallel-cone-coherence-cube-maps :
    ( c :
      coherence-cube-maps
        f g h k f' g' h' k' hA hB hC hD
        top back-left back-right front-left front-right bottom) →
    coherence-htpy-parallel-cone
      ( front-left)
      ( refl-htpy' k)
      ( ( f') ,
        ( g ∘ hA) ,
        ( rectangle-back-left-bottom-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))
      ( ( f') ,
        ( hC ∘ g') ,
        ( rectangle-top-front-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))
      ( refl-htpy' f')
      ( back-right)
  coherence-htpy-parallel-cone-coherence-cube-maps c =
    ( assoc-htpy
      ( h ·l (inv-htpy back-left))
      ( bottom ·r hA)
      ( (k ·l back-right) ∙h (refl-htpy' (k ∘ (hC ∘ g'))))) ∙h
    ( ( ap-concat-htpy'
        ( _)
        ( left-whisker-inv-htpy h back-left)) ∙h
      ( inv-htpy-left-transpose-htpy-concat (h ·l back-left) _ _
        ( ( (inv-htpy-assoc-htpy (h ·l back-left) (front-left ·r f') _) ∙h
            ( ( inv-htpy-assoc-htpy
                ( (h ·l back-left) ∙h (front-left ·r f'))
                ( hD ·l top)
                ( (inv-htpy front-right) ·r g')) ∙h
              ( inv-htpy-right-transpose-htpy-concat _ (front-right ·r g') _
                ( (assoc-htpy (bottom ·r hA) _ _) ∙h (inv-htpy c))))) ∙h
          ( ap-concat-htpy (bottom ·r hA) inv-htpy-right-unit-htpy))))
```

### Commuting cubes of maps induce commuting cubes of precomposition maps

```agda
module _
  { l1 l2 l3 l4 l1' l2' l3' l4' l5 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  ( f : A → B) (g : A → C) (h : B → D) (k : C → D)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  ( f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  ( hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  ( top : coherence-square-maps g' f' k' h')
  ( back-left : coherence-square-maps f' hA hB f)
  ( back-right : coherence-square-maps g' hA hC g)
  ( front-left : coherence-square-maps h' hB hD h)
  ( front-right : coherence-square-maps k' hC hD k)
  ( bottom : coherence-square-maps g f k h)
  where

  precomp-coherence-cube-maps :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      ( top)
      ( back-left)
      ( back-right)
      ( front-left)
      ( front-right)
      ( bottom) →
    ( W : UU l5) →
    coherence-cube-maps
      ( precomp h' W)
      ( precomp k' W)
      ( precomp f' W)
      ( precomp g' W)
      ( precomp h W)
      ( precomp k W)
      ( precomp f W)
      ( precomp g W)
      ( precomp hD W)
      ( precomp hB W)
      ( precomp hC W)
      ( precomp hA W)
      ( precomp-coherence-square-maps g f k h bottom W)
      ( precomp-coherence-square-maps hB h' h hD (inv-htpy front-left) W)
      ( precomp-coherence-square-maps hC k' k hD (inv-htpy front-right) W)
      ( precomp-coherence-square-maps hA f' f hB (inv-htpy back-left) W)
      ( precomp-coherence-square-maps hA g' g hC (inv-htpy back-right) W)
      ( precomp-coherence-square-maps g' f' k' h' top W)
  precomp-coherence-cube-maps c W =
    homotopy-reasoning
      ( (precomp f' W) ·l precomp-front-left-inv) ∙h
      ( precomp-back-left-inv ·r (precomp h W)) ∙h
      ( (precomp hA W) ·l precomp-bottom)
      ~ ( precomp-front-left-inv-whisker-f') ∙h
        ( precomp-h-whisker-back-left-inv) ∙h
        ( precomp-bottom-whisker-hA)
        by
        inv-htpy
          ( horizontal-concat-htpy²
            ( horizontal-concat-htpy²
              ( distributive-precomp-right-whisker-comp-coherence-square-maps
                ( W)
                ( hB)
                ( h')
                ( h)
                ( hD)
                ( inv-htpy front-left)
                ( f'))
              ( distributive-precomp-left-whisker-comp-coherence-square-maps
                ( W)
                ( hA)
                ( f')
                ( f)
                ( hB)
                ( inv-htpy back-left)
                ( h)))
            ( distributive-precomp-right-whisker-comp-coherence-square-maps
              ( W)
              ( g)
              ( f)
              ( k)
              ( h)
              ( bottom)
              ( hA)))
      ~ precomp-coherence-square-maps hA
          ( h' ∘ f')
          ( k ∘ g)
          ( hD)
          ( ( inv-htpy front-left ·r f') ∙h
            ( h ·l inv-htpy back-left) ∙h
            ( bottom ·r hA))
          ( W)
        by
        inv-htpy
          ( distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps
            ( W)
            ( hA)
            ( h' ∘ f')
            ( k ∘ g)
            ( hD)
            ( h ·l inv-htpy back-left)
            ( inv-htpy front-left ·r f')
            ( bottom ·r hA))
      ~ precomp-coherence-square-maps hA
          ( h' ∘ f')
          ( k ∘ g)
          ( hD)
          ( ( hD ·l top) ∙h
            ( ( inv-htpy front-right ·r g') ∙h
              ( k ·l inv-htpy back-right)))
          ( W)
        by
        ( λ x →
          ap
            ( λ square →
              precomp-coherence-square-maps hA (h' ∘ f') (k ∘ g) hD square W x)
            ( eq-htpy
              ( λ a' →
                inv-hexagon
                  ( ap hD (top a'))
                  ( inv (front-right (g' a')))
                  ( ap k (inv (back-right a')))
                  ( inv (front-left (f' a')))
                  ( ap h (inv (back-left a')))
                  ( bottom (hA a'))
                  ( coherence-cube-maps-rotate-240 f g h k f' g' h' k' hA hB hC
                    ( hD)
                    ( top)
                    ( back-left)
                    ( back-right)
                    ( front-left)
                    ( front-right)
                    ( bottom)
                    ( c)
                    ( a')))))
      ~ ( precomp-hD-whisker-top) ∙h
        ( ( precomp-front-right-inv-whisker-g') ∙h
          ( precomp-k-whisker-back-right-inv))
        by
        distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps'
          ( W)
          ( hA)
          ( h' ∘ f')
          ( k ∘ g)
          ( hD)
          ( inv-htpy front-right ·r g')
          ( hD ·l top)
          ( k ·l inv-htpy back-right)
      ~ ( precomp-top ·r (precomp hD W)) ∙h
        ( ( (precomp g' W) ·l precomp-front-right-inv) ∙h
          ( precomp-back-right-inv ·r (precomp k W)))
        by
        horizontal-concat-htpy²
          ( distributive-precomp-left-whisker-comp-coherence-square-maps W
            ( g')
            ( f')
            ( k')
            ( h')
            ( top)
            ( hD))
          ( horizontal-concat-htpy²
            ( distributive-precomp-right-whisker-comp-coherence-square-maps
              ( W)
              ( hC)
              ( k')
              ( k)
              ( hD)
              ( inv-htpy front-right)
              ( g'))
            ( distributive-precomp-left-whisker-comp-coherence-square-maps W hA
              ( g')
              ( g)
              ( hC)
              ( inv-htpy back-right)
              ( k)))
    where
    precomp-top :
      coherence-square-maps
        ( precomp k' W)
        ( precomp h' W)
        ( precomp g' W)
        ( precomp f' W)
    precomp-top = precomp-coherence-square-maps g' f' k' h' top W
    precomp-back-left-inv :
      coherence-square-maps
        ( precomp f W)
        ( precomp hB W)
        ( precomp hA W)
        ( precomp f' W)
    precomp-back-left-inv =
      precomp-coherence-square-maps hA f' f hB (inv-htpy back-left) W
    precomp-back-right-inv :
      coherence-square-maps
        ( precomp g W)
        ( precomp hC W)
        ( precomp hA W)
        ( precomp g' W)
    precomp-back-right-inv =
      precomp-coherence-square-maps hA g' g hC (inv-htpy back-right) W
    precomp-front-left-inv :
      coherence-square-maps
        ( precomp h W)
        ( precomp hD W)
        ( precomp hB W)
        ( precomp h' W)
    precomp-front-left-inv =
      precomp-coherence-square-maps hB h' h hD (inv-htpy front-left) W
    precomp-front-right-inv :
      coherence-square-maps
        ( precomp k W)
        ( precomp hD W)
        ( precomp hC W)
        ( precomp k' W)
    precomp-front-right-inv =
      precomp-coherence-square-maps hC k' k hD (inv-htpy front-right) W
    precomp-bottom :
      coherence-square-maps
        ( precomp k W)
        ( precomp h W)
        ( precomp g W)
        ( precomp f W)
    precomp-bottom = precomp-coherence-square-maps g f k h bottom W
    precomp-front-left-inv-whisker-f' :
      coherence-square-maps
        ( precomp h W)
        ( precomp hD W)
        ( precomp f' W ∘ precomp hB W)
        ( precomp f' W ∘ precomp h' W)
    precomp-front-left-inv-whisker-f' =
      precomp-coherence-square-maps
        ( hB ∘ f')
        ( h' ∘ f')
        ( h)
        ( hD)
        ( inv-htpy front-left ·r f')
        ( W)
    precomp-h-whisker-back-left-inv :
      coherence-square-maps
        ( precomp f W ∘ precomp h W)
        ( precomp hB W ∘ precomp h W)
        ( precomp hA W)
        ( precomp f' W)
    precomp-h-whisker-back-left-inv =
      precomp-coherence-square-maps hA f'
        ( h ∘ f)
        ( h ∘ hB)
        ( h ·l inv-htpy back-left)
        ( W)
    precomp-bottom-whisker-hA :
      coherence-square-maps
        ( precomp k W)
        ( precomp h W)
        ( precomp hA W ∘ precomp g W)
        ( precomp hA W ∘ precomp f W)
    precomp-bottom-whisker-hA =
      precomp-coherence-square-maps
        ( g ∘ hA)
        ( f ∘ hA)
        ( k)
        ( h)
        ( bottom ·r hA)
        ( W)
    precomp-hD-whisker-top :
      coherence-square-maps
        ( precomp k' W ∘ precomp hD W)
        ( precomp h' W ∘ precomp hD W)
        ( precomp g' W)
        ( precomp f' W)
    precomp-hD-whisker-top =
      precomp-coherence-square-maps g' f'
        ( hD ∘ k')
        ( hD ∘ h')
        ( hD ·l top)
        ( W)
    precomp-front-right-inv-whisker-g' :
      coherence-square-maps
        ( precomp k W)
        ( precomp hD W)
        ( precomp g' W ∘ precomp hC W)
        ( precomp g' W ∘ precomp k' W)
    precomp-front-right-inv-whisker-g' =
      precomp-coherence-square-maps
        ( hC ∘ g')
        ( k' ∘ g')
        ( k)
        ( hD)
        ( inv-htpy front-right ·r g')
        ( W)
    precomp-k-whisker-back-right-inv :
      coherence-square-maps
        ( precomp g W ∘ precomp k W)
        ( precomp hC W ∘ precomp k W)
        ( precomp hA W)
        ( precomp g' W)
    precomp-k-whisker-back-right-inv =
      precomp-coherence-square-maps hA g'
        ( k ∘ g)
        ( k ∘ hC)
        ( k ·l inv-htpy back-right)
        ( W)
```
