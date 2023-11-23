# Commuting cubes of maps

```agda
module foundation.commuting-cubes-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-hexagons-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

We specify the type of the homotopy witnessing that a cube commutes. Imagine
that the cube is presented as a lattice

```text
            A'
          / | \
         /  |  \
        /   |   \
       B'   A    C'
       |\ /   \ /|
       | \     / |
       |/ \   / \|
       B    D'   C'
        \   |   /
         \  |  /
          \ | /
            D
```

with all maps pointing in the downwards direction. Presented in this way, a cube
of maps has a top face, a back-left face, a back-right face, a front-left face,
a front-right face, and a bottom face, all of which are homotopies. An element
of type `coherence-cube-maps` is a homotopy filling the cube.

## Definition

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
    ( ap (λ t → t ∙ (ap h (back-left a')))
      ( ap (λ t' → t' ∙ inv (bottom (hA a')))
        ( ap-inv k (back-right a')))) ∙
    ( ( hexagon-rotate-120
        ( ap h (back-left a'))
        ( front-left (f' a'))
        ( ap hD (top a'))
        ( bottom (hA a'))
        ( ap k (back-right a'))
        ( front-right (g' a'))
        ( c a')) ∙
      ( inv
        ( ap (λ t → (front-right (g' a')) ∙ t)
          ( ap (λ t' → t' ∙ inv (front-left (f' a')))
            ( ap-inv hD (top a'))))))

  coherence-cube-maps-rotate-240 :
    coherence-cube-maps h' hB hD h g' hA hC g f' k' f k
      ( inv-htpy back-right)
      ( top)
      ( inv-htpy back-left)
      ( inv-htpy front-right)
      ( bottom)
      ( inv-htpy front-left)
  coherence-cube-maps-rotate-240 a' =
    ( ap (λ t → _ ∙ t) (ap-inv k (back-right a'))) ∙
    ( ( hexagon-rotate-240
        ( ap h (back-left a'))
        ( front-left (f' a'))
        ( ap hD (top a'))
        ( bottom (hA a'))
        ( ap k (back-right a'))
        ( front-right (g' a'))
        ( c a')) ∙
      ( inv
        ( ap
          ( λ t → inv (front-left (f' a')) ∙ t)
          ( ap (λ t' → t' ∙ _) (ap-inv h (back-left a'))))))

  coherence-cube-maps-mirror-A :
    coherence-cube-maps g f k h g' f' k' h' hA hC hB hD
      ( inv-htpy top)
      ( back-right)
      ( back-left)
      ( front-right)
      ( front-left)
      ( inv-htpy bottom)
  coherence-cube-maps-mirror-A a' =
    ( ap (λ t → _ ∙ t) (ap-inv hD (top a'))) ∙
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
    ( ap (λ t → t ∙ (ap k (back-right a')))
      ( ap (λ t → t ∙ _) (ap-inv h (back-left a')))) ∙
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
    ( ( ap (λ t → _ ∙ t) (ap-inv h (back-left a'))) ∙
      ( ( hexagon-mirror-C
          ( ap h (back-left a'))
          ( front-left (f' a'))
          ( ap hD (top a'))
          ( bottom (hA a'))
          ( ap k (back-right a'))
          ( front-right (g' a'))
          ( c a')) ∙
        ( inv
          ( ap
            ( λ t → inv (front-right (g' a')) ∙ t)
            ( ap (λ t' → t' ∙ _) (ap-inv k (back-right a')))))))
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
    ( λ a' →
      ( ap
        ( concat
          ( rectangle-left-cube a')
          ( hD (k' (g' a'))))
        ( right-unit))) ∙h
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
        ( h ·l (inv-htpy back-left))
        ( inv-htpy (h ·l back-left))
        ( _)
        ( left-whisk-inv-htpy h back-left)) ∙h
      ( inv-htpy-left-transpose-htpy-concat (h ·l back-left) _ _
        ( ( (inv-htpy-assoc-htpy (h ·l back-left) (front-left ·r f') _) ∙h
            ( ( inv-htpy-assoc-htpy
                ( (h ·l back-left) ∙h (front-left ·r f'))
                ( hD ·l top)
                ( (inv-htpy front-right) ·r g')) ∙h
              ( inv-htpy-right-transpose-htpy-concat _ (front-right ·r g') _
                ( (assoc-htpy (bottom ·r hA) _ _) ∙h (inv-htpy c))))) ∙h
          ( ap-concat-htpy (bottom ·r hA) _ _ inv-htpy-right-unit-htpy))))
```

### Any commuting cube of maps induces a commuting cube of function spaces

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
      ~ ( precomp-front-left-inv-whisk-f') ∙h
        ( precomp-h-whisk-back-left-inv) ∙h
        ( precomp-bottom-whisk-hA)
        by
        inv-htpy
          ( horizontal-concat-htpy²
            ( horizontal-concat-htpy²
              ( distributive-precomp-right-whisk-coherence-square-maps W hB h' h
                ( hD)
                ( inv-htpy front-left)
                ( f'))
              ( distributive-precomp-left-whisk-coherence-square-maps W hA f' f
                ( hB)
                ( inv-htpy back-left)
                ( h)))
            ( distributive-precomp-right-whisk-coherence-square-maps W g f k h
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
      ~ ( precomp-hD-whisk-top) ∙h
        ( ( precomp-front-right-inv-whisk-g') ∙h
          ( precomp-k-whisk-back-right-inv))
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
          ( distributive-precomp-left-whisk-coherence-square-maps W g' f' k' h'
            ( top)
            ( hD))
          ( horizontal-concat-htpy²
            ( distributive-precomp-right-whisk-coherence-square-maps W hC k' k
              ( hD)
              ( inv-htpy front-right)
              ( g'))
            ( distributive-precomp-left-whisk-coherence-square-maps W hA g' g hC
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
    precomp-front-left-inv-whisk-f' :
      coherence-square-maps
        ( precomp h W)
        ( precomp hD W)
        ( precomp f' W ∘ precomp hB W)
        ( precomp f' W ∘ precomp h' W)
    precomp-front-left-inv-whisk-f' =
      precomp-coherence-square-maps
        ( hB ∘ f')
        ( h' ∘ f')
        ( h)
        ( hD)
        ( inv-htpy front-left ·r f')
        ( W)
    precomp-h-whisk-back-left-inv :
      coherence-square-maps
        ( precomp f W ∘ precomp h W)
        ( precomp hB W ∘ precomp h W)
        ( precomp hA W)
        ( precomp f' W)
    precomp-h-whisk-back-left-inv =
      precomp-coherence-square-maps hA f'
        ( h ∘ f)
        ( h ∘ hB)
        ( h ·l inv-htpy back-left)
        ( W)
    precomp-bottom-whisk-hA :
      coherence-square-maps
        ( precomp k W)
        ( precomp h W)
        ( precomp hA W ∘ precomp g W)
        ( precomp hA W ∘ precomp f W)
    precomp-bottom-whisk-hA =
      precomp-coherence-square-maps
        ( g ∘ hA)
        ( f ∘ hA)
        ( k)
        ( h)
        ( bottom ·r hA)
        ( W)
    precomp-hD-whisk-top :
      coherence-square-maps
        ( precomp k' W ∘ precomp hD W)
        ( precomp h' W ∘ precomp hD W)
        ( precomp g' W)
        ( precomp f' W)
    precomp-hD-whisk-top =
      precomp-coherence-square-maps g' f'
        ( hD ∘ k')
        ( hD ∘ h')
        ( hD ·l top)
        ( W)
    precomp-front-right-inv-whisk-g' :
      coherence-square-maps
        ( precomp k W)
        ( precomp hD W)
        ( precomp g' W ∘ precomp hC W)
        ( precomp g' W ∘ precomp k' W)
    precomp-front-right-inv-whisk-g' =
      precomp-coherence-square-maps
        ( hC ∘ g')
        ( k' ∘ g')
        ( k)
        ( hD)
        ( inv-htpy front-right ·r g')
        ( W)
    precomp-k-whisk-back-right-inv :
      coherence-square-maps
        ( precomp g W ∘ precomp k W)
        ( precomp hC W ∘ precomp k W)
        ( precomp hA W)
        ( precomp g' W)
    precomp-k-whisk-back-right-inv =
      precomp-coherence-square-maps hA g'
        ( k ∘ g)
        ( k ∘ hC)
        ( k ·l inv-htpy back-right)
        ( W)
```
