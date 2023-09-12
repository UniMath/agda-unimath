# Commuting squares of maps

```agda
module foundation.commuting-squares-of-maps where

open import foundation-core.commuting-squares-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.function-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Properties

### Composing and inverting squares horizontally and vertically

If the horizontal/vertical maps in a commuting square are both equivalences,
then the square remains commuting if we invert those equivalences.

```agda
coherence-square-inv-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A → X) (right : B → Y) (bottom : X ≃ Y) →
  coherence-square-maps (map-equiv top) left right (map-equiv bottom) →
  coherence-square-maps (map-inv-equiv top) right left (map-inv-equiv bottom)
coherence-square-inv-horizontal top left right bottom H b =
  map-eq-transpose-equiv' bottom
    ( ( ap right (inv (is-section-map-inv-equiv top b))) ∙
      ( inv (H (map-inv-equiv top b))))

coherence-square-inv-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A ≃ X) (right : B ≃ Y) (bottom : X → Y) →
  coherence-square-maps top (map-equiv left) (map-equiv right) bottom →
  coherence-square-maps bottom (map-inv-equiv left) (map-inv-equiv right) top
coherence-square-inv-vertical top left right bottom H x =
  map-eq-transpose-equiv right
    ( ( inv (H (map-inv-equiv left x))) ∙
      ( ap bottom (is-section-map-inv-equiv left x)))

coherence-square-inv-all :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A ≃ X) (right : B ≃ Y) (bottom : X ≃ Y) →
  coherence-square-maps
    ( map-equiv top)
    ( map-equiv left)
    ( map-equiv right)
    ( map-equiv bottom) →
  coherence-square-maps
    ( map-inv-equiv bottom)
    ( map-inv-equiv right)
    ( map-inv-equiv left)
    ( map-inv-equiv top)
coherence-square-inv-all top left right bottom H =
  coherence-square-inv-vertical
    ( map-inv-equiv top)
    ( right)
    ( left)
    ( map-inv-equiv bottom)
    ( coherence-square-inv-horizontal
      ( top)
      ( map-equiv left)
      ( map-equiv right)
      ( bottom)
      ( H))
```

### Any commuting square of maps induces a commuting square of function spaces

```agda
precomp-coherence-square-maps :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D) →
  coherence-square-maps top left right bottom → (X : UU l5) →
  coherence-square-maps
    ( precomp right X)
    ( precomp bottom X)
    ( precomp top X)
    ( precomp left X)
precomp-coherence-square-maps top leeft right bottom H X =
  htpy-precomp H X
```

### Distributivity of pasting squares and transposing by precomposition

Given two commuting squares which can be composed horizontally (vertically), we
know that composing them and then transposing them by precomposition gives the
same homotopies as first transposing the squares and then composing them.

```text
      tl       tr                tr ∘ tl
  A -----> B -----> C         A --------> C
  |        |        |         |           |
l |       m|        | r |->  l|          r|
  |   H    |   K    |         |   H | K   |
  v        v        v         v           v
  X -----> Y -----> Z         X --------> Z
      bl       br                br ∘ bl

         -                          -
         |                          |
         v                          v

           -∘r
    W^Z ------> W^C
     |           |
-∘br |    W^K    | -∘tr           W^(H | K)
     |           |
     v     -∘m   v                   ~
    W^Y ------> W^B   |->
     |           |                  W^K
-∘bl |    W^H    | -∘tl             ---
     |           |                  W^H
     v           v
    W^X ------> W^A
          -∘l
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( W : UU l7)
  where

  distributive-precomp-pasting-horizontal-coherence-square-maps :
    ( top-left : A → B) (top-right : B → C)
    ( left : A → X) (middle : B → Y) (right : C → Z)
    ( bottom-left : X → Y) (bottom-right : Y → Z) →
    ( H : coherence-square-maps top-left left middle bottom-left) →
    ( K : coherence-square-maps top-right middle right bottom-right) →
    precomp-coherence-square-maps
      ( top-right ∘ top-left)
      ( left)
      ( right)
      ( bottom-right ∘ bottom-left)
      ( pasting-horizontal-coherence-square-maps
        ( top-left)
        ( top-right)
        ( left)
        ( middle)
        ( right)
        ( bottom-left)
        ( bottom-right)
        ( H)
        ( K))
      ( W) ~
    pasting-vertical-coherence-square-maps
      ( precomp right W)
      ( precomp bottom-right W)
      ( precomp top-right W)
      ( precomp middle W)
      ( precomp bottom-left W)
      ( precomp top-left W)
      ( precomp left W)
      ( precomp-coherence-square-maps
        ( top-right)
        ( middle)
        ( right)
        ( bottom-right)
        ( K)
        ( W))
      ( precomp-coherence-square-maps
        ( top-left)
        ( left)
        ( middle)
        ( bottom-left)
        ( H)
        ( W))
  distributive-precomp-pasting-horizontal-coherence-square-maps
    ( top-left)
    ( top-right)
    ( left)
    ( middle)
    ( right)
    ( bottom-left)
    ( bottom-right)
    ( H)
    ( K)
    ( h) =
    equational-reasoning
      eq-htpy
        ( h ·l ((bottom-right ·l H) ∙h (K ·r top-left)))
      ＝ eq-htpy
          ( (h ·l (bottom-right ·l H)) ∙h ((h ·l K) ·r top-left))
        by
        ap
          ( eq-htpy)
          ( eq-htpy
            ( distributive-left-whisk-concat-htpy
              ( h)
              ( bottom-right ·l H)
              ( K ·r top-left)))
      ＝ eq-htpy
          ( h ·l (bottom-right ·l H)) ∙
        eq-htpy
          ( (h ·l K) ·r top-left)
        by
        eq-htpy-concat-htpy
          ( h ·l (bottom-right ·l H))
          ( (h ·l K) ·r top-left)
      ＝ eq-htpy
          ( (h ∘ bottom-right) ·l H) ∙
          ap
            ( precomp top-left W)
            ( eq-htpy (h ·l K))
        by
        ap-binary
          ( λ L q → eq-htpy L ∙ q)
          ( eq-htpy (associative-left-whisk-comp h bottom-right H))
          ( compute-eq-htpy-right-whisk
            ( top-left)
            ( h ·l K))

  distributive-precomp-pasting-vertical-coherence-square-maps :
    ( top : A → X) (left-top : A → B) (right-top : X → Y) (middle : B → Y) →
    ( left-bottom : B → C) (right-bottom : Y → Z) (bottom : C → Z) →
    ( H : coherence-square-maps top left-top right-top middle) →
    ( K : coherence-square-maps middle left-bottom right-bottom bottom) →
    precomp-coherence-square-maps
      ( top)
      ( left-bottom ∘ left-top)
      ( right-bottom ∘ right-top)
      ( bottom)
      ( pasting-vertical-coherence-square-maps
        ( top)
        ( left-top)
        ( right-top)
        ( middle)
        ( left-bottom)
        ( right-bottom)
        ( bottom)
        ( H)
        ( K))
      ( W) ~
    pasting-horizontal-coherence-square-maps
      ( precomp right-bottom W)
      ( precomp right-top W)
      ( precomp bottom W)
      ( precomp middle W)
      ( precomp top W)
      ( precomp left-bottom W)
      ( precomp left-top W)
      ( precomp-coherence-square-maps
        ( middle)
        ( left-bottom)
        ( right-bottom)
        ( bottom)
        ( K)
        ( W))
      ( precomp-coherence-square-maps
        ( top)
        ( left-top)
        ( right-top)
        ( middle)
        ( H)
        ( W))
  distributive-precomp-pasting-vertical-coherence-square-maps
    ( top)
    ( left-top)
    ( right-top)
    ( middle)
    ( left-bottom)
    ( right-bottom)
    ( bottom)
    ( H)
    ( K)
    ( h) =
    equational-reasoning
      eq-htpy
        (h ·l ((K ·r left-top) ∙h (right-bottom ·l H)))
      ＝ eq-htpy
          ( ((h ·l K) ·r left-top) ∙h (h ·l (right-bottom ·l H)))
        by
        ap
          ( eq-htpy)
          ( eq-htpy
            ( distributive-left-whisk-concat-htpy
            ( h)
            ( K ·r left-top)
            ( right-bottom ·l H)))
      ＝ eq-htpy
          ( (h ·l K) ·r left-top) ∙
        eq-htpy
          ( h ·l (right-bottom ·l H))
        by
        eq-htpy-concat-htpy
          ( (h ·l K) ·r left-top)
          ( h ·l (right-bottom ·l H))
      ＝ ap
          ( precomp left-top W)
          ( eq-htpy (h ·l K)) ∙
        eq-htpy
          ( (h ∘ right-bottom) ·l H)
        by
        ap-binary
          ( λ p L → p ∙ eq-htpy L)
          ( compute-eq-htpy-right-whisk left-top (h ·l K))
          ( eq-htpy (associative-left-whisk-comp h right-bottom H))
```
