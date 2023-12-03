# Commuting squares of maps

```agda
module foundation.commuting-squares-of-maps where

open import foundation-core.commuting-squares-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.path-algebra
open import foundation.precomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.commuting-prisms-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Definitions

### Pasting commuting triangles into commuting squares along homotopic diagonals

Two [commuting triangles](foundation-core.commuting-triangles-of-maps.md)

```text
   A         A --> X
  | \         \    |
  |  \ H  L  K \   |
  |   \         \  |
  v    v         v v
  B --> Y         Y
```

with a [homotopic](foundation-core.homotopies.md) diagonal may be pasted into a
commuting square

```text
  A -----> X
  |        |
  |        |
  v        v
  B -----> Y.
```

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  ( top : A → X) (left : A → B) (right : X → Y) (bottom : B → Y)
  where

  coherence-square-htpy-coherence-triangles-maps :
    { diagonal-left diagonal-right : A → Y} →
    diagonal-left ~ diagonal-right →
    coherence-triangle-maps' diagonal-left bottom left →
    coherence-triangle-maps diagonal-right right top →
    coherence-square-maps top left right bottom
  coherence-square-htpy-coherence-triangles-maps L H K = (H ∙h L) ∙h K

  coherence-square-htpy-coherence-triangles-maps' :
    { diagonal-left diagonal-right : A → Y} →
    diagonal-left ~ diagonal-right →
    coherence-triangle-maps' diagonal-left bottom left →
    coherence-triangle-maps diagonal-right right top →
    coherence-square-maps top left right bottom
  coherence-square-htpy-coherence-triangles-maps' L H K = H ∙h (L ∙h K)

  coherence-square-coherence-triangles-maps :
    ( diagonal : A → Y) →
    coherence-triangle-maps' diagonal bottom left →
    coherence-triangle-maps diagonal right top →
    coherence-square-maps top left right bottom
  coherence-square-coherence-triangles-maps diagonal H K = H ∙h K

  compute-coherence-square-refl-htpy-coherence-triangles-maps :
    ( diagonal : A → Y) →
    ( H : coherence-triangle-maps' diagonal bottom left) →
    ( K : coherence-triangle-maps diagonal right top) →
    ( coherence-square-htpy-coherence-triangles-maps refl-htpy H K) ~
    ( coherence-square-coherence-triangles-maps diagonal H K)
  compute-coherence-square-refl-htpy-coherence-triangles-maps diagonal H K x =
    ap (_∙ K x) right-unit
```

### Inverting squares horizontally and vertically

If the horizontal/vertical maps in a commuting square are both
[equivalences](foundation-core.equivalences.md),
then the square remains commuting if we invert those equivalences.

```agda
coherence-square-inv-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A → X) (right : B → Y) (bottom : X ≃ Y) →
  coherence-square-maps (map-equiv top) left right (map-equiv bottom) →
  coherence-square-maps (map-inv-equiv top) right left (map-inv-equiv bottom)
coherence-square-inv-horizontal top left right bottom H b =
  map-eq-transpose-equiv-inv
    ( bottom)
    ( ( ap right (inv (is-section-map-inv-equiv top b))) ∙
      ( inv (H (map-inv-equiv top b))))

coherence-square-inv-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A ≃ X) (right : B ≃ Y) (bottom : X → Y) →
  coherence-square-maps top (map-equiv left) (map-equiv right) bottom →
  coherence-square-maps bottom (map-inv-equiv left) (map-inv-equiv right) top
coherence-square-inv-vertical top left right bottom H x =
  map-eq-transpose-equiv
    ( right)
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
precomp-coherence-square-maps top left right bottom H X =
  htpy-precomp H X
```

## Properties

### Taking vertical inversions of squares is an inverse operation

Vertical composition of a square with the square obtained by inverting the
vertical maps fits into a [prism](foundation.commuting-prisms-of-maps.md) with
the reflexivity square.

The analogous result for horizontal composition remains to be formalized.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  ( top : A → X) (left : A ≃ B) (right : X ≃ Y) (bottom : B → Y)
  where

  left-inverse-law-pasting-vertical-coherence-square-maps :
    ( H : coherence-square-maps top (map-equiv left) (map-equiv right) bottom) →
    horizontal-coherence-prism-maps
      ( top)
      ( map-equiv left)
      ( map-equiv right)
      ( bottom)
      ( map-inv-equiv left)
      ( map-inv-equiv right)
      ( top)
      ( id)
      ( id)
      ( is-retraction-map-inv-equiv left)
      ( H)
      ( coherence-square-inv-vertical top left right bottom H)
      ( refl-htpy)
      ( is-retraction-map-inv-equiv right)
  left-inverse-law-pasting-vertical-coherence-square-maps H a =
    ( right-unit) ∙
    ( inv
      ( ( ap
          ( λ q →
            ( q ∙ ap (map-inv-equiv right) (H a)) ∙
            ( is-retraction-map-inv-equiv right (top a)))
          ( triangle-eq-transpose-equiv-concat
            ( right)
            ( inv (H (map-inv-equiv left (map-equiv left a))))
            ( ap bottom (is-section-map-inv-equiv left (map-equiv left a))))) ∙
        ( assoc
          ( ( map-eq-transpose-equiv
              ( right)
              ( inv (H (map-inv-equiv left (map-equiv left a))))) ∙
            ( ap
              ( map-inv-equiv right)
              ( ap bottom (is-section-map-inv-equiv left (map-equiv left a)))))
          ( ap (map-inv-equiv right) (H a))
          ( is-retraction-map-inv-equiv right (top a))) ∙
        ( left-whisk-square-identification
          ( map-eq-transpose-equiv
            ( right)
            ( inv (H (map-inv-equiv left (map-equiv left a)))))
          ( inv
            ( coherence-square-identifications-comp-vertical
              { p-left =
                  ap
                    ( map-inv-equiv right)
                    ( H (map-inv-equiv left (map-equiv left a)))}
              { p-top =
                  ap
                    ( map-inv-equiv right)
                    ( ap
                      ( bottom)
                      ( is-section-map-inv-equiv left (map-equiv left a)))}
              { q-bottom = ap top (is-retraction-map-inv-equiv left a)}
              ( coherence-square-identifications-top-paste
                ( ap
                  ( map-inv-equiv right)
                  ( H (map-inv-equiv left (map-equiv left a))))
                ( _)
                ( _)
                ( _)
                ( inv
                  ( ap
                    ( ap (map-inv-equiv right))
                    ( ( ap (ap bottom) (coherence-map-inv-equiv left a)) ∙
                      ( inv
                        ( ap-comp
                          ( bottom)
                          ( map-equiv left)
                          ( is-retraction-map-inv-equiv left a))))))
                ( coherence-square-identifications-ap
                  ( map-inv-equiv right)
                  ( ap
                    ( bottom ∘ map-equiv left)
                    ( is-retraction-map-inv-equiv left a))
                  ( H (map-inv-equiv left (map-equiv left a)))
                  ( H a)
                  ( ap
                    ( map-equiv right ∘ top)
                    ( is-retraction-map-inv-equiv left a))
                  ( nat-htpy H (is-retraction-map-inv-equiv left a))))
              ( coherence-square-identifications-top-paste _
                ( ap top (is-retraction-map-inv-equiv left a))
                ( _)
                ( _)
                ( ap-comp
                  ( map-inv-equiv right)
                  ( map-equiv right ∘ top)
                  ( is-retraction-map-inv-equiv left a))
                ( nat-htpy
                  ( is-retraction-map-inv-equiv right ·r top)
                  ( is-retraction-map-inv-equiv left a)))))) ∙
        ( ap
          ( _∙ ap top (is-retraction-map-inv-equiv left a))
          ( right-inverse-eq-transpose-equiv
            ( right)
            ( H (map-inv-equiv left (map-equiv left a)))))))

  right-inverse-law-pasting-vertical-coherence-square-maps :
    ( H : coherence-square-maps top (map-equiv left) (map-equiv right) bottom) →
    horizontal-coherence-prism-maps
      ( bottom)
      ( map-inv-equiv left)
      ( map-inv-equiv right)
      ( top)
      ( map-equiv left)
      ( map-equiv right)
      ( bottom)
      ( id)
      ( id)
      ( is-section-map-inv-equiv left)
      ( coherence-square-inv-vertical top left right bottom H)
      ( H)
      ( refl-htpy)
      ( is-section-map-inv-equiv right)
  right-inverse-law-pasting-vertical-coherence-square-maps H a =
    ( right-unit) ∙
    ( inv
      ( ( assoc
          ( H (map-inv-equiv left a))
          ( ap
            ( map-equiv right)
            ( coherence-square-inv-vertical top left right bottom H a))
          ( is-section-map-inv-equiv right (bottom a))) ∙
        ( ap
          ( H (map-inv-equiv left a) ∙_)
          ( triangle-eq-transpose-equiv
            ( right)
            ( ( inv (H (map-inv-equiv left a))) ∙
              ( ap bottom (is-section-map-inv-equiv left a))))) ∙
        ( is-retraction-left-concat-inv
          ( H (map-inv-equiv left a))
          ( ap bottom (is-section-map-inv-equiv left a)))))
```

### Associativity of vertical pasting

The proof of associativity of horizontal pasting may be found in
[`foundation-core.commuting-squares-of-maps`](foundation-core.commuting-squares-of-maps.md).

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  { X : UU l5} {Y : UU l6} {Z : UU l7} {W : UU l8}
  ( top : A → X) (top-left : A → B) (top-right : X → Y)
  ( mid-top : B → Y) (mid-left : B → C) (mid-right : Y → Z) (mid-bottom : C → Z)
  ( bottom-left : C → D) (bottom-right : Z → W) (bottom : D → W)
  ( sq-top : coherence-square-maps top top-left top-right mid-top)
  ( sq-mid : coherence-square-maps mid-top mid-left mid-right mid-bottom)
  ( sq-bottom :
      coherence-square-maps mid-bottom bottom-left bottom-right bottom)
  where

  assoc-pasting-vertical-coherence-square-maps :
    pasting-vertical-coherence-square-maps
      ( top)
      ( mid-left ∘ top-left)
      ( mid-right ∘ top-right)
      ( mid-bottom)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( pasting-vertical-coherence-square-maps
        ( top)
        ( top-left)
        ( top-right)
        ( mid-top)
        ( mid-left)
        ( mid-right)
        ( mid-bottom)
        ( sq-top)
        ( sq-mid))
      ( sq-bottom) ~
    pasting-vertical-coherence-square-maps
      ( top)
      ( top-left)
      ( top-right)
      ( mid-top)
      ( bottom-left ∘ mid-left)
      ( bottom-right ∘ mid-right)
      ( bottom)
      ( sq-top)
      ( pasting-vertical-coherence-square-maps
        ( mid-top)
        ( mid-left)
        ( mid-right)
        ( mid-bottom)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( sq-mid)
        ( sq-bottom))
  assoc-pasting-vertical-coherence-square-maps =
    ( ap-concat-htpy
      ( sq-bottom ·r mid-left ·r top-left)
      ( ( distributive-left-whisk-concat-htpy
          ( bottom-right)
          ( sq-mid ·r top-left)
          ( mid-right ·l sq-top)) ∙h
        ( ap-concat-htpy
          ( bottom-right ·l (sq-mid ·r top-left))
          ( associative-left-whisk-comp bottom-right mid-right sq-top)))) ∙h
    ( inv-htpy-assoc-htpy
      ( sq-bottom ·r mid-left ·r top-left)
      ( bottom-right ·l (sq-mid ·r top-left))
      ( ( bottom-right ∘ mid-right) ·l sq-top))
```

### Naturality of commuting squares of maps with respect to identifications

Similarly to the naturality square of homotopies and
[identifications](foundation-core.identity-types.md), we have a naturality
square of coherence squares of maps and identifications:

```text
           ap f (ap g p)
  f (g x) =============== f (g y)
     ‖                       ‖
 H x ‖                       ‖ H y
     ‖                       ‖
  h (k x) =============== h (k y)
           ap h (ap k p)           .
```

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  ( top : A → B) (left : A → C) (right : B → D) (bottom : C → D)
  ( H : coherence-square-maps top left right bottom)
  where

  nat-coherence-square-maps :
    { x y : A} (p : x ＝ y) →
    coherence-square-identifications
      ( ap bottom (ap left p))
      ( H x)
      ( H y)
      ( ap right (ap top p))
  nat-coherence-square-maps refl = right-unit
```

As a corollary, whenever we have two coherence squares touching at a vertex:

```text
  A -----> B
  |        |
  |   H ⇗  |
  V        V
  C -----> D -----> X
           |        |
           |   K ⇗  |
           V        V
           Y -----> Z ,
```

there is a homotopy between first applying `H`, then `K`, and first applying
`K`, then `H`.

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  { X : UU l5} {Y : UU l6} {Z : UU l7}
  ( top : A → B) (left : A → C) (mid-top : B → D) (mid-left : C → D)
  ( mid-right : D → X) (mid-bottom : D → Y) (right : X → Z) (bottom : Y → Z)
  ( H : coherence-square-maps top left mid-top mid-left)
  ( K : coherence-square-maps mid-right mid-bottom right bottom)
  where

  swap-nat-coherence-square-maps :
    coherence-square-homotopies
      ( bottom ·l mid-bottom ·l H)
      ( K ·r mid-left ·r left)
      ( K ·r mid-top ·r top)
      ( right ·l mid-right ·l H)
  swap-nat-coherence-square-maps x =
    nat-coherence-square-maps mid-right mid-bottom right bottom K (H x)
```

### Commutativity of horizontal and vertical pasting

Given a square of commuting squares, like so:

```text
  A -----> B -----> C
  |        |        |
  |    ⇗   |    ⇗   |
  V        V        V
  X -----> Y -----> Z
  |        |        |
  |    ⇗   |    ⇗   |
  V        V        V
  M -----> N -----> O ,
```

we have two choices for obtaining the outer commuting square — either by first
vertically composing the smaller squares, and then horizontally composing the
newly created rectangles, or by first horizontally composing the squares, and
then vertically composing the rectangles.

The following lemma states that the big squares obtained by these two
compositions are again homotopic. Diagramatically, we have

```text
 H | K   H | K
 ----- ~ --|--
 L | T   L | T .
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  { M : UU l7} {N : UU l8} {O : UU l9}
  ( top-left : A → B) (top-right : B → C)
  ( left-top : A → X) (mid-top : B → Y) (right-top : C → Z)
  ( mid-left : X → Y) (mid-right : Y → Z)
  ( left-bottom : X → M) (mid-bottom : Y → N) (right-bottom : Z → O)
  ( bottom-left : M → N) (bottom-right : N → O)
  ( sq-left-top : coherence-square-maps top-left left-top mid-top mid-left)
  ( sq-right-top : coherence-square-maps top-right mid-top right-top mid-right)
  ( sq-left-bottom :
      coherence-square-maps mid-left left-bottom mid-bottom bottom-left)
  ( sq-right-bottom :
      coherence-square-maps mid-right mid-bottom right-bottom bottom-right)
  where

  commutative-pasting-vertical-pasting-horizontal-coherence-square-maps :
    ( pasting-horizontal-coherence-square-maps
      ( top-left)
      ( top-right)
      ( left-bottom ∘ left-top)
      ( mid-bottom ∘ mid-top)
      ( right-bottom ∘ right-top)
      ( bottom-left)
      ( bottom-right)
      ( pasting-vertical-coherence-square-maps
        ( top-left)
        ( left-top)
        ( mid-top)
        ( mid-left)
        ( left-bottom)
        ( mid-bottom)
        ( bottom-left)
        ( sq-left-top)
        ( sq-left-bottom))
      ( pasting-vertical-coherence-square-maps
        ( top-right)
        ( mid-top)
        ( right-top)
        ( mid-right)
        ( mid-bottom)
        ( right-bottom)
        ( bottom-right)
        ( sq-right-top)
        ( sq-right-bottom))) ~
    ( pasting-vertical-coherence-square-maps
      ( top-right ∘ top-left)
      ( left-top)
      ( right-top)
      ( mid-right ∘ mid-left)
      ( left-bottom)
      ( right-bottom)
      ( bottom-right ∘ bottom-left)
      ( pasting-horizontal-coherence-square-maps
        ( top-left)
        ( top-right)
        ( left-top)
        ( mid-top)
        ( right-top)
        ( mid-left)
        ( mid-right)
        ( sq-left-top)
        ( sq-right-top))
      ( pasting-horizontal-coherence-square-maps
        ( mid-left)
        ( mid-right)
        ( left-bottom)
        ( mid-bottom)
        ( right-bottom)
        ( bottom-left)
        ( bottom-right)
        ( sq-left-bottom)
        ( sq-right-bottom)))
  commutative-pasting-vertical-pasting-horizontal-coherence-square-maps =
    ( ap-concat-htpy' _
      ( distributive-left-whisk-concat-htpy
        ( bottom-right)
        ( sq-left-bottom ·r left-top)
        ( mid-bottom ·l sq-left-top)) ∙h
      ( both-whisk-square-htpy
        ( bottom-right ·l (sq-left-bottom ·r left-top))
        ( right-bottom ·l (sq-right-top ·r top-left))
        ( inv-htpy
          ( swap-nat-coherence-square-maps
            ( top-left)
            ( left-top)
            ( mid-top)
            ( mid-left)
            ( mid-right)
            ( mid-bottom)
            ( right-bottom)
            ( bottom-right)
            ( sq-left-top)
            ( sq-right-bottom))))) ∙h
      ( ap-concat-htpy _
        ( inv-htpy
          ( distributive-left-whisk-concat-htpy
            ( right-bottom)
            ( mid-right ·l sq-left-top)
            ( sq-right-top ·r top-left))))
```

### Distributivity of pasting squares and transposing by precomposition

Given two commuting squares which can be composed horizontally (vertically), we
know that composing them and then transposing them by precomposition gives a
homotopy that is homotopic to first transposing the squares and then composing
them.

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

### Transposing by precomposition of whiskered squares

Taking a square of the form

```text
      f        top
  X -----> A -----> B
           |        |
      left |   H    | right
           v        v
           C -----> D
             bottom
```

and transposing it by precomposition results in the square

```text
  W^D -----> W^B
   |          |
   |   W^H    |
   v          v   -∘f
  W^C -----> W^A -----> W^X
```

This fact can be written as distribution of right whiskering over transposition:
`W^(H ·r f) = W^f ·l W^H`.

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {X : UU l5} (W : UU l6)
  ( top : A → B) (left : A → C) (right : B → D) (bottom : C → D)
  ( H : coherence-square-maps top left right bottom)
  where

  distributive-precomp-right-whisk-coherence-square-maps :
    ( f : X → A) →
    precomp-coherence-square-maps
      ( top ∘ f)
      ( left ∘ f)
      ( right)
      ( bottom)
      ( H ·r f)
      ( W) ~
    ( ( precomp f W) ·l
      ( precomp-coherence-square-maps top left right bottom H W))
  distributive-precomp-right-whisk-coherence-square-maps f g =
    compute-eq-htpy-right-whisk f (g ·l H)
```

Similarly, we can calculate transpositions of left-whiskered squares with the
formula `W^(f ·l H) = W^H ·r W^f`.

```agda
  distributive-precomp-left-whisk-coherence-square-maps :
    ( f : D → X) →
    precomp-coherence-square-maps
      ( top)
      ( left)
      ( f ∘ right)
      ( f ∘ bottom)
      ( f ·l H)
      ( W) ~
    ( ( precomp-coherence-square-maps top left right bottom H W) ·r
      ( precomp f W))
  distributive-precomp-left-whisk-coherence-square-maps f g =
    ap eq-htpy (eq-htpy (λ a → inv (ap-comp g f (H a))))
```

### The square of function spaces induced by a composition of triangles is homotopic to the composition of induced triangles of function spaces

```agda
module _
  { l1 l2 l3 l4 l5 : Level}
  { A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} (W : UU l5)
  ( top : A → X) (left : A → B) (right : X → Y) (bottom : B → Y)
  where

  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps :
    { diagonal-left diagonal-right : A → Y} →
    ( L : diagonal-left ~ diagonal-right) →
    ( H : coherence-triangle-maps' diagonal-left bottom left) →
    ( K : coherence-triangle-maps diagonal-right right top) →
    ( precomp-coherence-square-maps
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( coherence-square-htpy-coherence-triangles-maps
        ( top)
        ( left)
        ( right)
        ( bottom)
        ( L)
        ( H)
        ( K))
      ( W)) ~
    ( coherence-square-htpy-coherence-triangles-maps
      ( precomp right W)
      ( precomp bottom W)
      ( precomp top W)
      ( precomp left W)
      ( htpy-precomp L W)
      ( precomp-coherence-triangle-maps' diagonal-left bottom left H W)
      ( precomp-coherence-triangle-maps diagonal-right right top K W))
  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps
    { diagonal-right = diagonal-right}
    ( L)
    ( H)
    ( K)
    ( h) =
    ( compute-concat-htpy-precomp (H ∙h L) K W h) ∙
    ( ap
      ( _∙ precomp-coherence-triangle-maps diagonal-right right top K W h)
      ( compute-concat-htpy-precomp H L W h))

  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps' :
    { diagonal-left diagonal-right : A → Y} →
    ( L : diagonal-left ~ diagonal-right) →
    ( H : coherence-triangle-maps' diagonal-left bottom left) →
    ( K : coherence-triangle-maps diagonal-right right top) →
    ( precomp-coherence-square-maps
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( coherence-square-htpy-coherence-triangles-maps'
        ( top)
        ( left)
        ( right)
        ( bottom)
        ( L)
        ( H)
        ( K))
      ( W)) ~
    ( coherence-square-htpy-coherence-triangles-maps'
      ( precomp right W)
      ( precomp bottom W)
      ( precomp top W)
      ( precomp left W)
      ( htpy-precomp L W)
      ( precomp-coherence-triangle-maps' diagonal-left bottom left H W)
      ( precomp-coherence-triangle-maps diagonal-right right top K W))
  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps'
    { diagonal-left = diagonal-left}
    ( L)
    ( H)
    ( K)
    ( h) =
    ( compute-concat-htpy-precomp H (L ∙h K) W h) ∙
    ( ap
      ( precomp-coherence-triangle-maps' diagonal-left bottom left H W h ∙_)
      ( compute-concat-htpy-precomp L K W h))

  distributive-precomp-coherence-square-comp-coherence-triangles-maps :
    ( diagonal : A → Y) →
    ( H : coherence-triangle-maps' diagonal bottom left) →
    ( K : coherence-triangle-maps diagonal right top) →
    ( precomp-coherence-square-maps
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( coherence-square-coherence-triangles-maps
        ( top)
        ( left)
        ( right)
        ( bottom)
        ( diagonal)
        ( H)
        ( K))
      ( W)) ~
    ( coherence-square-coherence-triangles-maps
      ( precomp right W)
      ( precomp bottom W)
      ( precomp top W)
      ( precomp left W)
      ( precomp diagonal W)
      ( precomp-coherence-triangle-maps' diagonal bottom left H W)
      ( precomp-coherence-triangle-maps diagonal right top K W))
  distributive-precomp-coherence-square-comp-coherence-triangles-maps
    ( diagonal)
    ( H)
    ( K)
    ( h) =
    compute-concat-htpy-precomp H K W h
```
