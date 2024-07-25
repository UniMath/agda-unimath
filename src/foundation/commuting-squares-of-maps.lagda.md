# Commuting squares of maps

```agda
module foundation.commuting-squares-of-maps where

open import foundation-core.commuting-squares-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-prisms-of-maps
open import foundation-core.commuting-squares-of-homotopies
open import foundation-core.commuting-squares-of-identifications
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Definitions

### Commuting squares of maps induce commuting squares of precomposition maps

Every commuting square

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y
          bottom
```

induces a commuting square of
[precomposition functions](foundation-core.precomposition-functions.md)

```text
                         precomp right S
                (A → S) -----------------> (X → S)
                   |                           |
  precomp bottom S |                           | precomp top S
                   ∨                           ∨
                (B → S) ------------------> (Y → S).
                          precomp left S
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → X) (left : A → B) (right : X → Y) (bottom : B → Y)
  where

  precomp-coherence-square-maps :
    coherence-square-maps top left right bottom →
    (S : UU l5) →
    coherence-square-maps
      ( precomp right S)
      ( precomp bottom S)
      ( precomp top S)
      ( precomp left S)
  precomp-coherence-square-maps = htpy-precomp

  precomp-coherence-square-maps' :
    coherence-square-maps' top left right bottom →
    (S : UU l5) →
    coherence-square-maps'
      ( precomp right S)
      ( precomp bottom S)
      ( precomp top S)
      ( precomp left S)
  precomp-coherence-square-maps' = htpy-precomp
```

### Commuting squares of maps induce commuting squares of postcomposition maps

Every commuting square

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y
          bottom
```

induces a commuting square of
[postcomposition functions](foundation-core.postcomposition-functions.md)

```text
                        postcomp S top
              (S → A) ------------------> (S → X)
                 |                           |
 postcomp S left |                           | postcomp S right
                 ∨                           ∨
              (S → B) ------------------> (S → Y).
                       postcomp S bottom
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → X) (left : A → B) (right : X → Y) (bottom : B → Y)
  where

  postcomp-coherence-square-maps :
    (S : UU l5) →
    coherence-square-maps top left right bottom →
    coherence-square-maps
      ( postcomp S top)
      ( postcomp S left)
      ( postcomp S right)
      ( postcomp S bottom)
  postcomp-coherence-square-maps S = htpy-postcomp S

  postcomp-coherence-square-maps' :
    (S : UU l5) →
    coherence-square-maps' top left right bottom →
    coherence-square-maps'
      ( postcomp S top)
      ( postcomp S left)
      ( postcomp S right)
      ( postcomp S bottom)
  postcomp-coherence-square-maps' S = htpy-postcomp S
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
      ( vertical-inv-equiv-coherence-square-maps top left right bottom H)
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
        ( left-whisker-concat-coherence-square-identifications
          ( map-eq-transpose-equiv
            ( right)
            ( inv (H (map-inv-equiv left (map-equiv left a)))))
          ( _)
          ( _)
          ( _)
          ( _)
          ( inv
            ( vertical-pasting-coherence-square-identifications
              ( ap
                ( map-inv-equiv right)
                ( ap
                  ( bottom)
                  ( is-section-map-inv-equiv left (map-equiv left a))))
              ( ap
                ( map-inv-equiv right)
                ( H (map-inv-equiv left (map-equiv left a))))
              ( ap (map-inv-equiv right) (H a))
              ( ap
                ( map-inv-equiv right)
                ( ap
                  ( map-equiv right ∘ top)
                  ( is-retraction-map-inv-equiv left a)))
              ( is-retraction-map-inv-equiv right
                ( top (map-inv-equiv left (map-equiv left a))))
              ( is-retraction-map-inv-equiv right (top a))
              ( ap top (is-retraction-map-inv-equiv left a))
              ( concat-top-identification-coherence-square-identifications
                ( _)
                ( ap
                  ( map-inv-equiv right)
                  ( H (map-inv-equiv left (map-equiv left a))))
                ( _)
                ( _)
                ( inv
                  ( ap
                    ( ap (map-inv-equiv right))
                    ( ( left-whisker-comp²
                        ( bottom)
                        ( coherence-map-inv-equiv left)
                        ( a)) ∙
                      ( inv
                        ( ap-comp
                          ( bottom)
                          ( map-equiv left)
                          ( is-retraction-map-inv-equiv left a))))))
                ( map-coherence-square-identifications
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
              ( concat-top-identification-coherence-square-identifications _ _ _
                ( ap top (is-retraction-map-inv-equiv left a))
                ( ap-comp
                  ( map-inv-equiv right)
                  ( map-equiv right ∘ top)
                  ( is-retraction-map-inv-equiv left a))
                ( nat-htpy
                  ( is-retraction-map-inv-equiv right ·r top)
                  ( is-retraction-map-inv-equiv left a)))))) ∙
        ( right-whisker-concat
          ( right-inverse-eq-transpose-equiv
            ( right)
            ( H (map-inv-equiv left (map-equiv left a))))
          ( ap top (is-retraction-map-inv-equiv left a)))))

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
      ( vertical-inv-equiv-coherence-square-maps top left right bottom H)
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
            ( vertical-inv-equiv-coherence-square-maps top left right bottom
              ( H)
              ( a)))
          ( is-section-map-inv-equiv right (bottom a))) ∙
        ( left-whisker-concat
          ( H (map-inv-equiv left a))
          ( triangle-eq-transpose-equiv
            ( right)
            ( ( inv (H (map-inv-equiv left a))) ∙
              ( ap bottom (is-section-map-inv-equiv left a))))) ∙
        ( is-section-inv-concat
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
      ( ( distributive-left-whisker-comp-concat
          ( bottom-right)
          ( sq-mid ·r top-left)
          ( mid-right ·l sq-top)) ∙h
        ( ap-concat-htpy
          ( bottom-right ·l (sq-mid ·r top-left))
          ( preserves-comp-left-whisker-comp
            ( bottom-right)
            ( mid-right)
            ( sq-top))))) ∙h
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
   f (g x) ---------------> f (g y)
      |                       |
  H x |                       | H y
      ∨                       ∨
   h (k x) ---------------> h (k y)
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
  ∨        ∨
  C -----> D -----> X
           |        |
           |   K ⇗  |
           ∨        ∨
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
  ∨        ∨        ∨
  X -----> Y -----> Z
  |        |        |
  |    ⇗   |    ⇗   |
  ∨        ∨        ∨
  M -----> N -----> O ,
```

we have two choices for obtaining the outer commuting square — either by first
vertically composing the smaller squares, and then horizontally composing the
newly created rectangles, or by first horizontally composing the squares, and
then vertically composing the rectangles.

The following lemma states that the big squares obtained by these two
compositions are again homotopic. Diagrammatically, we have

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
      ( distributive-left-whisker-comp-concat
        ( bottom-right)
        ( sq-left-bottom ·r left-top)
        ( mid-bottom ·l sq-left-top)) ∙h
      ( double-whisker-coherence-square-homotopies
        ( bottom-right ·l sq-left-bottom ·r left-top)
        ( sq-right-bottom ·r mid-left ·r left-top)
        ( bottom-right ·l mid-bottom ·l sq-left-top)
        ( right-bottom ·l mid-right ·l sq-left-top)
        ( sq-right-bottom ·r mid-top ·r top-left)
        ( right-bottom ·l sq-right-top ·r top-left)
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
          ( distributive-left-whisker-comp-concat
            ( right-bottom)
            ( mid-right ·l sq-left-top)
            ( sq-right-top ·r top-left))))
```

### Vertical pasting of a square with the right leg an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top : A → X) (top-left : A → B) (top-right : X → Y) (mid : B → Y)
  (bottom-left : B → C) (bottom-right : Y → Z) (bottom : C → Z)
  (K : coherence-square-maps mid bottom-left bottom-right bottom)
  (is-emb-bottom-right : is-emb bottom-right)
  where

  is-equiv-pasting-vertical-coherence-square-maps :
    is-equiv
      ( λ H →
        pasting-vertical-coherence-square-maps
          ( top)
          ( top-left)
          ( top-right)
          ( mid)
          ( bottom-left)
          ( bottom-right)
          ( bottom)
          ( H)
          ( K))
  is-equiv-pasting-vertical-coherence-square-maps =
    is-equiv-comp _ _
      ( is-equiv-map-Π-is-fiberwise-equiv (λ _ → is-emb-bottom-right _ _))
      ( is-equiv-concat-htpy (K ·r top-left) _)

  equiv-pasting-vertical-coherence-square-maps :
    coherence-square-maps top top-left top-right mid ≃
    coherence-square-maps
      ( top)
      ( bottom-left ∘ top-left)
      ( bottom-right ∘ top-right)
      ( bottom)
  pr1 equiv-pasting-vertical-coherence-square-maps H =
    pasting-vertical-coherence-square-maps
      ( top)
      ( top-left)
      ( top-right)
      ( mid)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( H)
      ( K)
  pr2 equiv-pasting-vertical-coherence-square-maps =
    is-equiv-pasting-vertical-coherence-square-maps
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
    l |   H  m |   K    | r  ↦  l |   H | K   | r
      ∨        ∨        ∨         ∨           ∨
      X -----> Y -----> Z         X --------> Z
          bl       br                br ∘ bl

               ↧                        ↧

             - ∘ r
        W^Z ------> W^C
         |           |
  - ∘ br |    W^K    | - ∘ tr        W^(H | K)
         ∨   - ∘ m   ∨                  ~
        W^Y ------> W^B       ↦
         |           |                 W^K
  - ∘ bl |    W^H    | - ∘ tl          ---
         ∨           ∨                 W^H
        W^X ------> W^A
             - ∘ l
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
            ( distributive-left-whisker-comp-concat
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
            ( htpy-precomp K W h)
        by
        ap-binary
          ( λ L q → eq-htpy L ∙ q)
          ( eq-htpy (preserves-comp-left-whisker-comp h bottom-right H))
          ( inv (coherence-eq-htpy-ap-precomp top-left (h ·l K)))

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
            ( distributive-left-whisker-comp-concat
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
          ( htpy-precomp K W h) ∙
        eq-htpy
          ( (h ∘ right-bottom) ·l H)
        by
        ap-binary
          ( λ p L → p ∙ eq-htpy L)
          ( inv (coherence-eq-htpy-ap-precomp left-top (h ·l K)))
          ( eq-htpy (preserves-comp-left-whisker-comp h right-bottom H))
```

### Transposing by precomposition of whiskered squares

Taking a square of the form

```text
      f        top
  X -----> A -----> B
           |        |
      left |   H    | right
           ∨        ∨
           C -----> D
             bottom
```

and transposing it by precomposition results in the square

```text
  W^D -----> W^B
   |          |
   |   W^H    |
   ∨          ∨  - ∘ f
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

  distributive-precomp-right-whisker-comp-coherence-square-maps :
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
  distributive-precomp-right-whisker-comp-coherence-square-maps f g =
    inv (coherence-eq-htpy-ap-precomp f (g ·l H))
```

Similarly, we can calculate transpositions of left-whiskered squares with the
formula `W^(f ·l H) = W^H ·r W^f`.

```agda
  distributive-precomp-left-whisker-comp-coherence-square-maps :
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
  distributive-precomp-left-whisker-comp-coherence-square-maps f g =
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
      ( horizontal-pasting-htpy-coherence-triangle-maps
        ( top)
        ( left)
        ( right)
        ( bottom)
        ( L)
        ( H)
        ( K))
      ( W)) ~
    ( horizontal-pasting-htpy-coherence-triangle-maps
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
    ( right-whisker-concat
      ( compute-concat-htpy-precomp H L W h)
      ( precomp-coherence-triangle-maps diagonal-right right top K W h))

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
      ( horizontal-pasting-htpy-coherence-triangle-maps'
        ( top)
        ( left)
        ( right)
        ( bottom)
        ( L)
        ( H)
        ( K))
      ( W)) ~
    ( horizontal-pasting-htpy-coherence-triangle-maps'
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
    ( left-whisker-concat
      ( precomp-coherence-triangle-maps' diagonal-left bottom left H W h)
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
      ( horizontal-pasting-coherence-triangle-maps
        ( top)
        ( left)
        ( right)
        ( bottom)
        ( diagonal)
        ( H)
        ( K))
      ( W)) ~
    ( horizontal-pasting-coherence-triangle-maps
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

### Collapsing inner squares in pasted squares composed of triangles

Consider two commuting squares, composed in total of four commuting triangles,
which take the following form:

```text
           top
     A -----------> C
     |             ∧|
     |           /  |
     |     bl  /    |
  tl |       /      | tr
     |     /        |
     |   /          |
     ∨ /    mid     ∨
     B -----------> Y
     |             ∧|
     |           /  |
     |     tr  /    |
  bl |       /      | br
     |     /        |
     |   /          |
     ∨ /            ∨
     C -----------> Z .
          bottom
```

Note that the bottom-left vertex is the same as the top-right vertex, and the
diagonals are not arbitrary.

If the square that arises in the middle,

```text
        bl
     B ----> C
     |       |
  bl |       | tr
     ∨       ∨
     C ----> Y ,
        tr
```

is homotopic to the reflexive homotopy `refl-htpy : tr ∘ bl ~ tr ∘ bl`, then the
whole rectangle collapses (is homotopic) to the
[horizontal composition](foundation.homotopy-algebra.md)

```text
                         Y
                        ∧ \
                  tr  /     \  br
                    /         \
        top       /             ∨
  A -----------> C -----------> Z .
   \             ∧    bottom
     \         /
   tl  \     /  bl
         ∨ /
          B
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {Y : UU l4} {Z : UU l5}
  (top : A → C) (top-left : A → B) (top-right : C → Y)
  (mid : B → Y)
  (bottom-left : B → C) (bottom-right : Y → Z) (bottom : C → Z)
  (top-left-triangle : coherence-triangle-maps' top bottom-left top-left)
  (top-right-triangle : coherence-triangle-maps mid top-right bottom-left)
  (bottom-left-triangle : coherence-triangle-maps' mid top-right bottom-left)
  (bottom-right-triangle :
    coherence-triangle-maps bottom bottom-right top-right)
  where

  pasting-coherence-squares-collapse-triangles' :
    bottom-left-triangle ∙h top-right-triangle ~ refl-htpy →
    pasting-vertical-coherence-square-maps
      ( top)
      ( top-left)
      ( top-right)
      ( mid)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( horizontal-pasting-up-diagonal-coherence-triangle-maps
        ( top)
        ( top-left)
        ( top-right)
        ( mid)
        ( top-left-triangle)
        ( top-right-triangle))
      ( horizontal-pasting-up-diagonal-coherence-triangle-maps
        ( mid)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( bottom-left-triangle)
        ( bottom-right-triangle)) ~
    horizontal-concat-htpy'
      ( bottom-right-triangle)
      ( top-left-triangle)
  pasting-coherence-squares-collapse-triangles' H =
    left-whisker-concat-coherence-square-homotopies
      ( bottom-right-triangle ·r bottom-left ·r top-left)
      ( refl-htpy)
      ( _)
      ( _)
      ( _)
      ( ( inv-htpy
          ( distributive-left-whisker-comp-concat
            ( bottom-right)
            ( bottom-left-triangle ·r top-left)
            ( ( top-right-triangle ·r top-left) ∙h
              ( top-right ·l top-left-triangle)))) ∙h
        ( left-whisker-comp²
          ( bottom-right)
          ( inv-htpy
            ( right-whisker-concat-coherence-triangle-homotopies
              ( refl-htpy)
              ( top-right-triangle ·r top-left)
              ( bottom-left-triangle ·r top-left)
              ( inv-htpy H ·r top-left)
              ( top-right ·l top-left-triangle)))) ∙h
        ( preserves-comp-left-whisker-comp
          ( bottom-right)
          ( top-right)
          ( top-left-triangle))) ∙h
    ( ap-concat-htpy'
      ( (bottom-right ∘ top-right) ·l top-left-triangle)
      ( right-unit-htpy))

  pasting-coherence-squares-collapse-triangles :
    bottom-left-triangle ∙h top-right-triangle ~ refl-htpy →
    pasting-vertical-coherence-square-maps
      ( top)
      ( top-left)
      ( top-right)
      ( mid)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( horizontal-pasting-up-diagonal-coherence-triangle-maps
        ( top)
        ( top-left)
        ( top-right)
        ( mid)
        ( top-left-triangle)
        ( top-right-triangle))
      ( horizontal-pasting-up-diagonal-coherence-triangle-maps
        ( mid)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( bottom-left-triangle)
        ( bottom-right-triangle)) ~
    horizontal-concat-htpy
      ( bottom-right-triangle)
      ( top-left-triangle)
  pasting-coherence-squares-collapse-triangles H =
    ( pasting-coherence-squares-collapse-triangles' H) ∙h
    ( coh-horizontal-concat-htpy
      ( bottom-right-triangle)
      ( top-left-triangle))
```
