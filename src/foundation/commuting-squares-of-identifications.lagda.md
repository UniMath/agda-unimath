# Commuting squares of identifications

```agda
module foundation.commuting-squares-of-identifications where

open import foundation-core.commuting-squares-of-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

In this file we develop some further properties of
[commuting squares of identifications](foundation-core.commuting-squares-of-identifications.md).

## Operations

### Horizontally pasting squares of identifications

Consider two squares of identifications as in the diagram

```text
            top-left         top-right
       a -------------> b -------------> c
       |                |                |
  left |                | middle         | right
       ∨                ∨                ∨
       d -------------> e -------------> f
          bottom-left      bottom-right
```

with `s : left ∙ bottom-left ＝ top-left ∙ middle` and t : middle ∙ bottom-right
＝ top-right ∙ right`. Then the outer square commutes.

```agda
module _
  {l : Level} {A : UU l} {a b c d e f : A}
  (top-left : a ＝ b) (top-right : b ＝ c)
  (left : a ＝ d) (middle : b ＝ e) (right : c ＝ f)
  (bottom-left : d ＝ e) (bottom-right : e ＝ f)
  where

  coherence-square-identifications-comp-horizontal :
    coherence-square-identifications top-left left middle bottom-left →
    coherence-square-identifications top-right middle right bottom-right →
    coherence-square-identifications
      (top-left ∙ top-right) left right (bottom-left ∙ bottom-right)
  coherence-square-identifications-comp-horizontal p q =
    ( ( ( ( inv (assoc left bottom-left bottom-right)) ∙
          ( ap-binary _∙_ p refl)) ∙
        ( assoc top-left middle bottom-right)) ∙
      ( ap-binary _∙_ (refl {x = top-left}) q)) ∙
    ( inv (assoc top-left top-right right))
```

### Vertically pasting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {a b c d e f : A}
  (top : a ＝ b) (top-left : a ＝ c) (top-right : b ＝ d)
  (middle : c ＝ d) (bottom-left : c ＝ e) (bottom-right : d ＝ f)
  (bottom : e ＝ f)
  where

  coherence-square-identifications-comp-vertical :
    coherence-square-identifications top top-left top-right middle →
    coherence-square-identifications middle bottom-left bottom-right bottom →
    coherence-square-identifications
      top (top-left ∙ bottom-left) (top-right ∙ bottom-right) bottom
  coherence-square-identifications-comp-vertical p q =
    ( ( assoc top-left bottom-left bottom) ∙
      ( ( ( ap-binary _∙_ (refl {x = top-left}) q) ∙
          ( inv (assoc top-left middle bottom-right))) ∙
        ( ap-binary _∙_ p (refl {x = bottom-right})))) ∙
    ( assoc top top-right bottom-right)
```

### Horizontal pasting of commuting squares of identifications

Consider a commuting diagram of identifications

```text
            top-left        top-right
       a -------------> b -------------> c
       |                |                |
  left |                | middle         | right
       ∨                ∨                ∨
       d -------------> e -------------> f
          bottom-left      bottom-right
```

in a type `A`.

```agda
{-
  (p-lleft : a ＝ b) (p-lbottom : b ＝ d) (p-rbottom : d ＝ f)
  (p-middle : c ＝ d) (p-ltop : a ＝ c) (p-rtop : c ＝ e) (p-rright : e ＝ f)
-}

module _
  {l : Level} {A : UU l} {a b c d e f : A}
  (top-left : a ＝ b) (top-right : b ＝ c)
  (left : a ＝ d) (middle : b ＝ e) (right : c ＝ f)
  (bottom-left : d ＝ e) (bottom-right : e ＝ f)
  where

  horizontal-concat-square :
    coherence-square-identifications top-left left middle bottom-left →
    coherence-square-identifications top-right middle right bottom-right →
    coherence-square-identifications
      ( top-left ∙ top-right)
      ( left)
      ( right)
      ( bottom-left ∙ bottom-right)
  horizontal-concat-square s t =
    ( inv (assoc left bottom-left bottom-right)) ∙
    ( ( ap (concat' a bottom-right) s) ∙
      ( ( assoc top-left middle bottom-right) ∙
        ( ( ap (concat top-left f) t) ∙
          ( inv (assoc top-left top-right right)))))

module _
  {l : Level} {A : UU l} {a b c d : A}
  where

  left-unit-law-horizontal-concat-square :
    (top : a ＝ b) (left : a ＝ c) (right : b ＝ d) (bottom : c ＝ d)
    (s : coherence-square-identifications top left right bottom) →
    horizontal-concat-square refl top left left right refl bottom
      ( horizontal-refl-coherence-square-identifications left)
      ( s) ＝
    s
  left-unit-law-horizontal-concat-square top refl right bottom s =
    right-unit ∙ ap-id s

vertical-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-tleft : a ＝ b) (p-bleft : b ＝ c) (p-bbottom : c ＝ f)
  (p-middle : b ＝ e) (p-ttop : a ＝ d) (p-tright : d ＝ e) (p-bright : e ＝ f)
  (s-top : coherence-square-identifications p-ttop p-tleft p-tright p-middle)
  (s-bottom :
    coherence-square-identifications p-middle p-bleft p-bright p-bbottom) →
  coherence-square-identifications
    p-ttop (p-tleft ∙ p-bleft) (p-tright ∙ p-bright) p-bbottom
vertical-concat-square {a = a} {f = f}
  p-tleft p-bleft p-bbottom p-middle p-ttop p-tright p-bright s-top s-bottom =
  ( assoc p-tleft p-bleft p-bbottom) ∙
  ( ( ap (concat p-tleft f) s-bottom) ∙
    ( ( inv (assoc p-tleft p-middle p-bright)) ∙
      ( ( ap (concat' a p-bright) s-top) ∙
        ( assoc p-ttop p-tright p-bright))))
```

### Whiskering squares of identifications

Given an identification at one the vertices of a coherence square, then we may
whisker the square by that identification.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (left : x ＝ z) (bottom : z ＝ w) (top : x ＝ y) (right : y ＝ w)
  where

  coherence-square-identifications-top-left-whisker' :
    {x' : A} (p : x' ＝ x) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom
  coherence-square-identifications-top-left-whisker' refl sq = sq

  coherence-square-identifications-top-left-whisker :
    {x' : A} (p : x ＝ x') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (inv p ∙ top) (inv p ∙ left) right bottom
  coherence-square-identifications-top-left-whisker refl sq = sq

  coherence-square-identifications-top-right-whisker :
    {y' : A} (p : y ＝ y') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (top ∙ p) left (inv p ∙ right) bottom
  coherence-square-identifications-top-right-whisker refl =
    top-concat-identification-coherence-square-identification
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)

  coherence-square-identifications-bottom-left-whisker :
    {z' : A} (p : z ＝ z') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top (left ∙ p) right (inv p ∙ bottom)
  coherence-square-identifications-bottom-left-whisker refl =
    left-concat-identification-coherence-square-identification
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)

  coherence-square-identifications-bottom-right-whisker :
    {w' : A} (p : w ＝ w') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p)
  coherence-square-identifications-bottom-right-whisker refl =
    ( bottom-concat-identification-coherence-square-identification
      ( top)
      ( left)
      ( right ∙ refl)
      ( bottom)
      ( inv right-unit)) ∘
    ( right-concat-identification-coherence-square-identification
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit))
```

## Properties

### Whiskering of squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : x ＝ y) (p' : x ＝ z) {q : y ＝ u} {q' : z ＝ u} (r : u ＝ v)
  where

  equiv-right-whisker-square-identification :
    ( coherence-square-identifications p p' q q') ≃
    ( coherence-square-identifications p p' (q ∙ r) (q' ∙ r))
  equiv-right-whisker-square-identification =
    ( equiv-concat-assoc' (p' ∙ (q' ∙ r)) p q r) ∘e
    ( equiv-concat-assoc p' q' r (p ∙ q ∙ r)) ∘e
    ( equiv-right-whisker-identification r)

  right-whisker-square-identification :
    coherence-square-identifications p p' q q' →
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r)
  right-whisker-square-identification =
    map-equiv equiv-right-whisker-square-identification

  right-unwhisker-square-identifications :
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r) →
    coherence-square-identifications p p' q q'
  right-unwhisker-square-identifications =
    map-inv-equiv equiv-right-whisker-square-identification

module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : v ＝ x) {q : x ＝ y} {q' : x ＝ z} {r : y ＝ u} {r' : z ＝ u}
  where

  equiv-left-whisker-square-identification :
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') r r')
  equiv-left-whisker-square-identification =
    ( inv-equiv (equiv-concat-assoc p q' r' (p ∙ q ∙ r))) ∘e
    ( inv-equiv (equiv-concat-assoc' (p ∙ (q' ∙ r')) p q r)) ∘e
    ( equiv-left-whisker-identification p)

  left-whisker-square-identification :
    coherence-square-identifications q q' r r' →
    coherence-square-identifications (p ∙ q) (p ∙ q') r r'
  left-whisker-square-identification =
    map-equiv equiv-left-whisker-square-identification

  left-unwhisker-square-identification :
    coherence-square-identifications (p ∙ q) (p ∙ q') r r' →
    coherence-square-identifications q q' r r'
  left-unwhisker-square-identification =
    map-inv-equiv equiv-left-whisker-square-identification

module _
  {l : Level} {A : UU l} {x y z u v w : A}
  where

  equiv-both-whisker-square-identifications :
    (p : x ＝ y) {q : y ＝ z} {q' : y ＝ u} {r : z ＝ v} {r' : u ＝ v} →
    (s : v ＝ w) →
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') (r ∙ s) (r' ∙ s))
  equiv-both-whisker-square-identifications p {q} {q'} s =
    ( equiv-left-whisker-square-identification p) ∘e
    ( equiv-right-whisker-square-identification q q' s)
```
