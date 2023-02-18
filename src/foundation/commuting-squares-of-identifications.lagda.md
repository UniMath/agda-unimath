# Commuting squares of identifications

```agda
{-# OPTIONS --safe #-}

module foundation.commuting-squares-of-identifications where

open import foundation-core.identity-types
open import foundation-core.universe-levels
```

## Idea

A square of identifications

```md
  x0 ------ y2
   |        |
   |        |
   |        |
  y1 ------ z
```

is said to _commute_ if there is a path `left ∙ bottom ＝ top ∙ right`. Such a path may be called a _filler_ of the square.

## Definitions

### Commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z : A}
  where

  coherence-square :
    (p-left : x ＝ y1) (p-bottom : y1 ＝ z)
    (p-top : x ＝ y2) (p-right : y2 ＝ z) → UU l
  coherence-square p-left p-bottom p-top p-right =
    (p-left ∙ p-bottom) ＝ (p-top ∙ p-right)
```

## Operations

### Pasting commutative squares of identifications

We can compose coherence squares that have an edge in common. We call this _pasting_ of squares.

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z1 z2 w : A}
  (p-left : x ＝ y1) {p-bottom : y1 ＝ z1}
  {p-top : x ＝ y2} (middle : y2 ＝ z1)
  {q-bottom : z1 ＝ w} {q-top : y2 ＝ z2}
  (q-right : z2 ＝ w)
  where

  coherence-square-comp-horizontal :
    coherence-square p-left p-bottom p-top middle →
    coherence-square middle q-bottom q-top q-right →
    coherence-square p-left (p-bottom ∙ q-bottom) (p-top ∙ q-top) q-right
  coherence-square-comp-horizontal p q =
    ( ( ( inv (assoc p-left p-bottom q-bottom) ∙
          ap-binary (_∙_) p (refl {x = q-bottom})) ∙
        assoc p-top middle q-bottom) ∙
      ap-binary (_∙_) (refl {x = p-top}) q) ∙
    inv (assoc p-top q-top q-right)

module _
  {l : Level} {A : UU l} {x y1 y2 z1 z2 w : A}
  {p-left : x ＝ y1} {middle : y1 ＝ z2}
  {p-top : x ＝ y2} {p-right : y2 ＝ z2}
  {q-left : y1 ＝ z1} {q-bottom : z1 ＝ w}
  {q-right : z2 ＝ w}
  where

  coherence-square-comp-vertical :
    coherence-square p-left middle p-top p-right →
    coherence-square q-left q-bottom middle q-right →
    coherence-square (p-left ∙ q-left) q-bottom p-top (p-right ∙ q-right)
  coherence-square-comp-vertical p q =
    ( assoc p-left q-left q-bottom ∙
      ( ( ap-binary (_∙_) (refl {x = p-left}) q ∙
          inv (assoc p-left middle q-right)) ∙
        ap-binary (_∙_) p (refl {x = q-right}))) ∙
      assoc p-top p-right q-right
```

### Whiskering of commutative squares

We can also _whisker_ a square: given a commutative square with, e.g., right edge `p-top` and an identification `p-top ＝ q-top`, we can derive a commutative square with top edge `q-top`. Note that whiskering of left and top edges is defined in `foundation-core.identity-types`.

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z : A}
  where

  coherence-square-left-whisk :
    {p1 p1' : x ＝ y1} (s : p1 ＝ p1') {q1 : y1 ＝ z} {p2 : x ＝ y2}
    {q2 : y2 ＝ z} → coherence-square p1 q1 p2 q2 → coherence-square p1' q1 p2 q2
  coherence-square-left-whisk refl sq = sq

  coherence-square-top-whisk :
    (p1 : x ＝ y1) (q1 : y1 ＝ z) (p2 : x ＝ y2) {p2' : x ＝ y2} (s : p2 ＝ p2')
    (q2 : y2 ＝ z) → coherence-square p1 q1 p2 q2 → coherence-square p1 q1 p2' q2
  coherence-square-top-whisk p1 q1 p2 refl q2 sq = sq

  coherence-square-right-whisk :
    {p-left : x ＝ y1} {p-bottom : y1 ＝ z} {p-top : x ＝ y2}
    {p-right q-right : y2 ＝ z} (s : p-right ＝ q-right) →
    coherence-square p-left p-bottom p-top p-right →
    coherence-square p-left p-bottom p-top q-right
  coherence-square-right-whisk refl sq = sq

  coherence-square-bottom-whisk :
    {p-left : x ＝ y1} {p-bottom q-bottom : y1 ＝ z} {p-top : x ＝ y2}
    {p-right : y2 ＝ z} (s : p-bottom ＝ q-bottom) →
    coherence-square p-left p-bottom p-top p-right →
    coherence-square p-left q-bottom p-top p-right
  coherence-square-bottom-whisk refl sq = sq
```
