# Squares of identifications

```agda

{-# OPTIONS --safe #-}

module foundation.squares-of-identifications where

open import foundation-core.identity-types
open import foundation-core.universe-levels
```

## Idea :

A square of identifications

```md
            x0 ------ y2
            |      |
            |      | 
            |      |
            y1 ------ z
```

is said to commute if there is a path `left ∙ bottom ＝ top ∙ right`. Such a path may often be called a "filler" of the square.

## Definitions

### Definition of commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z : A}
  where
  
  square :
    (p-left : x ＝ y1) (p-bottom : y1 ＝ z)
    (p-top : x ＝ y2) (p-right : y2 ＝ z) → UU l
  square p-left p-bottom p-top p-right =
    (p-left ∙ p-bottom) ＝ (p-top ∙ p-right)
```

## Operations

### Pasting commutative squares

We can compose coherence squares that have an edge in common. We call this `pasting` of squares.

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z1 z2 w : A}
  (p-left : x ＝ y1) {p-bottom : y1 ＝ z1}
  {p-top : x ＝ y2} (middle : y2 ＝ z1)
  {q-bottom : z1 ＝ w} {q-top : y2 ＝ z2}
  (q-right : z2 ＝ w)
  where

  square-comp-horizontal :
    (square p-left p-bottom p-top middle) →
    (square middle q-bottom q-top q-right) →
    (square p-left (p-bottom ∙ q-bottom) (p-top ∙ q-top) q-right)
  square-comp-horizontal p q =
    ((( inv (assoc p-left p-bottom q-bottom) ∙
      (ap-binary (_∙_) p (refl {x = q-bottom}))) ∙
        (assoc p-top middle q-bottom)) ∙
          (ap-binary (_∙_) (refl {x = p-top}) q)) ∙
            inv (assoc p-top q-top q-right)

module _
  {l : Level} {A : UU l} {x y1 y2 z1 z2 w : A}
  {p-left : x ＝ y1} {middle : y1 ＝ z2}
  {p-top : x ＝ y2} {p-right : y2 ＝ z2}
  {q-left : y1 ＝ z1} {q-bottom : z1 ＝ w}
  {q-right : z2 ＝ w}
  where

  square-comp-vertical :
    (square p-left middle p-top p-right) →
    (square q-left q-bottom middle q-right) →
    (square (p-left ∙ q-left) q-bottom p-top (p-right ∙ q-right))
  square-comp-vertical p q =
    (assoc p-left q-left q-bottom ∙ (((ap-binary (_∙_) (refl {x = p-left}) q) ∙
      (inv (assoc p-left middle q-right))) ∙
        ap-binary (_∙_) p (refl {x = q-right}))) ∙ assoc p-top p-right q-right

```

### Whiskering of commutative squares

We can also "whisker" a square: given a commutative square with, e.g., right leg `p-top` and an identification `p-top ＝ q-top`, we can derive a commutative square with top leg `q-top`. Note that whiskering of left and top legs is defined in `foundation-core.identity-types`.

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z : A}
  where

  sq-left-whisk :
    {p1 p1' : x ＝ y1} (s : p1 ＝ p1') {q1 : y1 ＝ z} {p2 : x ＝ y2}
    {q2 : y2 ＝ z} → square p1 q1 p2 q2 → square p1' q1 p2 q2
  sq-left-whisk refl sq = sq

  sq-top-whisk :
    (p1 : x ＝ y1) (q1 : y1 ＝ z) (p2 : x ＝ y2) {p2' : x ＝ y2} (s : p2 ＝ p2')
    (q2 : y2 ＝ z) → square p1 q1 p2 q2 → square p1 q1 p2' q2
  sq-top-whisk p1 q1 p2 refl q2 sq = sq

  sq-right-whisk :
    {p-left : x ＝ y1} {p-bottom : y1 ＝ z} {p-top : x ＝ y2}
    {p-right q-right : y2 ＝ z} (s : p-right ＝ q-right)  → square p-left p-bottom p-top p-right →
    square p-left p-bottom p-top q-right
  sq-right-whisk refl sq = sq

  sq-bottom-whisk :
    {p-left : x ＝ y1} {p-bottom q-bottom : y1 ＝ z} {p-top : x ＝ y2}
    {p-right : y2 ＝ z} (s : p-bottom ＝ q-bottom)  → square p-left p-bottom p-top p-right →
    square p-left q-bottom p-top p-right
  sq-bottom-whisk refl sq = sq
```

