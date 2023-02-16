---
title : Paths
description: a collection of definitions and lemmas specific to this thesis relating to paths.
---

```agda

module foundation.squares-of-identifications where


{-FROM: agda-unimath -}

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
```

### Idea :

A square of identifications (paths)

```md
                 p-top
            x0 ------ y2
            |                 |
p-left |                 | p-right
            |                 |
            y1 ------ z
             p-bottom
```

is said to commute if there is a path `p ∙ q ＝ r ∙ s`. Such a path may often be called a "filler" of the square. The type fillers for a given square, called `square p q r s`, is defined in `foundation-core.identity-types`. This file includes basic operations on commutative squares of identifications.

### Composition of squares

### Pasting

We can compose commutative squares that have a leg in common (often called pasting of squares).

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
      (horizontal-concat-Id² p (refl {x = q-bottom}))) ∙
        (assoc p-top middle q-bottom)) ∙
          (horizontal-concat-Id² (refl {x = p-top}) q)) ∙
            inv (assoc p-top q-top q-right)
```

### Whiskering

We can also "whisker" a square: given a commutative square with, e.g., right leg `p-top` and an identification `p-top ＝ q-top`, we can derive a commutative square with top leg `q-top`. Note that whiskering of left and top legs is defined in `foundation-core.identity-types`.

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z : A}
  where

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

