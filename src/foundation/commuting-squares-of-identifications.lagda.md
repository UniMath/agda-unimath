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
  x ------ y2
  |         |
  |         |
  |         |
  y1 ------ z
```

is said to _commute_ if there is an identification `left ∙ bottom ＝ top ∙ right`. Such an identification may be called a _filler_ of the square.

## Definition

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

### Pasting commuting squares of identifications

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

### Pasting of identifications along edges in coherence squares

Given a coherence square with an edge `p` and a new identification `s : p ＝ p'` then we may paste that identification onto
the square to get a coherence having `p'` as an edge instead of `p`.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (left : x ＝ z) (bottom : z ＝ w) (top : x ＝ y) (right : y ＝ w)
  where

  coherence-square-left-paste :
    {left' : x ＝ z} (s : left ＝ left') →
    coherence-square left bottom top right →
    coherence-square left' bottom top right
  coherence-square-left-paste refl sq = sq

  coherence-square-bottom-paste :
    {bottom' : z ＝ w} (s : bottom ＝ bottom') →
    coherence-square left bottom top right →
    coherence-square left bottom' top right
  coherence-square-bottom-paste refl sq = sq

  coherence-square-top-paste :
    {top' : x ＝ y} (s : top ＝ top') →
    coherence-square left bottom top right →
    coherence-square left bottom top' right
  coherence-square-top-paste refl sq = sq

  coherence-square-right-paste :
    {right' : y ＝ w} (s : right ＝ right') →
    coherence-square left bottom top right →
    coherence-square left bottom top right'
  coherence-square-right-paste refl sq = sq
```
