# Commuting squares of identifications

```agda
module foundation.commuting-squares-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

A square of identifications

```text
          top
      x ------- y
      |         |
 left |         | right
      |         |
      z ------- w
         bottom
```

is said to **commute** if there is an identification
`left ∙ bottom ＝ top ∙ right`. Such an identification is called a **coherence**
of the square.

## Definition

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  coherence-square-identifications :
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) → UU l
  coherence-square-identifications top left right bottom =
    (left ∙ bottom) ＝ (top ∙ right)
```

## Operations

### Composing squares of identifications

We can compose coherence squares that have an edge in common. This is also
called _pasting_ of squares.

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z1 z2 w : A}
  (p-left : x ＝ y1) {p-bottom : y1 ＝ z1}
  {p-top : x ＝ y2} (middle : y2 ＝ z1)
  {q-bottom : z1 ＝ w} {q-top : y2 ＝ z2}
  (q-right : z2 ＝ w)
  where

  coherence-square-identifications-comp-horizontal :
    coherence-square-identifications p-top p-left middle p-bottom →
    coherence-square-identifications q-top middle q-right q-bottom →
    coherence-square-identifications
      (p-top ∙ q-top) p-left q-right (p-bottom ∙ q-bottom)
  coherence-square-identifications-comp-horizontal p q =
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

  coherence-square-identifications-comp-vertical :
    coherence-square-identifications p-top p-left p-right middle →
    coherence-square-identifications middle q-left q-right q-bottom →
    coherence-square-identifications
      p-top (p-left ∙ q-left) (p-right ∙ q-right) q-bottom
  coherence-square-identifications-comp-vertical p q =
    ( assoc p-left q-left q-bottom ∙
      ( ( ap-binary (_∙_) (refl {x = p-left}) q ∙
          inv (assoc p-left middle q-right)) ∙
        ap-binary (_∙_) p (refl {x = q-right}))) ∙
      assoc p-top p-right q-right
```

### Pasting of identifications along edges of squares of identifications

Given a coherence square with an edge `p` and a new identification `s : p ＝ p'`
then we may paste that identification onto the square to get a coherence square
having `p'` as an edge instead of `p`.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (left : x ＝ z) (bottom : z ＝ w) (top : x ＝ y) (right : y ＝ w)
  where

  coherence-square-identifications-left-paste :
    {left' : x ＝ z} (s : left ＝ left') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left' right bottom
  coherence-square-identifications-left-paste refl sq = sq

  coherence-square-identifications-bottom-paste :
    {bottom' : z ＝ w} (s : bottom ＝ bottom') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right bottom'
  coherence-square-identifications-bottom-paste refl sq = sq

  coherence-square-identifications-top-paste :
    {top' : x ＝ y} (s : top ＝ top') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top' left right bottom
  coherence-square-identifications-top-paste refl sq = sq

  coherence-square-identifications-right-paste :
    {right' : y ＝ w} (s : right ＝ right') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right' bottom
  coherence-square-identifications-right-paste refl sq = sq
```

### Whiskering squares of identifications

Given an identification at one the vertices of a coherence square, then we may
whisker the square by that identification.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (left : x ＝ z) (bottom : z ＝ w) (top : x ＝ y) (right : y ＝ w)
  where

  coherence-square-identifications-top-left-whisk' :
    {x' : A} (p : x' ＝ x) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom
  coherence-square-identifications-top-left-whisk' refl sq = sq

  coherence-square-identifications-top-left-whisk :
    {x' : A} (p : x ＝ x') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (inv p ∙ top) (inv p ∙ left) right bottom
  coherence-square-identifications-top-left-whisk refl sq = sq

  coherence-square-identifications-top-right-whisk :
    {y' : A} (p : y ＝ y') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (top ∙ p) left (inv p ∙ right) bottom
  coherence-square-identifications-top-right-whisk refl =
    coherence-square-identifications-top-paste
      left bottom top right (inv right-unit)

  coherence-square-identifications-bottom-left-whisk :
    {z' : A} (p : z ＝ z') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top (left ∙ p) right (inv p ∙ bottom)
  coherence-square-identifications-bottom-left-whisk refl =
    coherence-square-identifications-left-paste
      left bottom top right (inv right-unit)

  coherence-square-identifications-bottom-right-whisk :
    {w' : A} (p : w ＝ w') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p)
  coherence-square-identifications-bottom-right-whisk refl =
    ( coherence-square-identifications-bottom-paste
      left bottom top (right ∙ refl) (inv right-unit)) ∘
    ( coherence-square-identifications-right-paste
      left bottom top right (inv right-unit))
```
