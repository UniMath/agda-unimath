# Commuting squares of identifications

```agda
module foundation-core.commuting-squares-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

A square of [identifications](foundation-core.identity-types.md)

```text
           top
       x -------> y
       |          |
  left |          | right
       ∨          ∨
       z -------> w
          bottom
```

is said to **commute** if there is an identification
`left ∙ bottom ＝ top ∙ right`. Such an identification is called a
{{#concept "coherence" Disambiguation="commuting square of identifications" Agda=coherence-square-identifications}}
of the square.

## Definitions

### Commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  where

  coherence-square-identifications : UU l
  coherence-square-identifications = left ∙ bottom ＝ top ∙ right
```

### Horizontally constant squares

```agda
module _
  {l : Level} {A : UU l} {a b : A} (p : a ＝ b)
  where

  horizontal-refl-coherence-square-identifications :
    coherence-square-identifications refl p p refl
  horizontal-refl-coherence-square-identifications = right-unit
```

### Vertically constant squares

```agda
module _
  {l : Level} {A : UU l} {a b : A} (p : a ＝ b)
  where

  vertical-refl-coherence-square-identifications :
    coherence-square-identifications p refl refl p
  vertical-refl-coherence-square-identifications = inv right-unit
```

## Operations

### Inverting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  coherence-square-identifications-horizontal-inv :
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (inv top) right left (inv bottom)
  coherence-square-identifications-horizontal-inv refl refl right refl coh =
    right-unit ∙ inv coh
```

### Functions acting on squares of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y z w : A} (f : A → B)
  where

  coherence-square-identifications-ap :
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications
      ( ap f top)
      ( ap f left)
      ( ap f right)
      ( ap f bottom)
  coherence-square-identifications-ap refl refl right refl coh = ap (ap f) coh
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
