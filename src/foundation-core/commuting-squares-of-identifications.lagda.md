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

{{#concept "Horizontally constant squares" Disambiguation="identifications" Agda=horizontal-refl-coherence-square-identifications}}
are commuting squares of identifications of the form

```text
       refl
    a -----> a
    |        |
  p |        | p
    ∨        ∨
    b -----> b.
       refl
```

```agda
module _
  {l : Level} {A : UU l} {a b : A} (p : a ＝ b)
  where

  horizontal-refl-coherence-square-identifications :
    coherence-square-identifications refl p p refl
  horizontal-refl-coherence-square-identifications = right-unit
```

### Vertically constant squares

{{#concept "Vertically constant squares" Disambiguation="identifications" Agda=vertical-refl-coherence-square-identifications}}
are commuting squares of identifications of the form

```text
           p
       a -----> b
       |        |
  refl |        | refl
       ∨        ∨
       a -----> b.
           p
```

```agda
module _
  {l : Level} {A : UU l} {a b : A} (p : a ＝ b)
  where

  vertical-refl-coherence-square-identifications :
    coherence-square-identifications p refl refl p
  vertical-refl-coherence-square-identifications = inv right-unit
```

## Operations

### Inverting squares of identifications horizontally

Given a commuting square of identifications

```text
           top
       x -------> y
       |          |
  left |          | right
       ∨          ∨
       z -------> w,
          bottom
```

the square of identifications

```text
             inv top
        y ------------> x
        |               |
  right |               | left
        ∨               ∨
        w ------------> z
           inv bottom
```

commutes.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  horizontal-inv-coherence-square-identifications :
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (inv top) right left (inv bottom)
  horizontal-inv-coherence-square-identifications refl refl right refl coh =
    right-unit ∙ inv coh
```

### Inverting squares of identifications vertically

Given a commuting square of identifications

```text
           top
       x -------> y
       |          |
  left |          | right
       ∨          ∨
       z -------> w,
          bottom
```

the square of identifications

```text
              bottom
           z -------> w
           |          |
  inv left |          | inv right
           ∨          ∨
           x -------> y
               top
```

commutes.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  vertical-inv-coherence-square-identifications :
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications bottom (inv left) (inv right) top
  vertical-inv-coherence-square-identifications refl refl refl refl refl = refl
```

### Functions acting on squares of identifications

Given a commuting square of identifications

```text
           top
       x -------> y
       |          |
  left |          | right
       ∨          ∨
       z -------> w
          bottom
```

in a type `A`, and given a map `f : A → B`, the square of identifications

```text
                 ap f top
           f x -----------> f y
            |                |
  ap f left |                | ap f right
            ∨                ∨
            z -------------> w
               ap f bottom
```

commutes.

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

Consider a commuting square of identifications and an identification of one of
the four sides with another identification, as for example in the diagram below:

```text
             top
       a ---------> b
       |           | |
  left |     right |=| right'
       ∨           ∨ ∨
       c ---------> d.
           bottom
```

Then any identification witnessing that the square commutes can be concatenated
with the identification on the side, to obtain a new commuting square of
identifications.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  where

  left-concat-identification-coherence-square-identification :
    {left' : x ＝ z} (s : left ＝ left') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left' right bottom
  left-concat-identification-coherence-square-identification refl sq = sq

  bottom-concat-identification-coherence-square-identification :
    {bottom' : z ＝ w} (s : bottom ＝ bottom') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right bottom'
  bottom-concat-identification-coherence-square-identification refl sq = sq

  top-concat-identification-coherence-square-identification :
    {top' : x ＝ y} (s : top ＝ top') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top' left right bottom
  top-concat-identification-coherence-square-identification refl sq = sq

  right-concat-identification-coherence-square-identification :
    {right' : y ＝ w} (s : right ＝ right') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right' bottom
  right-concat-identification-coherence-square-identification refl sq = sq
```
