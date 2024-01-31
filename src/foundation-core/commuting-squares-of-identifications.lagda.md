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

  map-coherence-square-identifications :
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications
      ( ap f top)
      ( ap f left)
      ( ap f right)
      ( ap f bottom)
  map-coherence-square-identifications refl refl right refl coh = ap (ap f) coh
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

  left-concat-identification-coherence-square-identifications :
    {left' : x ＝ z} (s : left ＝ left') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left' right bottom
  left-concat-identification-coherence-square-identifications refl sq = sq

  bottom-concat-identification-coherence-square-identifications :
    {bottom' : z ＝ w} (s : bottom ＝ bottom') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right bottom'
  bottom-concat-identification-coherence-square-identifications refl sq = sq

  top-concat-identification-coherence-square-identifications :
    {top' : x ＝ y} (s : top ＝ top') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top' left right bottom
  top-concat-identification-coherence-square-identifications refl sq = sq

  right-concat-identification-coherence-square-identifications :
    {right' : y ＝ w} (s : right ＝ right') →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right' bottom
  right-concat-identification-coherence-square-identifications refl sq = sq
```

### Whiskering and splicing coherences of commuting squares of identifications

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

we may consider four ways of attaching new identifications to it:

1. Prepending `p : u ＝ x` to the left gives us a commuting square

   ```text
                p ∙ top
              u -------> y
              |          |
     p ∙ left |          | right
              ∨          ∨
              z -------> w.
                 bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ ((p ∙ left) ∙ bottom ＝ (p ∙ top) ∙ right).
   ```

2. Appending an identification `p : w ＝ u` to the right gives a commuting
   square of identifications

   ```text
                   top
           x ------------> y
           |               |
      left |               | right ∙ p
           ∨               ∨
           z ------------> u.
              bottom ∙ p
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ (left ∙ (bottom ∙ p) ＝ top ∙ (right ∙ p)).
   ```

3. Splicing an identification `p : z ＝ u` and its inverse into the middle gives
   a commuting square of identifications

   ```text
                      top
              x --------------> y
              |                 |
     left ∙ p |                 | right
              ∨                 ∨
              u --------------> w.
                 p⁻¹ ∙ bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ ((left ∙ p) ∙ (p⁻¹ ∙ bottom) ＝ top ∙ right).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ ((left ∙ p⁻¹) ∙ (p ∙ bottom) ＝ top ∙ right).
   ```

4. Splicing an identification `p : y ＝ u` and its inverse into the middle gives
   a commuting square of identifications

   ```text
             top ∙ p
          x --------> u
          |           |
     left |           | p⁻¹ ∙ right
          ∨           ∨
          z --------> w.
             bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ (left ∙ bottom ＝ (top ∙ p) ∙ (p⁻¹ ∙ right)).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙ bottom ＝ top ∙ right) ≃ (left ∙ bottom ＝ (top ∙ p⁻¹) ∙ (p ∙ right)).
   ```

These operations are useful in proofs involving path algebra, because taking
`equiv-right-whisker-square-identicications` as an example, it provides us with
two maps: the forward direction states
`(p ∙ r ＝ q ∙ s) → (p ∙ (r ∙ t)) ＝ q ∙ (s ∙ t))`, which allows one to append
an identification without needing to reassociate on the right, and the backwards
direction conversely allows one to cancel out an identification in parentheses.

#### Left whiskering coherences of commuting squares of identifications

For any identification `p : u ＝ x` we obtain an equivalence

```text
           top                                p ∙ top
       x -------> y                         u -------> y
       |          |                         |          |
  left |          | right    ≃     p ∙ left |          | right
       ∨          ∨                         ∨          ∨
       z -------> w                         z -------> w
          bottom                               bottom
```

of coherences of commuting squares of identifications.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  where

  coherence-square-identifications-top-left-whisker' :
    {u : A} (p : u ＝ x) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom
  coherence-square-identifications-top-left-whisker' refl sq = sq

  coherence-square-identifications-top-left-whisker :
    {u : A} (p : x ＝ u) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (inv p ∙ top) (inv p ∙ left) right bottom
  coherence-square-identifications-top-left-whisker refl sq = sq
```

#### Right whiskering coherences of commuting squares of identifications

For any identification `p : w ＝ u` we obtain an equivalence

```text
           top                                 top
       x -------> y                     x ------------> y
       |          |                     |               |
  left |          | right    ≃     left |               | right ∙ p
       ∨          ∨                     ∨               ∨
       z -------> w                     z ------------> w
          bottom                           bottom ∙ p
```

of coherences of commuting squares of identifications.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  where

  coherence-square-identifications-bottom-right-whisker :
    {u : A} (p : w ＝ u) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p)
  coherence-square-identifications-bottom-right-whisker refl =
    ( bottom-concat-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right ∙ refl)
      ( bottom)
      ( inv right-unit)) ∘
    ( right-concat-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit))
```

#### Left splicing coherences of commuting squares of identifications

For inverse pair of identifications `p : y ＝ u` and `q : u ＝ y` equipped with
`α : inv p ＝ q` we obtain an equivalence

```text
           top                                    top
       x -------> y                         x -----------> y
       |          |                         |              |
  left |          | right    ≃     left ∙ p |              | right
       ∨          ∨                         ∨              ∨
       z -------> w                         u -----------> w
          bottom                               q ∙ bottom
```

of coherences of commuting squares of identifications.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  where

  coherence-square-identifications-bottom-left-whisker :
    {u : A} (p : z ＝ u) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top (left ∙ p) right (inv p ∙ bottom)
  coherence-square-identifications-bottom-left-whisker refl =
    left-concat-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)
```

#### Right splicing coherences of commuting squares of identifications

For inverse pair of identifications `p : y ＝ u` and `q : u ＝ y` equipped with
`α : inv p ＝ q` we obtain an equivalence

```text
           top                             top ∙ p
       x -------> y                     x --------> u
       |          |                     |           |
  left |          | right    ≃     left |           | q ∙ right
       ∨          ∨                     ∨           ∨
       z -------> w                     z --------> w
          bottom                           bottom
```

of coherences of commuting squares of identifications.

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  where

  coherence-square-identifications-top-right-whisker :
    {u : A} (p : y ＝ u) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (top ∙ p) left (inv p ∙ right) bottom
  coherence-square-identifications-top-right-whisker refl =
    top-concat-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)
```
