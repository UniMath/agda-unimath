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
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.whiskering-identifications-concatenation
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

is said to be a
{{#concept "commuting square" Disambiguation="identifications" Agda=coherence-square-identifications}}
if there is an identification `left ∙ bottom ＝ top ∙ right`. Such an
identification is called a
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

### Squares with `refl` on the top and bottom

Given an identification `α : p ＝ q`, we can obtain a coherence square with
`refl` on the top and bottom, like the diagram below.

```text
       refl
    a -----> a
    |        |
  p |        | q
    ∨        ∨
    b -----> b
       refl
```

```agda
module _
  {l : Level} {A : UU l} {a b : A} (p q : a ＝ b)
  where

  coherence-square-identifications-horizontal-refl :
    p ＝ q →
    coherence-square-identifications
      ( refl)
      ( p)
      ( q)
      ( refl)
  coherence-square-identifications-horizontal-refl α =
    right-unit ∙ α
```

Conversely, given a coherence square as above, we can obtain an equality
`p ＝ q`.

```agda
  inv-coherence-square-identifications-horizontal-refl :
    coherence-square-identifications
      ( refl)
      ( p)
      ( q)
      ( refl) →
    p ＝ q
  inv-coherence-square-identifications-horizontal-refl α =
    inv right-unit ∙ α
```

### Squares with `refl` on the left and right

Given an identification `α : p ＝ q`, we can obtain a coherence square with
`refl` on the left and right, like the diagram below.

```text
           q
       a -----> b
       |        |
  refl |        | refl
       ∨        ∨
       a -----> b
           p
```

```agda
  coherence-square-identifications-vertical-refl :
    p ＝ q →
    coherence-square-identifications
      ( q)
      ( refl)
      ( refl)
      ( p)
  coherence-square-identifications-vertical-refl α =
    α ∙ inv right-unit
```

Conversely, given a coherence square as above, we can obtain an equality
` p ＝ q`.

```agda
  inv-coherence-square-identifications-vertical-refl :
    coherence-square-identifications
      ( q)
      ( refl)
      ( refl)
      ( p) →
    p ＝ q
  inv-coherence-square-identifications-vertical-refl α =
    α ∙ right-unit
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
  horizontal-inv-coherence-square-identifications refl left right bottom coh =
    inv (right-transpose-eq-concat left bottom right coh)
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
  vertical-inv-coherence-square-identifications top refl right bottom coh =
    right-transpose-eq-concat top right (bottom) (inv coh)
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
  map-coherence-square-identifications refl refl _ _ coh = ap (ap f) coh
```

### Concatenating identifications of edges and coherences of commuting squares of identifications

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

**Note.** To avoid cyclic module dependencies we will give direct proofs that
concatenating identifications of edges of a square with the coherence of its
commutativity is an equivalence.

#### Concatenating identifications of the top edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
           top'
         ------->
       x -------> y
       |   top    |
  left |          | right
       ∨          ∨
       z -------> w.
          bottom
```

with an identification `top ＝ top'`. Then we get an equivalence

```text
           top                             top'
       x -------> y                    x -------> y
       |          |                    |          |
  left |          | right    ≃    left |          | right
       ∨          ∨                    ∨          ∨
       z -------> w                    z -------> w.
          bottom                          bottom
```

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  {top' : x ＝ y} (s : top ＝ top')
  where

  concat-top-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top' left right bottom
  concat-top-identification-coherence-square-identifications t =
    t ∙ ap (concat' _ right) s

  inv-concat-top-identification-coherence-square-identifications :
    coherence-square-identifications top' left right bottom →
    coherence-square-identifications top left right bottom
  inv-concat-top-identification-coherence-square-identifications t =
    t ∙ inv (ap (concat' _ right) s)

  is-section-inv-concat-top-identification-coherence-square-identifications :
    is-section
      concat-top-identification-coherence-square-identifications
      inv-concat-top-identification-coherence-square-identifications
  is-section-inv-concat-top-identification-coherence-square-identifications =
    is-section-inv-concat' (ap (concat' _ right) s)

  is-retraction-inv-concat-top-identification-coherence-square-identifications :
    is-retraction
      concat-top-identification-coherence-square-identifications
      inv-concat-top-identification-coherence-square-identifications
  is-retraction-inv-concat-top-identification-coherence-square-identifications =
    is-retraction-inv-concat' (ap (concat' _ right) s)
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).

#### Concatenating identifications of the left edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
              top
         x -------> y
        | |         |
  left' | | left    | right
        ∨ ∨         ∨
         z -------> w.
            bottom
```

with an identification `left ＝ left'`. Then we get an equivalence

```text
           top                              top
       x -------> y                     x -------> y
       |          |                     |          |
  left |          | right    ≃    left' |          | right
       ∨          ∨                     ∨          ∨
       z -------> w                     z -------> w.
          bottom                           bottom
```

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  {left' : x ＝ z} (s : left ＝ left')
  where

  concat-left-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left' right bottom
  concat-left-identification-coherence-square-identifications t =
    inv (ap (concat' _ bottom) s) ∙ t

  inv-concat-left-identification-coherence-square-identifications :
    coherence-square-identifications top left' right bottom →
    coherence-square-identifications top left right bottom
  inv-concat-left-identification-coherence-square-identifications t =
    ap (concat' _ bottom) s ∙ t

  is-section-inv-concat-left-identification-coherence-square-identifications :
    is-section
      concat-left-identification-coherence-square-identifications
      inv-concat-left-identification-coherence-square-identifications
  is-section-inv-concat-left-identification-coherence-square-identifications =
    is-retraction-inv-concat (ap (concat' _ bottom) s)

  is-retraction-inv-concat-left-identification-coherence-square-identifications :
    is-retraction
      concat-left-identification-coherence-square-identifications
      inv-concat-left-identification-coherence-square-identifications
  is-retraction-inv-concat-left-identification-coherence-square-identifications =
    is-section-inv-concat (ap (concat' _ bottom) s)
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).

#### Concatenating identifications of the right edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
            top
       x -------> y
       |         | |
  left |   right | | right'
       ∨         ∨ ∨
       z -------> w.
          bottom
```

with an identification `right ＝ right'`. Then we get an equivalence

```text
           top                             top
       x -------> y                    x -------> y
       |          |                    |          |
  left |          | right    ≃    left |          | right'
       ∨          ∨                    ∨          ∨
       z -------> w                    z -------> w.
          bottom                          bottom
```

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  {right' : y ＝ w} (s : right ＝ right')
  where

  concat-right-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right' bottom
  concat-right-identification-coherence-square-identifications t =
    t ∙ ap (concat top _) s

  inv-concat-right-identification-coherence-square-identifications :
    coherence-square-identifications top left right' bottom →
    coherence-square-identifications top left right bottom
  inv-concat-right-identification-coherence-square-identifications t =
    t ∙ inv (ap (concat top _) s)

  is-section-inv-concat-right-identification-coherence-square-identifications :
    is-section
      concat-right-identification-coherence-square-identifications
      inv-concat-right-identification-coherence-square-identifications
  is-section-inv-concat-right-identification-coherence-square-identifications =
    is-section-inv-concat' (ap (concat top _) s)

  is-retraction-inv-concat-right-identification-coherence-square-identifications :
    is-retraction
      concat-right-identification-coherence-square-identifications
      inv-concat-right-identification-coherence-square-identifications
  is-retraction-inv-concat-right-identification-coherence-square-identifications =
    is-retraction-inv-concat' (ap (concat top _) s)
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).

#### Concatenating identifications of the bottom edge with a coherence of a commuting square of identifications

Consider a commuting diagram of identifications

```text
            top
       x -------> y
       |          |
  left |          | right
       ∨  bottom  ∨
       z -------> w.
         ------->
          bottom'
```

with an identification `bottom ＝ bottom'`. Then we get an equivalence

```text
           top                             top
       x -------> y                    x -------> y
       |          |                    |          |
  left |          | right    ≃    left |          | right
       ∨          ∨                    ∨          ∨
       z -------> w                    z -------> w.
          bottom                          bottom'
```

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  {bottom' : z ＝ w} (s : bottom ＝ bottom')
  where

  concat-bottom-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left right bottom'
  concat-bottom-identification-coherence-square-identifications t =
    inv (ap (concat left _) s) ∙ t

  inv-concat-bottom-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom' →
    coherence-square-identifications top left right bottom
  inv-concat-bottom-identification-coherence-square-identifications t =
    ap (concat left _) s ∙ t

  is-section-inv-concat-bottom-identification-coherence-square-identifications :
    is-section
      concat-bottom-identification-coherence-square-identifications
      inv-concat-bottom-identification-coherence-square-identifications
  is-section-inv-concat-bottom-identification-coherence-square-identifications =
    is-retraction-inv-concat (ap (concat left _) s)

  is-retraction-inv-concat-bottom-identification-coherence-square-identifications :
    is-retraction
      concat-bottom-identification-coherence-square-identifications
      inv-concat-bottom-identification-coherence-square-identifications
  is-retraction-inv-concat-bottom-identification-coherence-square-identifications =
    is-section-inv-concat (ap (concat left _) s)
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).

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
`equiv-right-whisker-concat-coherence-square-identifications` as an example, it
provides us with two maps: the forward direction states
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
  {l : Level} {A : UU l} {x y z w u : A}
  where

  left-whisker-concat-coherence-square-identifications :
    (p : u ＝ x)
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom
  left-whisker-concat-coherence-square-identifications
    refl top left right bottom =
    id

  left-unwhisker-concat-coherence-square-identifications :
    (p : u ＝ x)
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom →
    coherence-square-identifications top left right bottom
  left-unwhisker-concat-coherence-square-identifications
    refl top left right bottom =
    id
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

  right-whisker-concat-coherence-square-identifications :
    coherence-square-identifications top left right bottom →
    {u : A} (p : w ＝ u) →
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p)
  right-whisker-concat-coherence-square-identifications s refl =
    concat-bottom-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right ∙ refl)
      ( bottom)
      ( inv right-unit)
      ( concat-right-identification-coherence-square-identifications
        ( top)
        ( left)
        ( right)
        ( bottom)
        ( inv right-unit)
        ( s))

  right-unwhisker-cohernece-square-identifications :
    {u : A} (p : w ＝ u) →
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p) →
    coherence-square-identifications top left right bottom
  right-unwhisker-cohernece-square-identifications refl =
    ( inv-concat-right-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)) ∘
    ( inv-concat-bottom-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right ∙ refl)
      ( bottom)
      ( inv right-unit))
```

### Double whiskering of commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z u v w : A}
  where

  double-whisker-coherence-square-identifications :
    (p : x ＝ y)
    (top : y ＝ u) (left : y ＝ z) (right : u ＝ v) (bottom : z ＝ v)
    (s : v ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications
      ( p ∙ top)
      ( p ∙ left)
      ( right ∙ s)
      ( bottom ∙ s)
  double-whisker-coherence-square-identifications
    p top left right bottom q H =
    left-whisker-concat-coherence-square-identifications p top left
      ( right ∙ q)
      ( bottom ∙ q)
    ( right-whisker-concat-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( H)
      ( q))
```

#### Left splicing coherences of commuting squares of identifications

For any inverse pair of identifications `p : y ＝ u` and `q : u ＝ y` equipped
with `α : inv p ＝ q` we obtain an equivalence

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

  left-splice-coherence-square-identifications :
    {u : A} (p : z ＝ u) (q : u ＝ z) (α : inv p ＝ q) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top (left ∙ p) right (q ∙ bottom)
  left-splice-coherence-square-identifications refl .refl refl =
    concat-left-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)

  left-unsplice-coherence-square-identifications :
    {u : A} (p : z ＝ u) (q : u ＝ z) (α : inv p ＝ q) →
    coherence-square-identifications top (left ∙ p) right (q ∙ bottom) →
    coherence-square-identifications top left right bottom
  left-unsplice-coherence-square-identifications refl .refl refl =
    inv-concat-left-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)
```

#### Right splicing coherences of commuting squares of identifications

For any inverse pair of identifications `p : y ＝ u` and `q : u ＝ y` equipped
with `α : inv p ＝ q` we obtain an equivalence

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

  right-splice-coherence-square-identifications :
    {u : A} (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (top ∙ p) left (inv p ∙ right) bottom
  right-splice-coherence-square-identifications refl .refl refl =
    concat-top-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)

  right-unsplice-coherence-square-identifications :
    {u : A} (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    coherence-square-identifications (top ∙ p) left (inv p ∙ right) bottom →
    coherence-square-identifications top left right bottom
  right-unsplice-coherence-square-identifications refl .refl refl =
    inv-concat-top-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)
```

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

with `s : left ∙ bottom-left ＝ top-left ∙ middle` and
`t : middle ∙ bottom-right ＝ top-right ∙ right`. Then the outer square
commutes.

```agda
module _
  {l : Level} {A : UU l} {a b c d e f : A}
  (top-left : a ＝ b) (top-right : b ＝ c)
  (left : a ＝ d) (middle : b ＝ e) (right : c ＝ f)
  (bottom-left : d ＝ e) (bottom-right : e ＝ f)
  where

  horizontal-pasting-coherence-square-identifications :
    coherence-square-identifications top-left left middle bottom-left →
    coherence-square-identifications top-right middle right bottom-right →
    coherence-square-identifications
      (top-left ∙ top-right) left right (bottom-left ∙ bottom-right)
  horizontal-pasting-coherence-square-identifications s t =
    ( right-whisker-concat-coherence-square-identifications
      ( top-left)
      ( left)
      ( middle)
      ( bottom-left)
      ( s)
      ( bottom-right)) ∙
    ( ( inv (assoc top-left middle bottom-right)) ∙
      ( left-whisker-concat-coherence-square-identifications
        ( top-left)
        ( top-right)
        ( middle)
        ( right)
        ( bottom-right)
        ( t)))
```

### Vertically pasting squares of identifications

Consider two squares of identifications as in the diagram

```text
                  top
              a --------> b
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              c --------> d
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              e --------> f
                 bottom
```

with `s : top-left ∙ middle ＝ top ∙ top-right` and
`t : bottom-left ∙ bottom ＝ middle ∙ bottom-right`. Then the outer square
commutes.

```agda
module _
  {l : Level} {A : UU l} {a b c d e f : A}
  (top : a ＝ b) (top-left : a ＝ c) (top-right : b ＝ d)
  (middle : c ＝ d) (bottom-left : c ＝ e) (bottom-right : d ＝ f)
  (bottom : e ＝ f)
  where

  vertical-pasting-coherence-square-identifications :
    coherence-square-identifications top top-left top-right middle →
    coherence-square-identifications middle bottom-left bottom-right bottom →
    coherence-square-identifications
      top (top-left ∙ bottom-left) (top-right ∙ bottom-right) bottom
  vertical-pasting-coherence-square-identifications s t =
    ( left-whisker-concat-coherence-square-identifications
      ( top-left)
      ( middle)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( t)) ∙
    ( ( assoc top-left middle bottom-right) ∙
      ( right-whisker-concat-coherence-square-identifications
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( s)
        ( bottom-right)))
```

## Properties

### Left unit law for horizontal pasting of commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  where

  left-unit-law-horizontal-pasting-coherence-square-identifications :
    (top : a ＝ b) (left : a ＝ c) (right : b ＝ d) (bottom : c ＝ d)
    (s : coherence-square-identifications top left right bottom) →
    horizontal-pasting-coherence-square-identifications
      ( refl)
      ( top)
      ( left)
      ( left)
      ( right)
      ( refl)
      ( bottom)
      ( horizontal-refl-coherence-square-identifications left)
      ( s) ＝
    s
  left-unit-law-horizontal-pasting-coherence-square-identifications
    refl refl right refl s = refl
```

### Right unit law for horizontal pasting of commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  where

  right-unit-law-horizontal-pasting-coherence-square-identifications :
    (top : a ＝ b) (left : a ＝ c) (right : b ＝ d) (bottom : c ＝ d)
    (s : coherence-square-identifications top left right bottom) →
    horizontal-pasting-coherence-square-identifications
      ( top)
      ( refl)
      ( left)
      ( right)
      ( right)
      ( bottom)
      ( refl)
      ( s)
      ( horizontal-refl-coherence-square-identifications right) ∙
    right-whisker-concat right-unit right ＝
    left-whisker-concat left right-unit ∙ s
  right-unit-law-horizontal-pasting-coherence-square-identifications
    refl refl .refl refl refl =
    refl
```

### Left unit law for vertical pasting of commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  where

  left-unit-law-vertical-pasting-coherence-square-identifications :
    (top : a ＝ b) (left : a ＝ c) (right : b ＝ d) (bottom : c ＝ d)
    (s : coherence-square-identifications top left right bottom) →
    vertical-pasting-coherence-square-identifications
      ( top)
      ( refl)
      ( refl)
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( vertical-refl-coherence-square-identifications top)
      ( s) ＝
    s
  left-unit-law-vertical-pasting-coherence-square-identifications
    refl refl .refl refl refl = refl
```

### Right unit law for vertical pasting of commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  where

  right-unit-law-vertical-pasting-coherence-square-identifications :
    (top : a ＝ b) (left : a ＝ c) (right : b ＝ d) (bottom : c ＝ d)
    (s : coherence-square-identifications top left right bottom) →
    vertical-pasting-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( refl)
      ( refl)
      ( bottom)
      ( s)
      ( vertical-refl-coherence-square-identifications bottom) ∙
    left-whisker-concat top right-unit ＝
    right-whisker-concat right-unit bottom ∙ s
  right-unit-law-vertical-pasting-coherence-square-identifications
    refl refl .(refl ∙ refl) refl refl =
    refl
```

### Computing the right whiskering of a vertically constant square with an identification

Consider the vertically constant square of identifications

```text
           p
       x -----> y
       |        |
  refl |        | refl
       ∨        ∨
       x -----> y
           p
```

at an identification `p : x ＝ y`, and consider an identification `q : y ＝ z`.
Then the right whiskering of the above square with `q` is the commuting square
of identifications

```text
            p
       x -------> y
       |          |
  refl |   refl   | q
       ∨          ∨
       x -------> z
          p ∙ q
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  right-whisker-concat-vertical-refl-coherence-square-identifications :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    right-whisker-concat-coherence-square-identifications p refl refl p
      ( vertical-refl-coherence-square-identifications p)
      ( q) ＝
    refl
  right-whisker-concat-vertical-refl-coherence-square-identifications
    refl refl =
    refl
```

### Computing the right whiskering of a horizontally constant square with an identification

Consider a horizontally constant commuting square of identifications

```text
       refl
    x -----> x
    |        |
  p |        | p
    ∨        ∨
    y -----> y
       refl
```

at an identification `p` and consider an identification `q : y ＝ z`. Then the
right whiskering of the above square with `q` is the square

```text
       refl
    x -----> x
    |        |
  p |  refl  | p ∙ q
    ∨        ∨
    y -----> z.
        q
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  right-whisker-concat-horizontal-refl-coherence-square-identifications :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    right-whisker-concat-coherence-square-identifications refl p p refl
      ( horizontal-refl-coherence-square-identifications p)
      ( q) ＝
    refl
  right-whisker-concat-horizontal-refl-coherence-square-identifications
    refl refl =
    refl
```

### Computing the left whiskering of a horizontally constant square with an identification

Consider an identification `p : x ＝ y` and a horizontally constant commuting
square of identifications

```text
       refl
    y -----> y
    |        |
  q |        | q
    ∨        ∨
    z -----> z
       refl
```

at an identification `q : y ＝ z`. The the left whiskering of the above square
with `p` is the commuting square

```text
                                  q ∙ refl
        x ------------------------------------------------------> y
        |                                                         |
  q ∙ p |  right-unit ∙ inv (right-whisker-concat right-unit p)   | p
        ∨                                                         ∨
        z ------------------------------------------------------> z.
                                   refl
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  left-whisker-concat-horizontal-refl-coherence-square-identifications :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    left-whisker-concat-coherence-square-identifications p refl q q refl
      ( horizontal-refl-coherence-square-identifications q) ∙
    right-whisker-concat right-unit q ＝
    right-unit
  left-whisker-concat-horizontal-refl-coherence-square-identifications
    refl refl =
    refl

  left-whisker-concat-horizontal-refl-coherence-square-identifications' :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    left-whisker-concat-coherence-square-identifications p refl q q refl
      ( horizontal-refl-coherence-square-identifications q) ＝
    right-unit ∙ inv (right-whisker-concat right-unit q)
  left-whisker-concat-horizontal-refl-coherence-square-identifications'
    refl refl =
    refl
```

### Computing the left whiskering of a vertically constant square with an identification

Consider the vertically constant square of identifications

```text
           q
       y -----> z
       |        |
  refl |        | refl
       ∨        ∨
       y -----> z
           q
```

at an identification `q : y ＝ z` and consider an identification `p : x ＝ y`.
Then the left whiskering of the above square with `p` is the square

```text
                                    p ∙ q
           x ---------------------------------------------------> z
           |                                                      |
  p ∙ refl |  right-whisker-concat right-unit q ∙ inv right-unit  | refl
           ∨                                                      ∨
           y ---------------------------------------------------> z.
                                      q
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  left-whisker-concat-vertical-refl-coherence-square-identifications :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    left-whisker-concat-coherence-square-identifications p q refl refl q
      ( vertical-refl-coherence-square-identifications q) ∙
    right-unit ＝
    right-whisker-concat right-unit q
  left-whisker-concat-vertical-refl-coherence-square-identifications
    refl refl =
    refl

  left-whisker-concat-vertical-refl-coherence-square-identifications' :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    left-whisker-concat-coherence-square-identifications p q refl refl q
      ( vertical-refl-coherence-square-identifications q) ＝
    right-whisker-concat right-unit q ∙ inv right-unit
  left-whisker-concat-vertical-refl-coherence-square-identifications'
    refl refl =
    refl
```

### Left whiskering horizontal concatenations of squares with identifications

Consider a commuting diagram of identifications of the form

```text
            top-left        top-right
       a -------------> c -------------> e
       |                |                |
  left |                | middle         | right
       ∨                ∨                ∨
       b -------------> d -------------> f
          bottom-left      bottom-right
```

and consider an identification `p : x ＝ a`. Then the left whiskering of `p` and
the horizontal concatenation of coherences of commuting squares is up to
associativity the horizontal concatenation of the squares

```text
              p ∙ top-left      top-right
           x -------------> c -------------> e
           |                |                |
  p ∙ left |                | middle         | right
           ∨                ∨                ∨
           b -------------> d -------------> f
              bottom-left      bottom-right
```

where the left square is the left whiskering of `p` and the original left
square.

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  left-whisker-concat-horizontal-pasting-coherence-square-identifications :
    {x a b c d e f : A} (p : x ＝ a)
    (top-left : a ＝ c) (top-right : c ＝ e)
    (left : a ＝ b) (middle : c ＝ d) (right : e ＝ f)
    (bottom-left : b ＝ d) (bottom-right : d ＝ f)
    (l : coherence-square-identifications top-left left middle bottom-left)
    (r : coherence-square-identifications top-right middle right bottom-right) →
    left-whisker-concat-coherence-square-identifications p
      ( top-left ∙ top-right)
      ( left)
      ( right)
      ( bottom-left ∙ bottom-right)
      ( horizontal-pasting-coherence-square-identifications
        ( top-left)
        ( top-right)
        ( left)
        ( middle)
        ( right)
        ( bottom-left)
        ( bottom-right)
        ( l)
        ( r)) ＝
    horizontal-pasting-coherence-square-identifications
      ( p ∙ top-left)
      ( top-right)
      ( p ∙ left)
      ( middle)
      ( right)
      ( bottom-left)
      ( bottom-right)
      ( left-whisker-concat-coherence-square-identifications p
        ( top-left)
        ( left)
        ( middle)
        ( bottom-left)
        ( l))
      ( r) ∙
    right-whisker-concat
      ( assoc p top-left top-right)
      ( right)
  left-whisker-concat-horizontal-pasting-coherence-square-identifications
    refl top-left top-right left middle right bottom-left bottom-right l r =
    inv right-unit
```

### Left whiskering vertical concatenations of squares with identifications

Consider two squares of identifications as in the diagram

```text
                  top
              a --------> b
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              c --------> d
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              e --------> f
                 bottom
```

and consider an identification `p : x ＝ a`. Then the left whiskering of `p`
with the vertical pasting of the two squares above is up to associativity the
vertical pasting of the squares

```text
                  p ∙ top
               x --------> b
               |           |
  p ∙ top-left |           | top-right
               ∨  middle   ∨
               c --------> d
               |           |
   bottom-left |           | bottom-right
               ∨           ∨
               e --------> f.
                  bottom
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  left-whisker-concat-vertical-concat-coherence-square-identifications :
    {x a b c d e f : A} (p : x ＝ a) →
    (top : a ＝ b) (top-left : a ＝ c) (top-right : b ＝ d) (middle : c ＝ d)
    (bottom-left : c ＝ e) (bottom-right : d ＝ f) (bottom : e ＝ f)
    (t : coherence-square-identifications top top-left top-right middle) →
    (b :
      coherence-square-identifications middle bottom-left bottom-right bottom) →
    right-whisker-concat (assoc p top-left bottom-left) bottom ∙
    left-whisker-concat-coherence-square-identifications p
      ( top)
      ( top-left ∙ bottom-left)
      ( top-right ∙ bottom-right)
      ( bottom)
      ( vertical-pasting-coherence-square-identifications
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( t)
        ( b)) ＝
    vertical-pasting-coherence-square-identifications
      ( p ∙ top)
      ( p ∙ top-left)
      ( top-right)
      ( middle)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( left-whisker-concat-coherence-square-identifications p
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( t))
      ( b)
  left-whisker-concat-vertical-concat-coherence-square-identifications
    refl top top-left top-right middle bottom-left bottom-right bottom t b =
    refl
```

### Right whiskering horizontal pastings of commuting squares of identifications

Consider a commuting diagram of identifications of the form

```text
            top-left        top-right
       a -------------> c -------------> e
       |                |                |
  left |                | middle         | right
       ∨                ∨                ∨
       b -------------> d -------------> f
          bottom-left      bottom-right
```

and consider an identification `q : f ＝ y`. Then the right whiskering of the
horizontal pasting of the squares above is up to associativity the horizontal
pasting of the squares

```text
            top-left           top-right
       a -------------> c ------------------> e
       |                |                     |
  left |                | middle              | right ∙ q
       ∨                ∨                     ∨
       b -------------> d ------------------> y
          bottom-left      bottom-right ∙ q
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  right-whisker-concat-horizontal-pasting-coherence-square-identifications :
    {a b c d e f y : A}
    (top-left : a ＝ c) (top-right : c ＝ e)
    (left : a ＝ b) (middle : c ＝ d) (right : e ＝ f)
    (bottom-left : b ＝ d) (bottom-right : d ＝ f)
    (l : coherence-square-identifications top-left left middle bottom-left) →
    (r : coherence-square-identifications top-right middle right bottom-right) →
    (q : f ＝ y) →
    right-whisker-concat-coherence-square-identifications
      ( top-left ∙ top-right)
      ( left)
      ( right)
      ( bottom-left ∙ bottom-right)
      ( horizontal-pasting-coherence-square-identifications
        ( top-left)
        ( top-right)
        ( left)
        ( middle)
        ( right)
        ( bottom-left)
        ( bottom-right)
        ( l)
        ( r))
      ( q) ＝
    left-whisker-concat left (assoc bottom-left bottom-right q) ∙
    horizontal-pasting-coherence-square-identifications
      ( top-left)
      ( top-right)
      ( left)
      ( middle)
      ( right ∙ q)
      ( bottom-left)
      ( bottom-right ∙ q)
      ( l)
      ( right-whisker-concat-coherence-square-identifications
        ( top-right)
        ( middle)
        ( right)
        ( bottom-right)
        ( r)
        ( q))
  right-whisker-concat-horizontal-pasting-coherence-square-identifications
    refl refl refl .refl .refl refl refl refl refl refl =
    refl
```

### Right whiskering vertical concatenations of squares with identifications

Consider two squares of identifications as in the diagram

```text
                  top
              a --------> b
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              c --------> d
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              e --------> f
                 bottom
```

and consider an identification `q : f ＝ y`. Then the right whiskering of the
vertical pasting of the two squares above with `q` is up to associativity the
vertical pasting of the squares

```text
                     top
              a ------------> b
              |               |
     top-left |               | top-right
              ∨    middle     ∨
              c ------------> d
              |               |
  bottom-left |               | bottom-right ∙ q
              ∨               ∨
              e ------------> y.
                 bottom ∙ q
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  right-whisker-concat-vertical-pasting-coherence-square-identifications :
    {a b c d e f y : A}
    (top : a ＝ b) (top-left : a ＝ c) (top-right : b ＝ d)
    (middle : c ＝ d)
    (bottom-left : c ＝ e) (bottom-right : d ＝ f) (bottom : e ＝ f)
    (t : coherence-square-identifications top top-left top-right middle) →
    (b :
      coherence-square-identifications middle bottom-left bottom-right bottom) →
    (q : f ＝ y) →
    right-whisker-concat-coherence-square-identifications
      ( top)
      ( top-left ∙ bottom-left)
      ( top-right ∙ bottom-right)
      ( bottom)
      ( vertical-pasting-coherence-square-identifications
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( t)
        ( b))
      ( q) ∙
    left-whisker-concat top (assoc top-right bottom-right q) ＝
    vertical-pasting-coherence-square-identifications
      ( top)
      ( top-left)
      ( top-right)
      ( middle)
      ( bottom-left)
      ( bottom-right ∙ q)
      ( bottom ∙ q)
      ( t)
      ( right-whisker-concat-coherence-square-identifications
        ( middle)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( b)
        ( q))
  right-whisker-concat-vertical-pasting-coherence-square-identifications
    refl refl .refl refl refl .refl refl refl refl refl =
    refl
```
