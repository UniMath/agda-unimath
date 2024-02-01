# Commuting squares of identifications

```agda
module foundation-core.commuting-squares-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
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

  abstract
    is-equiv-concat-top-identification-coherence-square-identifications :
      is-equiv concat-top-identification-coherence-square-identifications
    is-equiv-concat-top-identification-coherence-square-identifications =
      is-equiv-is-invertible
        inv-concat-top-identification-coherence-square-identifications
        is-section-inv-concat-top-identification-coherence-square-identifications
        is-retraction-inv-concat-top-identification-coherence-square-identifications

  equiv-concat-top-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top' left right bottom
  pr1 equiv-concat-top-identification-coherence-square-identifications =
    concat-top-identification-coherence-square-identifications
  pr2 equiv-concat-top-identification-coherence-square-identifications =
    is-equiv-concat-top-identification-coherence-square-identifications
```

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

  is-equiv-concat-left-identification-coherence-square-identifications :
    is-equiv concat-left-identification-coherence-square-identifications
  is-equiv-concat-left-identification-coherence-square-identifications =
    is-equiv-is-invertible
      inv-concat-left-identification-coherence-square-identifications
      is-section-inv-concat-left-identification-coherence-square-identifications
      is-retraction-inv-concat-left-identification-coherence-square-identifications

  equiv-concat-left-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left' right bottom
  pr1 equiv-concat-left-identification-coherence-square-identifications =
    concat-left-identification-coherence-square-identifications
  pr2 equiv-concat-left-identification-coherence-square-identifications =
    is-equiv-concat-left-identification-coherence-square-identifications
```

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

  abstract
    is-equiv-concat-right-identification-coherence-square-identifications :
      is-equiv concat-right-identification-coherence-square-identifications
    is-equiv-concat-right-identification-coherence-square-identifications =
      is-equiv-is-invertible
        inv-concat-right-identification-coherence-square-identifications
        is-section-inv-concat-right-identification-coherence-square-identifications
        is-retraction-inv-concat-right-identification-coherence-square-identifications

  equiv-concat-right-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left right' bottom
  pr1 equiv-concat-right-identification-coherence-square-identifications =
    concat-right-identification-coherence-square-identifications
  pr2 equiv-concat-right-identification-coherence-square-identifications =
    is-equiv-concat-right-identification-coherence-square-identifications
```

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

  is-equiv-concat-bottom-identification-coherence-square-identifications :
    is-equiv concat-bottom-identification-coherence-square-identifications
  is-equiv-concat-bottom-identification-coherence-square-identifications =
    is-equiv-is-invertible
      inv-concat-bottom-identification-coherence-square-identifications
      is-section-inv-concat-bottom-identification-coherence-square-identifications
      is-retraction-inv-concat-bottom-identification-coherence-square-identifications

  equiv-concat-bottom-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left right bottom'
  pr1 equiv-concat-bottom-identification-coherence-square-identifications =
    concat-bottom-identification-coherence-square-identifications
  pr2 equiv-concat-bottom-identification-coherence-square-identifications =
    is-equiv-concat-bottom-identification-coherence-square-identifications
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
  {l : Level} {A : UU l} {x y z w u : A}
  (p : u ＝ x)
  (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w)
  where

  equiv-left-whisker-coherence-square-identifications :
    (p : u ＝ x)
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom
  equiv-left-whisker-coherence-square-identifications refl
    top left right bottom = id-equiv

  left-whisker-coherence-square-identifications :
    (p : u ＝ x)
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom
  left-whisker-coherence-square-identifications refl top left right bottom =
    id

  left-unwhisker-coherence-square-identifications :
    (p : u ＝ x)
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom →
    coherence-square-identifications top left right bottom
  left-unwhisker-coherence-square-identifications refl top left right bottom =
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

  equiv-right-whisker-coherence-square-identifications :
    {u : A} (p : w ＝ u) →
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p)
  equiv-right-whisker-coherence-square-identifications refl =
    ( equiv-concat-bottom-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right ∙ refl)
      ( bottom)
      ( inv right-unit)) ∘e
    ( equiv-concat-right-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit))

  right-whisker-coherence-square-identifications :
    {u : A} (p : w ＝ u) →
    coherence-square-identifications top left right bottom →
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p)
  right-whisker-coherence-square-identifications refl =
    ( concat-bottom-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right ∙ refl)
      ( bottom)
      ( inv right-unit)) ∘
    ( concat-right-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit))

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

  equiv-left-splice-coherence-square-identifications :
    {u : A} (p : z ＝ u) (q : u ＝ z) (α : inv p ＝ q) →
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top (left ∙ p) right (q ∙ bottom)
  equiv-left-splice-coherence-square-identifications refl .refl refl =
    equiv-concat-left-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)

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

  equiv-right-splice-coherence-square-identifications :
    {u : A} (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications (top ∙ p) left (inv p ∙ right) bottom
  equiv-right-splice-coherence-square-identifications refl .refl refl =
    equiv-concat-top-identification-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( inv right-unit)

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
