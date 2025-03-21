# Commuting squares of identifications

```agda
module foundation.commuting-squares-of-identifications where

open import foundation-core.commuting-squares-of-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.equivalences
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

is said to be a
{{#concept "commuting square" Disambiguation="identifications" Agda=coherence-square-identifications}}
if there is an identification `left ∙ bottom ＝ top ∙ right`. Such an
identification is called a
{{#concept "coherence" Disambiguation="commuting square of identifications" Agda=coherence-square-identifications}}
of the square.

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

  abstract
    is-equiv-concat-top-identification-coherence-square-identifications :
      is-equiv
        ( concat-top-identification-coherence-square-identifications
            top left right bottom s)
    is-equiv-concat-top-identification-coherence-square-identifications =
      is-equiv-is-invertible
        ( inv-concat-top-identification-coherence-square-identifications
            top left right bottom s)
        ( is-section-inv-concat-top-identification-coherence-square-identifications
            top left right bottom s)
        ( is-retraction-inv-concat-top-identification-coherence-square-identifications
            top left right bottom s)

  equiv-concat-top-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top' left right bottom
  pr1 equiv-concat-top-identification-coherence-square-identifications =
    concat-top-identification-coherence-square-identifications
      top left right bottom s
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

  abstract
    is-equiv-concat-left-identification-coherence-square-identifications :
      is-equiv
        ( concat-left-identification-coherence-square-identifications
            top left right bottom s)
    is-equiv-concat-left-identification-coherence-square-identifications =
      is-equiv-is-invertible
        ( inv-concat-left-identification-coherence-square-identifications
            top left right bottom s)
        ( is-section-inv-concat-left-identification-coherence-square-identifications
            top left right bottom s)
        ( is-retraction-inv-concat-left-identification-coherence-square-identifications
            top left right bottom s)

  equiv-concat-left-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left' right bottom
  pr1 equiv-concat-left-identification-coherence-square-identifications =
    concat-left-identification-coherence-square-identifications
        top left right bottom s
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

  abstract
    is-equiv-concat-right-identification-coherence-square-identifications :
      is-equiv
        ( concat-right-identification-coherence-square-identifications
            top left right bottom s)
    is-equiv-concat-right-identification-coherence-square-identifications =
      is-equiv-is-invertible
        ( inv-concat-right-identification-coherence-square-identifications
            top left right bottom s)
        ( is-section-inv-concat-right-identification-coherence-square-identifications
            top left right bottom s)
        ( is-retraction-inv-concat-right-identification-coherence-square-identifications
            top left right bottom s)

  equiv-concat-right-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left right' bottom
  pr1 equiv-concat-right-identification-coherence-square-identifications =
    concat-right-identification-coherence-square-identifications
      top left right bottom s
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

  is-equiv-concat-bottom-identification-coherence-square-identifications :
    is-equiv
      ( concat-bottom-identification-coherence-square-identifications
          top left right bottom s)
  is-equiv-concat-bottom-identification-coherence-square-identifications =
    is-equiv-is-invertible
      ( inv-concat-bottom-identification-coherence-square-identifications
          top left right bottom s)
      ( is-section-inv-concat-bottom-identification-coherence-square-identifications
          top left right bottom s)
      ( is-retraction-inv-concat-bottom-identification-coherence-square-identifications
          top left right bottom s)

  equiv-concat-bottom-identification-coherence-square-identifications :
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left right bottom'
  pr1 equiv-concat-bottom-identification-coherence-square-identifications =
    concat-bottom-identification-coherence-square-identifications
        top left right bottom s
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

  equiv-left-whisker-concat-coherence-square-identifications :
    (p : u ＝ x)
    (top : x ＝ y) (left : x ＝ z) (right : y ＝ w) (bottom : z ＝ w) →
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications (p ∙ top) (p ∙ left) right bottom
  equiv-left-whisker-concat-coherence-square-identifications
    refl top left right bottom =
    id-equiv
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

  equiv-right-whisker-concat-coherence-square-identifications :
    {u : A} (p : w ＝ u) →
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications top left (right ∙ p) (bottom ∙ p)
  equiv-right-whisker-concat-coherence-square-identifications refl =
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
```

### Double whiskering of commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z u v w : A}
  where

  equiv-double-whisker-coherence-square-identifications :
    (p : x ＝ y)
    (top : y ＝ u) (left : y ＝ z) (right : u ＝ v) (bottom : z ＝ v)
    (s : v ＝ w) →
    coherence-square-identifications top left right bottom ≃
    coherence-square-identifications
      ( p ∙ top)
      ( p ∙ left)
      ( right ∙ s)
      ( bottom ∙ s)
  equiv-double-whisker-coherence-square-identifications
    p top left right bottom q =
    equiv-left-whisker-concat-coherence-square-identifications p top left
      ( right ∙ q)
      ( bottom ∙ q) ∘e
    equiv-right-whisker-concat-coherence-square-identifications
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( q)
```

### Computing the pasting of squares with `refl` on opposite sides

Consider two squares of identifications as in the diagram

```text
                  refl
              a --------> a
              |           |
     top-left |           | top-right
              ∨   refl    ∨
              b --------> b
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              c --------> c
                  refl
```

Then the pasted square can be computed in terms of the horizontal concatenation
of the filler squares

```agda
module _
  {l : Level} {A : UU l} {a b c : A}
  where

  vertical-pasting-coherence-square-identifications-horizontal-refl :
    (top-left : a ＝ b) (top-right : a ＝ b)
    (bottom-left : b ＝ c) (bottom-right : b ＝ c)
    (α : top-left ＝ top-right) (β : bottom-left ＝ bottom-right) →
    ( inv-coherence-square-identifications-horizontal-refl
      ( top-left ∙ bottom-left)
      ( top-right ∙ bottom-right)
      ( vertical-pasting-coherence-square-identifications
        ( refl)
        ( top-left)
        ( top-right)
        ( refl)
        ( bottom-left)
        ( bottom-right)
        ( refl)
        ( coherence-square-identifications-horizontal-refl
          ( top-left)
          ( top-right)
          ( α))
        ( coherence-square-identifications-horizontal-refl
          ( bottom-left)
          ( bottom-right)
          ( β)))) ＝
      ( horizontal-concat-Id² α β)
  vertical-pasting-coherence-square-identifications-horizontal-refl
    refl refl refl refl refl refl =
      refl

  vertical-pasting-inv-coherence-square-identifications-horizontal-refl :
    (top-left : a ＝ b) (top-right : a ＝ b)
    (bottom-left : b ＝ c) (bottom-right : b ＝ c)
    (α : coherence-square-identifications refl top-left top-right refl)
    (β : coherence-square-identifications refl bottom-left bottom-right refl) →
    ( inv-coherence-square-identifications-horizontal-refl
      ( top-left ∙ bottom-left)
      ( top-right ∙ bottom-right)
      ( vertical-pasting-coherence-square-identifications
        ( refl)
        ( top-left)
        ( top-right)
        ( refl)
        ( bottom-left)
        ( bottom-right)
        ( refl)
        ( α)
        ( β))) ＝
      ( horizontal-concat-Id²
        ( inv-coherence-square-identifications-horizontal-refl
          ( top-left)
          ( top-right)
          ( α))
        ( inv-coherence-square-identifications-horizontal-refl
          ( bottom-left)
          ( bottom-right)
          ( β)))
  vertical-pasting-inv-coherence-square-identifications-horizontal-refl
    refl refl refl refl refl refl =
      refl
```
