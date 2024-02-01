# Commuting squares of identifications

```agda
module foundation.commuting-squares-of-identifications where

open import foundation-core.commuting-squares-of-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

In this file we develop some further properties of
[commuting squares of identifications](foundation-core.commuting-squares-of-identifications.md).

## Operations

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

with `s : left ∙ bottom-left ＝ top-left ∙ middle` and t : middle ∙ bottom-right
＝ top-right ∙ right`. Then the outer square commutes.

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
    ( right-whisker-coherence-square-identifications
      ( top-left)
      ( left)
      ( middle)
      ( bottom-left)
      ( bottom-right)
      ( s)) ∙
    ( ( inv (assoc top-left middle bottom-right)) ∙
      ( left-whisker-coherence-square-identifications
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
  vertical-pasting-coherence-square-identifications p q =
    ( left-whisker-coherence-square-identifications
      ( top-left)
      ( middle)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( q)) ∙
    ( ( assoc top-left middle bottom-right) ∙
      ( right-whisker-coherence-square-identifications
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( bottom-right)
        ( p)))
```

## Properties

### Unit law for horizontal pasting of identifications

in a type `A`.

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

### Whiskering of squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : x ＝ y) (p' : x ＝ z) {q : y ＝ u} {q' : z ＝ u} (r : u ＝ v)
  where

  equiv-right-whisker-square-identification :
    ( coherence-square-identifications p p' q q') ≃
    ( coherence-square-identifications p p' (q ∙ r) (q' ∙ r))
  equiv-right-whisker-square-identification =
    ( equiv-concat-assoc' (p' ∙ (q' ∙ r)) p q r) ∘e
    ( equiv-concat-assoc p' q' r (p ∙ q ∙ r)) ∘e
    ( equiv-right-whisker-identification r)

  right-whisker-square-identification :
    coherence-square-identifications p p' q q' →
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r)
  right-whisker-square-identification =
    map-equiv equiv-right-whisker-square-identification

  right-unwhisker-square-identifications :
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r) →
    coherence-square-identifications p p' q q'
  right-unwhisker-square-identifications =
    map-inv-equiv equiv-right-whisker-square-identification

module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : v ＝ x) {q : x ＝ y} {q' : x ＝ z} {r : y ＝ u} {r' : z ＝ u}
  where

  equiv-left-whisker-square-identification :
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') r r')
  equiv-left-whisker-square-identification =
    ( inv-equiv (equiv-concat-assoc p q' r' (p ∙ q ∙ r))) ∘e
    ( inv-equiv (equiv-concat-assoc' (p ∙ (q' ∙ r')) p q r)) ∘e
    ( equiv-left-whisker-identification p)

  left-whisker-square-identification :
    coherence-square-identifications q q' r r' →
    coherence-square-identifications (p ∙ q) (p ∙ q') r r'
  left-whisker-square-identification =
    map-equiv equiv-left-whisker-square-identification

  left-unwhisker-square-identification :
    coherence-square-identifications (p ∙ q) (p ∙ q') r r' →
    coherence-square-identifications q q' r r'
  left-unwhisker-square-identification =
    map-inv-equiv equiv-left-whisker-square-identification

module _
  {l : Level} {A : UU l} {x y z u v w : A}
  where

  equiv-both-whisker-square-identifications :
    (p : x ＝ y) {q : y ＝ z} {q' : y ＝ u} {r : z ＝ v} {r' : u ＝ v} →
    (s : v ＝ w) →
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') (r ∙ s) (r' ∙ s))
  equiv-both-whisker-square-identifications p {q} {q'} s =
    ( equiv-left-whisker-square-identification p) ∘e
    ( equiv-right-whisker-square-identification q q' s)
```
