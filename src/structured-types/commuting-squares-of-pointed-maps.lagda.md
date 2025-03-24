# Commuting squares of pointed maps

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.commuting-squares-of-pointed-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications funext
open import foundation.commuting-squares-of-maps funext univalence
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import structured-types.pointed-homotopies funext univalence truncations
open import structured-types.pointed-maps funext univalence truncations
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies-composition funext univalence truncations
```

</details>

## Idea

Consider a square of [pointed maps](structured-types.pointed-maps.md)

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y.
          bottom
```

Such a square is said to be a
{{#concept "commuting square" Disambiguation="pointed maps" Agda=coherence-square-pointed-maps}}
of pointed maps if there is a
[pointed homotopy](structured-types.pointed-homotopies.md)

```text
  bottom ∘∗ left ~∗ right ∘∗ top.
```

Such a homotopy is referred to as the
{{#concept "coherence" Disambiguation="commuting squares of pointed maps" Agda=coherence-square-pointed-maps}}
of the commuting square of pointed maps.

## Definitions

### Coherences of commuting squares of pointed maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : Pointed-Type l3} {X : Pointed-Type l4}
  (top : C →∗ B) (left : C →∗ A) (right : B →∗ X) (bottom : A →∗ X)
  where

  coherence-square-pointed-maps : UU (l3 ⊔ l4)
  coherence-square-pointed-maps =
    bottom ∘∗ left ~∗ right ∘∗ top

  coherence-square-maps-coherence-square-pointed-maps :
    coherence-square-pointed-maps →
    coherence-square-maps
      ( map-pointed-map top)
      ( map-pointed-map left)
      ( map-pointed-map right)
      ( map-pointed-map bottom)
  coherence-square-maps-coherence-square-pointed-maps =
    htpy-pointed-htpy
```

## Operations

### Left whiskering of coherences of commuting squares of pointed maps

Consider a commuting square of pointed maps

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y
          bottom
```

and consider a pointed map `f : Y →∗ Z`. Then the square

```text
              top
       A -------------> X
       |                |
  left |                | f ∘∗ right
       ∨                ∨
       B -------------> Z
          f ∘∗ bottom
```

also commutes.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4} {Z : Pointed-Type l5}
  (f : Y →∗ Z)
  (top : A →∗ X) (left : A →∗ B) (right : X →∗ Y) (bottom : B →∗ Y)
  (s : coherence-square-pointed-maps top left right bottom)
  where

  left-whisker-comp-coherence-square-pointed-maps :
    coherence-square-pointed-maps top left (f ∘∗ right) (f ∘∗ bottom)
  left-whisker-comp-coherence-square-pointed-maps =
    concat-pointed-htpy
      ( associative-comp-pointed-map f bottom left)
      ( concat-pointed-htpy
        ( left-whisker-comp-pointed-htpy f _ _ s)
        ( inv-associative-comp-pointed-map f right top))
```

### Left whiskering of coherences of commuting squares of pointed maps

Consider a commuting square of pointed maps

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y
          bottom
```

and consider a pointed map `f : Z →∗ A`. Then the square

```text
               f ∘∗ top
            A ----------> X
            |             |
  left ∘∗ f |             | right
            ∨             ∨
            B ----------> Z
                bottom
```

also commutes.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4} {Z : Pointed-Type l5}
  (top : A →∗ X) (left : A →∗ B) (right : X →∗ Y) (bottom : B →∗ Y)
  (s : coherence-square-pointed-maps top left right bottom)
  (f : Z →∗ A)
  where

  right-whisker-comp-coherence-square-pointed-maps :
    coherence-square-pointed-maps (top ∘∗ f) (left ∘∗ f) right bottom
  right-whisker-comp-coherence-square-pointed-maps =
    concat-pointed-htpy
      ( inv-associative-comp-pointed-map bottom left f)
      ( concat-pointed-htpy
        ( right-whisker-comp-pointed-htpy _ _ s f)
        ( associative-comp-pointed-map right top f))
```

### Horizontal pasting of coherences of commuting squares of pointed maps

Consider two commuting squares of pointed maps, as in the diagram

```text
            top-left         top-right
       A -------------> B --------------> C
       |                |                 |
  left |                | middle          | right
       ∨                ∨                 ∨
       D -------------> E --------------> F
          bottom-left      bottom-right
```

with pointed homotopies

```text
  H : bottom-left ∘∗ left ~∗ middle ∘∗ top
  K : bottom-right ∘∗ middle ~∗ right ∘∗ top-right.
```

The
{{#concept "horizontal pasting" Disambiguation="commuting squares of pointed maps" Agda=horizontal-pasting-coherence-square-pointed-maps}}
of these coherences of commuting squares of pointed maps is the coherence of the
commuting square

```text
             top-right ∘∗ top-left
       A -----------------------------> C
       |                                |
  left |                                | right
       ∨                                ∨
       D -----------------------------> F
          bottom-right ∘∗ bottom-left
```

obtained by concatenation of the following three pointed homotopies:

```text
  (bottom-right ∘∗ bottom-left) ∘∗ left
  ~∗ (bottom-right ∘∗ middle) ∘∗ top-left
  ~∗ bottom-right ∘∗ (middle ∘∗ top-left)
  ~∗ right ∘∗ (top-right ∘∗ top-left).
```

The first and third homotopy in this concatenation are the whiskerings of
coherences of
[commuting triangles of pointed maps](structured-types.commuting-triangles-of-pointed-maps.md).

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  {U : Pointed-Type l5} {V : Pointed-Type l6}
  (top-left : A →∗ X) (top-right : X →∗ U)
  (left : A →∗ B) (middle : X →∗ Y) (right : U →∗ V)
  (bottom-left : B →∗ Y) (bottom-right : Y →∗ V)
  (left-square :
    coherence-square-pointed-maps top-left left middle bottom-left)
  (right-square :
    coherence-square-pointed-maps top-right middle right bottom-right)
  where

  horizontal-pasting-coherence-square-pointed-maps :
    coherence-square-pointed-maps
      ( top-right ∘∗ top-left)
      ( left)
      ( right)
      ( bottom-right ∘∗ bottom-left)
  horizontal-pasting-coherence-square-pointed-maps =
    concat-pointed-htpy
      ( left-whisker-comp-coherence-square-pointed-maps
        ( bottom-right)
        ( top-left)
        ( left)
        ( middle)
        ( bottom-left)
        ( left-square))
      ( concat-pointed-htpy
        ( associative-comp-pointed-map bottom-right middle top-left)
        ( right-whisker-comp-coherence-square-pointed-maps
          ( top-right)
          ( middle)
          ( right)
          ( bottom-right)
          ( right-square)
          ( top-left)))
```

### Vertical pasting of coherences of commuting squares of pointed maps

Consider two commuting squares of pointed maps, as in the diagram

```text
                   top
              A --------> B
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              C --------> D
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              E --------> F
                 bottom
```

with pointed homotopies

```text
  H : middle ∘∗ top-left ~∗ top-right ∘∗ top
  K : bottom ∘∗ bottom-left ~∗  bottom-right ∘∗ middle.
```

The
{{#concept "vertical pasting" Disambiguation="commuting squares of pointed maps" Agda=vertical-pasting-coherence-square-pointed-maps}}
of these coherences of commuting squares of pointed maps is the coherence of the
commuting square

```text
                               top
                          A --------> B
                          |           |
  bottom-left ∘∗ top-left |           | bottom-right ∘∗ top-right
                          ∨           ∨
                          E --------> F
                             bottom
```

obtained by concatenation of the following three pointed homotopies:

```text
  bottom ∘∗ (bottom-left ∘∗ top-left)
  ~∗ bottom-right ∘∗ (middle ∘∗ top-left)
  ~∗ (bottom-right ∘∗ middle) ∘∗ top-left
  ~∗ (bottom-right ∘∗ top-right) ∘∗ top.
```

The first and third homotopy in this concatenation are the whiskerings of
coherences of
[commuting triangles of pointed maps](structured-types.commuting-triangles-of-pointed-maps.md).

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : Pointed-Type l3} {D : Pointed-Type l4}
  {E : Pointed-Type l5} {F : Pointed-Type l6}
  (top : A →∗ B) (top-left : A →∗ C) (top-right : B →∗ D) (middle : C →∗ D)
  (bottom-left : C →∗ E) (bottom-right : D →∗ F) (bottom : E →∗ F)
  (top-square : coherence-square-pointed-maps top top-left top-right middle)
  (bottom-square :
    coherence-square-pointed-maps middle bottom-left bottom-right bottom)
  where

  vertical-pasting-coherence-square-pointed-maps :
    coherence-square-pointed-maps
      ( top)
      ( bottom-left ∘∗ top-left)
      ( bottom-right ∘∗ top-right)
      ( bottom)
  vertical-pasting-coherence-square-pointed-maps =
    concat-pointed-htpy
      ( right-whisker-comp-coherence-square-pointed-maps
        ( middle)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( bottom-square)
        ( top-left))
      ( concat-pointed-htpy
        ( inv-associative-comp-pointed-map bottom-right middle top-left)
        ( left-whisker-comp-coherence-square-pointed-maps
          ( bottom-right)
          ( top)
          ( top-left)
          ( top-right)
          ( middle)
          ( top-square)))
```
