# Commuting squares of pointed maps

```agda
module structured-types.commuting-squares-of-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies
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

Such a square is said to be a {{#concept "commuting square of pointed maps" Agda=coherence-square-pointed-maps}} if there is a [pointed homotopy](structured-types.pointed-homotopies.md)

```text
  bottom ∘∗ left ~∗ right ∘∗ top.
```

Such a homotopy is referred to as the {{#concept "coherence" Disambiguation="commuting squares of pointed maps" Agda=coherence-square-pointed-maps}} of the commuting square of pointed maps.

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
    htpy-pointed-htpy (bottom ∘∗ left) (right ∘∗ top)
```

## Properties

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
  K : bottom-right ∘∗ middle ~∗ right ∘∗ top-right
```

The {{#concept "horizontal pasting" Disambiguation="commuting squares of pointed maps" Agda=horizontal-pasting-coherence-square-pointed-maps}} of these coherences of commuting squares of pointed maps is the coherence of the commuting square

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

The first and third homotopy in this concatenation are the whiskerings of coherences of [commuting triangles of pointed homotopies](structured-types.commuting-triangles-of-pointed-homotopies.md).

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
      ( associative-comp-pointed-map bottom-right bottom-left left)
      ( concat-pointed-htpy
        {! left-whisker-pointed-htpy!}
        {!!})
```
