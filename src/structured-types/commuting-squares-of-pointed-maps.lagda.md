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

A coherence square of pointed maps

```text
  A ------> X
  |         |
  |         |
  |         |
  V         V
  B ------> Y
```

is a coherence of the underlying square of (unpointed) maps, plus a coherence
between the pointedness preservation proofs.

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
      ( (bottom-right ∘∗ bottom-left) ∘∗ left)
      ( bottom-right ∘∗ (bottom-left ∘∗ left))
      ( right ∘∗ (top-right ∘∗ top-left))
      ( associative-comp-pointed-map bottom-right bottom-left left)
      ( concat-pointed-htpy
        ( bottom-right ∘∗ (bottom-left ∘∗ left))
        ( bottom-right ∘∗ (middle ∘∗ top-left))
        ( right ∘∗ (top-right ∘∗ top-left))
        {! left-whisker-pointed-htpy!}
        {!!})
```
