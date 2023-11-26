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

## Definition

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
