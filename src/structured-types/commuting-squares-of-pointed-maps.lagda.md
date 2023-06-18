# Commuting squares of pointed maps

```agda
module structured-types.commuting-squares-of-pointed-maps where
```

<details><summary>Imports</summary>

```agda
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
coherence-square-pointed-maps :
  {l1 l2 l3 l4 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : Pointed-Type l3} {X : Pointed-Type l4}
  (top : C →∗ B) (left : C →∗ A) (right : B →∗ X) (bottom : A →∗ X) →
  UU (l3 ⊔ l4)
coherence-square-pointed-maps top left right bottom =
  (bottom ∘∗ left) ~∗ (right ∘∗ top)
```
