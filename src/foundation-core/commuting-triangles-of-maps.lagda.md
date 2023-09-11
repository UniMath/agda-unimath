# Commuting triangles of maps

```agda
module foundation-core.commuting-triangles-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A triangle of maps

```text
 A ----> B
  \     /
   \   /
    V V
     X
```

is said to commute if there is a homotopy between the map on the left and the
composite map.

## Definition

### Commuting triangles of maps

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  coherence-triangle-maps :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps left right top = left ~ (right ∘ top)

  coherence-triangle-maps' :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps' left right top = (right ∘ top) ~ left
```

### Concatenation of commuting triangles of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) (i : A → B) (j : B → C)
  where

  concat-coherence-triangle-maps :
    coherence-triangle-maps f g i →
    coherence-triangle-maps g h j →
    coherence-triangle-maps f h (j ∘ i)
  concat-coherence-triangle-maps H K =
    H ∙h (K ·r i)
```
