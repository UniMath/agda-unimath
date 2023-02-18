# Commuting triangles

```agda
{-# OPTIONS --safe #-}

module foundation-core.commuting-triangles where

open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.universe-levels
```

## Idea

A triangle of maps

```md
 A ----> B
  \     /
   \   /
    V V
     X
```

is said to commute if there is a homotopy between the map on the left and the composite map.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  coherence-triangle :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle left right top = left ~ (right ∘ top)

  coherence-triangle' :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle' left right top = (right ∘ top) ~ left
```
