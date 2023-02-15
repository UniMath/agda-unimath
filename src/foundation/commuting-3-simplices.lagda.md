---
title: Commuting 3-simplices
---

```agda
module foundation.commuting-3-simplices where

open import foundation-core.cones-pullbacks
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.universe-levels

open import foundation.commuting-triangles
open import foundation.homotopies
```

## Idea

A commuting 3-simplex is a commuting diagram of the form

```md
  A ----------> B
  |  \       ^  |
  |    \   /    |
  |      /      |
  |    /   \    |
  V  /       v  V
  X ----------> Y.
```

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A → X) (right : B → Y) (bottom : X → Y)
  (diagonal-up : X → B) (diagonal-down : A → Y)
  (upper-left : coherence-triangle top diagonal-up left)
  (lower-right : coherence-triangle bottom right diagonal-up)
  (upper-right : coherence-triangle diagonal-down right top)
  (lower-left : coherence-triangle diagonal-down bottom left)
  where

  coherence-3-simplex : UU (l1 ⊔ l4)
  coherence-3-simplex =
    ( upper-right ∙h (right ·l upper-left)) ~
    ( lower-left ∙h (lower-right ·r left))

  coherence-3-simplex' : UU (l1 ⊔ l4)
  coherence-3-simplex' =
    ( lower-left ∙h (lower-right ·r left)) ~
    ( upper-right ∙h (right ·l upper-left))
```
