# Commuting 3-simplices of maps

```agda
{-# OPTIONS --safe #-}
```

<details><summary>Imports</summary>
```agda
module foundation-core.commuting-3-simplices-of-maps where
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
open import foundation-core.universe-levels
```
</details>

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
  (upper-left : coherence-triangle-maps top diagonal-up left)
  (lower-right : coherence-triangle-maps bottom right diagonal-up)
  (upper-right : coherence-triangle-maps diagonal-down right top)
  (lower-left : coherence-triangle-maps diagonal-down bottom left)
  where

  coherence-3-simplex-maps : UU (l1 ⊔ l4)
  coherence-3-simplex-maps =
    ( upper-right ∙h (right ·l upper-left)) ~
    ( lower-left ∙h (lower-right ·r left))

  coherence-3-simplex-maps' : UU (l1 ⊔ l4)
  coherence-3-simplex-maps' =
    ( lower-left ∙h (lower-right ·r left)) ~
    ( upper-right ∙h (right ·l upper-left))
```
