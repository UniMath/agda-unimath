# Commuting 3-simplices of homotopies

```agda
{-# OPTIONS --safe #-}

module foundation-core.commuting-3-simplices-of-homotopies where

open import foundation-core.commuting-triangles-of-homotopies
open import foundation-core.homotopies
open import foundation-core.universe-levels
```

## Idea

A commuting 3-simplex of homotopies is a commuting diagram of the form

```md
  f ----------> g
  |  \       ^  |
  |    \   /    |
  |      /      |
  |    /   \    |
  V  /       v  V
  h ----------> i.
```

where f, g, h, and i are functions.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  (diagonal-up : h ~ g) (diagonal-down : f ~ i)
  (upper-left : coherence-triangle-htpy top diagonal-up left)
  (lower-right : coherence-triangle-htpy bottom right diagonal-up)
  (upper-right : coherence-triangle-htpy diagonal-down right top)
  (lower-left : coherence-triangle-htpy diagonal-down bottom left)
  where

  coherence-3-simplex-htpy : UU (l1 ⊔ l2)
  coherence-3-simplex-htpy =
    ( upper-right ∙h
      left-whisk-htpy-coherence-triangle-htpy {right = diagonal-up} right upper-left) ~
    ( ( lower-left ∙h
        right-whisk-htpy-coherence-triangle-htpy {right = right} lower-right left) ∙h
      assoc-htpy left diagonal-up right)

  coherence-3-simplex-htpy' : UU (l1 ⊔ l2)
  coherence-3-simplex-htpy' =
    ( ( lower-left ∙h
        right-whisk-htpy-coherence-triangle-htpy {right = right} lower-right left) ∙h
      assoc-htpy left diagonal-up right) ~
    ( upper-right ∙h
      left-whisk-htpy-coherence-triangle-htpy {right = diagonal-up} right upper-left)
```
