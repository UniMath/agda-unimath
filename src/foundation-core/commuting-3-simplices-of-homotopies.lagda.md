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
  (upper-left : htpy-coherence-triangle top diagonal-up left)
  (lower-right : htpy-coherence-triangle bottom right diagonal-up)
  (upper-right : htpy-coherence-triangle diagonal-down right top)
  (lower-left : htpy-coherence-triangle diagonal-down bottom left)
  where

  htpy-coherence-3-simplex : UU (l1 ⊔ l2)
  htpy-coherence-3-simplex =
    ( upper-right ∙h
      left-whisk-htpy-htpy-coherence-triangle {right = diagonal-up} right upper-left) ~
    ( ( lower-left ∙h
        right-whisk-htpy-htpy-coherence-triangle {right = right} lower-right left) ∙h
      assoc-htpy left diagonal-up right)

  htpy-coherence-3-simplex' : UU (l1 ⊔ l2)
  htpy-coherence-3-simplex' =
    ( ( lower-left ∙h
        right-whisk-htpy-htpy-coherence-triangle {right = right} lower-right left) ∙h
      assoc-htpy left diagonal-up right) ~
    ( upper-right ∙h
      left-whisk-htpy-htpy-coherence-triangle {right = diagonal-up} right upper-left)
```
